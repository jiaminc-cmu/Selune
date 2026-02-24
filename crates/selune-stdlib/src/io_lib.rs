//! Lua 5.4 io library.

use selune_core::gc::{GcHeap, GcIdx, NativeContext, NativeError, Userdata};
use selune_core::string::StringInterner;
use selune_core::table::Table;
use selune_core::value::TValue;
use std::cell::RefCell;
use std::io::{self, BufReader, Read, Seek, SeekFrom, Write};

// ---------------------------------------------------------------------------
// Thread-local default file handles
// ---------------------------------------------------------------------------

thread_local! {
    static DEFAULT_INPUT: RefCell<Option<GcIdx<Userdata>>> = const { RefCell::new(None) };
    static DEFAULT_OUTPUT: RefCell<Option<GcIdx<Userdata>>> = const { RefCell::new(None) };
    /// Shared metatable for all file handles.
    static FILE_METATABLE: RefCell<Option<GcIdx<Table>>> = const { RefCell::new(None) };
}

/// Return the GC-relevant roots held by the io library (default input, default output, file metatable).
/// Called by the VM's GC mark phase so these thread-local handles are not prematurely collected.
#[allow(clippy::type_complexity)]
pub fn gc_roots() -> (
    Option<GcIdx<Userdata>>,
    Option<GcIdx<Userdata>>,
    Option<GcIdx<Table>>,
) {
    let input = DEFAULT_INPUT.with(|cell| *cell.borrow());
    let output = DEFAULT_OUTPUT.with(|cell| *cell.borrow());
    let mt = FILE_METATABLE.with(|cell| *cell.borrow());
    (input, output, mt)
}

/// Return GC roots for active lines iterator states (both the state userdata and the file it references).
/// NOTE: With the upvalue-based approach, lines iterator state is rooted through the native function's
/// upvalue field, which is traced by the GC automatically. This function now returns an empty vec.
pub fn gc_lines_roots(_gc: &selune_core::gc::GcHeap) -> Vec<GcIdx<Userdata>> {
    Vec::new()
}

// ---------------------------------------------------------------------------
// LuaFile: the data stored inside userdata
// ---------------------------------------------------------------------------

/// Internal file representation for the io library.
pub struct LuaFile {
    pub inner: LuaFileInner,
    pub name: String,
    pub is_closed: bool,
    /// Pushback byte for ungetc-like behavior (used by read_number).
    pub ungetc: Option<u8>,
    /// If true, flush after every write that contains '\n' (line buffering).
    pub line_buffered: bool,
}

/// Variants for the backing file stream.
pub enum LuaFileInner {
    Stdin(BufReader<io::Stdin>),
    Stdout,
    Stderr,
    File(std::fs::File),
    /// Buffered file — created by f:setvbuf("full"|"line", size).
    /// Inner writes go through BufWriter; reads flush first then read from underlying.
    BufferedFile(std::io::BufWriter<std::fs::File>),
}

impl LuaFile {
    fn new_stdin() -> Self {
        LuaFile {
            inner: LuaFileInner::Stdin(BufReader::new(io::stdin())),
            name: "stdin".to_string(),
            is_closed: false,
            ungetc: None,
            line_buffered: false,
        }
    }

    fn new_stdout() -> Self {
        LuaFile {
            inner: LuaFileInner::Stdout,
            name: "stdout".to_string(),
            is_closed: false,
            ungetc: None,
            line_buffered: false,
        }
    }

    fn new_stderr() -> Self {
        LuaFile {
            inner: LuaFileInner::Stderr,
            name: "stderr".to_string(),
            is_closed: false,
            ungetc: None,
            line_buffered: false,
        }
    }

    fn new_file(file: std::fs::File, name: String) -> Self {
        LuaFile {
            inner: LuaFileInner::File(file),
            name,
            is_closed: false,
            ungetc: None,
            line_buffered: false,
        }
    }

    fn is_stdio(&self) -> bool {
        matches!(
            self.inner,
            LuaFileInner::Stdin(_) | LuaFileInner::Stdout | LuaFileInner::Stderr
        )
    }
}

impl Read for LuaFile {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        // Handle pushback byte first
        if let Some(b) = self.ungetc.take() {
            if !buf.is_empty() {
                buf[0] = b;
                if buf.len() == 1 {
                    return Ok(1);
                }
                // Read remaining into rest of buffer
                let n = match &mut self.inner {
                    LuaFileInner::Stdin(r) => r.read(&mut buf[1..])?,
                    LuaFileInner::Stdout | LuaFileInner::Stderr => 0,
                    LuaFileInner::File(f) => f.read(&mut buf[1..])?,
                    LuaFileInner::BufferedFile(bw) => bw.get_mut().read(&mut buf[1..])?,
                };
                return Ok(1 + n);
            }
        }
        match &mut self.inner {
            LuaFileInner::Stdin(r) => r.read(buf),
            LuaFileInner::Stdout => Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "cannot read from stdout",
            )),
            LuaFileInner::Stderr => Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "cannot read from stderr",
            )),
            LuaFileInner::File(f) => f.read(buf),
            LuaFileInner::BufferedFile(bw) => bw.get_mut().read(buf),
        }
    }
}

impl Write for LuaFile {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let n = match &mut self.inner {
            LuaFileInner::Stdin(_) => {
                return Err(io::Error::new(
                    io::ErrorKind::Unsupported,
                    "cannot write to stdin",
                ));
            }
            LuaFileInner::Stdout => io::stdout().write(buf)?,
            LuaFileInner::Stderr => io::stderr().write(buf)?,
            LuaFileInner::File(f) => f.write(buf)?,
            LuaFileInner::BufferedFile(bw) => bw.write(buf)?,
        };
        // Line buffering: flush if the written data contains a newline
        if self.line_buffered && buf.contains(&b'\n') {
            let _ = self.flush();
        }
        Ok(n)
    }

    fn flush(&mut self) -> io::Result<()> {
        match &mut self.inner {
            LuaFileInner::Stdin(_) => Ok(()),
            LuaFileInner::Stdout => io::stdout().flush(),
            LuaFileInner::Stderr => io::stderr().flush(),
            LuaFileInner::File(f) => f.flush(),
            LuaFileInner::BufferedFile(bw) => bw.flush(),
        }
    }
}

impl Seek for LuaFile {
    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
        match &mut self.inner {
            LuaFileInner::File(f) => f.seek(pos),
            LuaFileInner::BufferedFile(bw) => {
                bw.flush()?;
                bw.get_mut().seek(pos)
            }
            _ => Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "cannot seek on stdio",
            )),
        }
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn register_fn(
    gc: &mut GcHeap,
    table: GcIdx<Table>,
    strings: &mut StringInterner,
    name: &'static str,
    func: fn(&mut NativeContext) -> Result<Vec<TValue>, NativeError>,
) {
    let idx = gc.alloc_native(func, name);
    let val = TValue::from_native(idx);
    let key = strings.intern(name.as_bytes());
    gc.get_table_mut(table).raw_set_str(key, val);
}

/// Allocate a LuaFile as userdata with the file metatable attached.
fn alloc_file_userdata(gc: &mut GcHeap, lua_file: LuaFile) -> GcIdx<Userdata> {
    let mt = FILE_METATABLE.with(|cell| *cell.borrow());
    gc.alloc_userdata(Box::new(lua_file), mt)
}

/// Get a string argument from the context, returning the bytes as a Rust String.
fn get_string_arg(ctx: &NativeContext, idx: usize, fname: &str) -> Result<String, NativeError> {
    let val = ctx.args.get(idx).copied().unwrap_or(TValue::nil());
    if let Some(sid) = val.as_string_id() {
        let bytes = ctx.strings.get_bytes(sid).to_vec();
        String::from_utf8(bytes).map_err(|_| {
            NativeError::String(format!(
                "bad argument #{} to '{}' (invalid UTF-8)",
                idx + 1,
                fname
            ))
        })
    } else {
        Err(NativeError::String(format!(
            "bad argument #{} to '{}' (string expected, got {})",
            idx + 1,
            fname,
            type_name(val)
        )))
    }
}

/// Get optional string argument (nil returns None, string returns Some(String), else error).
fn get_opt_string_arg(
    ctx: &NativeContext,
    idx: usize,
    fname: &str,
) -> Result<Option<String>, NativeError> {
    let val = ctx.args.get(idx).copied().unwrap_or(TValue::nil());
    if val.is_nil() {
        return Ok(None);
    }
    get_string_arg(ctx, idx, fname).map(Some)
}

fn type_name(val: TValue) -> &'static str {
    if val.is_nil() {
        "nil"
    } else if val.is_bool() {
        "boolean"
    } else if val.is_integer() || val.is_float() {
        "number"
    } else if val.is_string() {
        "string"
    } else if val.is_table() {
        "table"
    } else if val.is_function() {
        "function"
    } else {
        "userdata"
    }
}

/// Extract a GcIdx<Userdata> from a TValue, ensuring it's a LuaFile userdata.
fn get_file_arg(
    ctx: &NativeContext,
    idx: usize,
    fname: &str,
) -> Result<GcIdx<Userdata>, NativeError> {
    let val = ctx.args.get(idx).copied().unwrap_or(TValue::nil());
    if let Some(ud_idx) = val.as_userdata_idx() {
        let ud = ctx.gc.get_userdata(ud_idx);
        if ud.data.downcast_ref::<LuaFile>().is_some() {
            return Ok(ud_idx);
        }
    }
    let got = if ctx.args.get(idx).is_none() {
        "got no value".to_string()
    } else {
        let tname = selune_core::object::obj_type_name(val, ctx.gc, ctx.strings);
        format!("FILE* expected, got {}", tname)
    };
    Err(NativeError::String(format!(
        "bad argument #{} to '{}' ({})",
        idx + 1,
        fname,
        got,
    )))
}

/// Return a Lua-style I/O error: nil, errmsg, errno.
fn io_error_result(strings: &mut StringInterner, err: io::Error) -> Vec<TValue> {
    let msg = err.to_string();
    let sid = strings.intern_or_create(msg.as_bytes());
    let errno = err.raw_os_error().unwrap_or(0) as i64;
    vec![
        TValue::nil(),
        TValue::from_string_id(sid),
        TValue::from_integer(errno),
    ]
}

/// Return a Lua-style I/O error with filename prefix: nil, "filename: errmsg", errno.
fn io_error_result_with_name(
    strings: &mut StringInterner,
    filename: &str,
    err: io::Error,
) -> Vec<TValue> {
    let msg = format!("{}: {}", filename, err);
    let sid = strings.intern_or_create(msg.as_bytes());
    let errno = err.raw_os_error().unwrap_or(0) as i64;
    vec![
        TValue::nil(),
        TValue::from_string_id(sid),
        TValue::from_integer(errno),
    ]
}

/// Get a mutable reference to the LuaFile inside a userdata, using a raw pointer
/// to work around the borrow checker. The caller must ensure exclusive access.
///
/// # Safety
/// The returned pointer is valid as long as `gc` is not used to reallocate the
/// userdata arena. The caller must ensure no other references to this userdata
/// exist while the returned pointer is live.
unsafe fn get_lua_file_ptr(gc: &mut GcHeap, ud_idx: GcIdx<Userdata>) -> *mut LuaFile {
    let ud = gc.get_userdata_mut(ud_idx);
    let any_ref: &mut dyn std::any::Any = &mut *ud.data;
    match any_ref.downcast_mut::<LuaFile>() {
        Some(lf) => lf as *mut LuaFile,
        None => std::ptr::null_mut(),
    }
}

// ---------------------------------------------------------------------------
// Core read implementation (shared by io.read and f:read)
// ---------------------------------------------------------------------------

#[derive(Clone)]
enum ReadFormat {
    Number,       // "*n" or "n"
    Line,         // "*l" or "l" (default) - line without newline
    LineWithNL,   // "*L" or "L" - line with newline
    All,          // "*a" or "a" - read all
    Bytes(usize), // integer N - read N bytes
}

/// Parse a read format from a TValue, with access to both gc and strings.
fn parse_read_format_full(
    val: TValue,
    gc: &GcHeap,
    strings: &StringInterner,
) -> Result<ReadFormat, NativeError> {
    // Integer argument: read N bytes
    if let Some(n) = val.as_full_integer(gc) {
        if n < 0 {
            return Err(NativeError::String(
                "bad argument to 'read' (invalid format)".to_string(),
            ));
        }
        return Ok(ReadFormat::Bytes(n as usize));
    }
    // Float that is a whole number
    if let Some(f) = val.as_float() {
        if f >= 0.0 && f == (f as usize as f64) {
            return Ok(ReadFormat::Bytes(f as usize));
        }
    }
    // String format
    if let Some(sid) = val.as_string_id() {
        let bytes = strings.get_bytes(sid);
        let s = std::str::from_utf8(bytes).unwrap_or("");
        // Strip leading "*" for compat (Lua 5.3 used *n, *l, *L, *a; 5.4 also accepts without *)
        let s = s.strip_prefix('*').unwrap_or(s);
        return match s {
            "n" | "num" | "number" => Ok(ReadFormat::Number),
            "l" | "line" => Ok(ReadFormat::Line),
            "L" => Ok(ReadFormat::LineWithNL),
            "a" | "all" => Ok(ReadFormat::All),
            _ => Err(NativeError::String(format!(
                "bad argument to 'read' (invalid format '{}')",
                s
            ))),
        };
    }
    Err(NativeError::String(
        "bad argument to 'read' (invalid format)".to_string(),
    ))
}

fn read_one_format(
    lua_file: &mut LuaFile,
    fmt: &ReadFormat,
    gc: &mut GcHeap,
    strings: &mut StringInterner,
) -> Result<TValue, NativeError> {
    match fmt {
        ReadFormat::Line => read_line(lua_file, false, strings),
        ReadFormat::LineWithNL => read_line(lua_file, true, strings),
        ReadFormat::All => read_all(lua_file, strings),
        ReadFormat::Number => read_number(lua_file, gc),
        ReadFormat::Bytes(n) => read_bytes(lua_file, *n, strings),
    }
}

fn read_line(
    lua_file: &mut LuaFile,
    keep_newline: bool,
    strings: &mut StringInterner,
) -> Result<TValue, NativeError> {
    let mut line = Vec::new();
    let n = read_line_bytes(lua_file, &mut line)?;
    if n == 0 && line.is_empty() {
        // EOF
        return Ok(TValue::nil());
    }
    if !keep_newline {
        // Strip trailing \n (and \r\n)
        if line.last() == Some(&b'\n') {
            line.pop();
            if line.last() == Some(&b'\r') {
                line.pop();
            }
        }
    }
    let sid = strings.intern_or_create(&line);
    Ok(TValue::from_string_id(sid))
}

/// Read bytes until newline or EOF. Returns number of bytes read.
fn read_line_bytes(lua_file: &mut LuaFile, buf: &mut Vec<u8>) -> Result<usize, NativeError> {
    let mut total = 0;
    let mut byte = [0u8; 1];
    loop {
        match lua_file.read(&mut byte) {
            Ok(0) => break, // EOF
            Ok(_) => {
                buf.push(byte[0]);
                total += 1;
                if byte[0] == b'\n' {
                    break;
                }
            }
            Err(e) => {
                let errno = e.raw_os_error().unwrap_or(0);
                return Err(NativeError::IoError(e.to_string(), errno));
            }
        }
    }
    Ok(total)
}

fn read_all(lua_file: &mut LuaFile, strings: &mut StringInterner) -> Result<TValue, NativeError> {
    let mut buf = Vec::new();
    lua_file.read_to_end(&mut buf).map_err(|e| {
        let errno = e.raw_os_error().unwrap_or(0);
        NativeError::IoError(e.to_string(), errno)
    })?;
    let sid = strings.intern_or_create(&buf);
    Ok(TValue::from_string_id(sid))
}

/// Read a single byte from the file, returning None on EOF.
fn read_byte(lua_file: &mut LuaFile) -> Option<u8> {
    let mut byte = [0u8; 1];
    match lua_file.read(&mut byte) {
        Ok(0) => None,
        Ok(_) => Some(byte[0]),
        Err(_) => None,
    }
}

/// PUC-compatible number reader. Mirrors liolib.c's read_number with single look-ahead.
fn read_number(lua_file: &mut LuaFile, gc: &mut GcHeap) -> Result<TValue, NativeError> {
    const MAX_NUM_LEN: usize = 200;
    let mut buf = Vec::new();
    // `c` is the current look-ahead character (like rn.c in PUC)
    let mut c: Option<u8>;

    // Skip whitespace
    loop {
        c = read_byte(lua_file);
        match c {
            None => return Ok(TValue::nil()),
            Some(b) if (b as char).is_ascii_whitespace() => continue,
            _ => break,
        }
    }

    // Helper: test if current look-ahead matches any char in `chars`. If so, consume it.
    // Returns true if consumed.
    macro_rules! test_and_consume {
        ($c:expr, $lua_file:expr, $buf:expr, $chars:expr) => {{
            let mut matched = false;
            if let Some(ch) = $c {
                for &expected in $chars.as_bytes() {
                    if ch == expected {
                        $buf.push(ch);
                        $c = read_byte($lua_file);
                        matched = true;
                        break;
                    }
                }
            }
            matched
        }};
    }

    // Read digits (hex or decimal). Returns count of digits read.
    macro_rules! read_digits {
        ($c:expr, $lua_file:expr, $buf:expr, $hex:expr) => {{
            let mut count = 0usize;
            while $buf.len() < MAX_NUM_LEN {
                if let Some(ch) = $c {
                    let is_digit = if $hex {
                        ch.is_ascii_hexdigit()
                    } else {
                        ch.is_ascii_digit()
                    };
                    if is_digit {
                        $buf.push(ch);
                        $c = read_byte($lua_file);
                        count += 1;
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            }
            count
        }};
    }

    // Optional sign
    test_and_consume!(c, lua_file, buf, "+-");

    // Check for hex prefix
    let hex;
    let mut count;
    if test_and_consume!(c, lua_file, buf, "0") {
        if test_and_consume!(c, lua_file, buf, "xX") {
            hex = true;
            count = 0;
        } else {
            hex = false;
            count = 1; // the '0' itself counts as a digit
        }
    } else {
        hex = false;
        count = 0;
    }

    // Integral part
    count += read_digits!(c, lua_file, buf, hex);

    // Decimal point
    if test_and_consume!(c, lua_file, buf, ".") {
        count += read_digits!(c, lua_file, buf, hex);
    }

    // Exponent (only if we have at least one digit)
    if count > 0 {
        let exp_chars = if hex { "pP" } else { "eE" };
        if test_and_consume!(c, lua_file, buf, exp_chars) {
            test_and_consume!(c, lua_file, buf, "+-");
            read_digits!(c, lua_file, buf, false);
        }
    }

    // Push back the look-ahead character
    if let Some(b) = c {
        lua_file.ungetc = Some(b);
    }

    if buf.len() >= MAX_NUM_LEN {
        return Ok(TValue::nil());
    }

    let token = String::from_utf8(buf).unwrap_or_default();
    match parse_lua_number(&token, gc) {
        Some(v) => Ok(v),
        None => Ok(TValue::nil()),
    }
}

/// Parse a Lua number string (decimal int, hex int, decimal float, hex float).
fn parse_lua_number(s: &str, gc: &mut GcHeap) -> Option<TValue> {
    let trimmed = s.trim();
    let is_hex = {
        let t = if trimmed.starts_with('-') || trimmed.starts_with('+') {
            &trimmed[1..]
        } else {
            trimmed
        };
        t.starts_with("0x") || t.starts_with("0X")
    };

    if is_hex {
        if trimmed.contains('.') || trimmed.contains('p') || trimmed.contains('P') {
            return parse_hex_float(trimmed).map(TValue::from_float);
        }
        // Hex integer (wrapping)
        let (neg, hex_str) = if let Some(r) = trimmed.strip_prefix('-') {
            (true, r)
        } else if let Some(r) = trimmed.strip_prefix('+') {
            (false, r)
        } else {
            (false, trimmed)
        };
        let hex_digits = hex_str
            .strip_prefix("0x")
            .or_else(|| hex_str.strip_prefix("0X"))?;
        let val = u64::from_str_radix(hex_digits, 16).ok()?;
        let ival = if neg {
            (val as i64).wrapping_neg()
        } else {
            val as i64
        };
        return Some(TValue::from_full_integer(ival, gc));
    }

    if let Ok(i) = trimmed.parse::<i64>() {
        return Some(TValue::from_full_integer(i, gc));
    }
    // Reject inf/nan which Rust accepts but Lua doesn't
    let lower = trimmed.to_ascii_lowercase();
    let stripped = lower.trim_start_matches(['+', '-']);
    if !stripped.starts_with("inf") && !stripped.starts_with("nan") {
        if let Ok(f) = trimmed.parse::<f64>() {
            return Some(TValue::from_float(f));
        }
    }
    None
}

/// Parse hex float like "0xABCp-3", "-0x1.8p1"
fn parse_hex_float(s: &str) -> Option<f64> {
    let (neg, rest) = if let Some(r) = s.strip_prefix('-') {
        (true, r)
    } else if let Some(r) = s.strip_prefix('+') {
        (false, r)
    } else {
        (false, s)
    };
    let rest = rest
        .strip_prefix("0x")
        .or_else(|| rest.strip_prefix("0X"))?;

    let mut mantissa: f64 = 0.0;
    let mut frac_exp: i32 = 0;
    let mut in_frac = false;
    let mut idx = 0;
    let bytes = rest.as_bytes();

    while idx < bytes.len() {
        let ch = bytes[idx];
        if ch == b'.' {
            if in_frac {
                return None;
            }
            in_frac = true;
            idx += 1;
            continue;
        }
        if ch == b'p' || ch == b'P' {
            break;
        }
        let digit = match ch {
            b'0'..=b'9' => (ch - b'0') as f64,
            b'a'..=b'f' => (ch - b'a' + 10) as f64,
            b'A'..=b'F' => (ch - b'A' + 10) as f64,
            _ => return None,
        };
        mantissa = mantissa * 16.0 + digit;
        if in_frac {
            frac_exp -= 4;
        }
        idx += 1;
    }

    let mut exp: i32 = 0;
    if idx < bytes.len() && (bytes[idx] == b'p' || bytes[idx] == b'P') {
        idx += 1;
        let mut exp_neg = false;
        if idx < bytes.len() && bytes[idx] == b'-' {
            exp_neg = true;
            idx += 1;
        } else if idx < bytes.len() && bytes[idx] == b'+' {
            idx += 1;
        }
        while idx < bytes.len() && bytes[idx].is_ascii_digit() {
            exp = exp * 10 + (bytes[idx] - b'0') as i32;
            idx += 1;
        }
        if exp_neg {
            exp = -exp;
        }
    }

    let total_exp = exp + frac_exp;
    let result = mantissa * (2.0_f64).powi(total_exp);
    Some(if neg { -result } else { result })
}

fn read_bytes(
    lua_file: &mut LuaFile,
    n: usize,
    strings: &mut StringInterner,
) -> Result<TValue, NativeError> {
    if n == 0 {
        // Read 0 bytes: return "" if not at EOF, nil if at EOF
        let mut test = [0u8; 1];
        match lua_file.read(&mut test) {
            Ok(0) => return Ok(TValue::nil()),
            Ok(_) => {
                // Push back the byte we read
                lua_file.ungetc = Some(test[0]);
                let sid = strings.intern(b"");
                return Ok(TValue::from_string_id(sid));
            }
            Err(e) => {
                let errno = e.raw_os_error().unwrap_or(0);
                return Err(NativeError::IoError(e.to_string(), errno));
            }
        }
    }

    let mut buf = vec![0u8; n];
    let mut total = 0;
    while total < n {
        match lua_file.read(&mut buf[total..]) {
            Ok(0) => break, // EOF
            Ok(read) => total += read,
            Err(e) => {
                let errno = e.raw_os_error().unwrap_or(0);
                return Err(NativeError::IoError(e.to_string(), errno));
            }
        }
    }
    if total == 0 {
        return Ok(TValue::nil());
    }
    buf.truncate(total);
    let sid = strings.intern_or_create(&buf);
    Ok(TValue::from_string_id(sid))
}

// ---------------------------------------------------------------------------
// Core write implementation (shared by io.write and f:write)
// ---------------------------------------------------------------------------

fn do_write(
    lua_file: &mut LuaFile,
    args: &[TValue],
    gc: &GcHeap,
    strings: &StringInterner,
    file_tvalue: TValue,
) -> Result<Vec<TValue>, NativeError> {
    if lua_file.is_closed {
        return Err(NativeError::String(
            "attempt to use a closed file".to_string(),
        ));
    }

    for (i, &arg) in args.iter().enumerate() {
        if let Some(sid) = arg.as_string_id() {
            let bytes = strings.get_bytes(sid);
            lua_file.write_all(bytes).map_err(|e| {
                let errno = e.raw_os_error().unwrap_or(0);
                NativeError::IoError(e.to_string(), errno)
            })?;
        } else if let Some(int_val) = arg.as_full_integer(gc) {
            let s = format!("{}", int_val);
            lua_file.write_all(s.as_bytes()).map_err(|e| {
                let errno = e.raw_os_error().unwrap_or(0);
                NativeError::IoError(e.to_string(), errno)
            })?;
        } else if let Some(f) = arg.as_float() {
            let s = format_lua_float(f);
            lua_file.write_all(s.as_bytes()).map_err(|e| {
                let errno = e.raw_os_error().unwrap_or(0);
                NativeError::IoError(e.to_string(), errno)
            })?;
        } else {
            return Err(NativeError::String(format!(
                "bad argument #{} to 'write' (string expected, got {})",
                i + 1,
                type_name(arg)
            )));
        }
    }

    // Return the file handle itself (for chaining)
    Ok(vec![file_tvalue])
}

/// Format a float the way Lua would for io.write.
/// Lua uses C's "%.14g" format which switches between fixed and scientific notation.
fn format_lua_float(f: f64) -> String {
    if f.is_infinite() {
        if f.is_sign_positive() {
            return "inf".to_string();
        } else {
            return "-inf".to_string();
        }
    }
    if f.is_nan() {
        return "-nan".to_string();
    }

    // Emulate %.14g: use 14 significant digits, choose shorter of fixed vs scientific
    let fixed = format!("{:.14e}", f);
    // Parse the exponent from the scientific notation
    if let Some(e_pos) = fixed.find('e') {
        let exp: i32 = fixed[e_pos + 1..].parse().unwrap_or(0);
        if (-4..14).contains(&exp) {
            // Use fixed-point notation with enough decimal places
            let decimals = if exp >= 0 {
                (13 - exp).max(0) as usize
            } else {
                (13 + (-exp).abs()) as usize
            };
            let mut result = format!("{:.*}", decimals, f);
            // Trim trailing zeros after decimal point (like %g does)
            if result.contains('.') {
                let trimmed = result.trim_end_matches('0');
                let trimmed = trimmed.trim_end_matches('.');
                result = trimmed.to_string();
            }
            return result;
        }
    }
    // Fall back to scientific notation for very large/small numbers
    let s = format!("{:.13e}", f);
    // Trim trailing zeros in the mantissa part
    if let Some(e_pos) = s.find('e') {
        let (mantissa, exponent) = s.split_at(e_pos);
        let trimmed = if mantissa.contains('.') {
            let t = mantissa.trim_end_matches('0');
            t.trim_end_matches('.')
        } else {
            mantissa
        };
        format!("{}{}", trimmed, exponent)
    } else {
        s
    }
}

// ---------------------------------------------------------------------------
// Registration
// ---------------------------------------------------------------------------

/// Register the io library into _ENV.
pub fn register(env_idx: GcIdx<Table>, gc: &mut GcHeap, strings: &mut StringInterner) {
    // 1) Create the file handle metatable with __index methods
    let methods_table = gc.alloc_table(0, 16);
    register_fn(gc, methods_table, strings, "read", native_file_read);
    register_fn(gc, methods_table, strings, "write", native_file_write);
    register_fn(gc, methods_table, strings, "close", native_file_close);
    register_fn(gc, methods_table, strings, "seek", native_file_seek);
    register_fn(gc, methods_table, strings, "setvbuf", native_file_setvbuf);
    register_fn(gc, methods_table, strings, "lines", native_file_lines);
    register_fn(gc, methods_table, strings, "flush", native_file_flush);

    let file_mt = gc.alloc_table(0, 8);
    let index_key = strings.intern(b"__index");
    gc.get_table_mut(file_mt)
        .raw_set_str(index_key, TValue::from_table(methods_table));
    let tostring_key = strings.intern(b"__tostring");
    let tostring_idx = gc.alloc_native(native_file_tostring, "__tostring");
    gc.get_table_mut(file_mt)
        .raw_set_str(tostring_key, TValue::from_native(tostring_idx));
    let gc_key = strings.intern(b"__gc");
    let gc_fn_idx = gc.alloc_native(native_file_gc, "__gc");
    gc.get_table_mut(file_mt)
        .raw_set_str(gc_key, TValue::from_native(gc_fn_idx));
    let close_key = strings.intern(b"__close");
    let close_fn_idx = gc.alloc_native(native_file_gc, "__close");
    gc.get_table_mut(file_mt)
        .raw_set_str(close_key, TValue::from_native(close_fn_idx));
    let name_key = strings.intern(b"__name");
    let name_val = TValue::from_string_id(strings.intern(b"FILE*"));
    gc.get_table_mut(file_mt).raw_set_str(name_key, name_val);

    // Store the metatable in thread-local so alloc_file_userdata can use it
    FILE_METATABLE.with(|cell| {
        *cell.borrow_mut() = Some(file_mt);
    });

    // 2) Create stdin/stdout/stderr userdata
    let stdin_idx = alloc_file_userdata(gc, LuaFile::new_stdin());
    let stdout_idx = alloc_file_userdata(gc, LuaFile::new_stdout());
    let stderr_idx = alloc_file_userdata(gc, LuaFile::new_stderr());

    // Store default input/output
    DEFAULT_INPUT.with(|cell| {
        *cell.borrow_mut() = Some(stdin_idx);
    });
    DEFAULT_OUTPUT.with(|cell| {
        *cell.borrow_mut() = Some(stdout_idx);
    });

    // 3) Create the io table
    let io_table = gc.alloc_table(0, 24);

    // Store stdin/stdout/stderr in io table
    let stdin_key = strings.intern(b"stdin");
    gc.get_table_mut(io_table)
        .raw_set_str(stdin_key, TValue::from_userdata(stdin_idx));
    let stdout_key = strings.intern(b"stdout");
    gc.get_table_mut(io_table)
        .raw_set_str(stdout_key, TValue::from_userdata(stdout_idx));
    let stderr_key = strings.intern(b"stderr");
    gc.get_table_mut(io_table)
        .raw_set_str(stderr_key, TValue::from_userdata(stderr_idx));

    // Register module-level functions
    register_fn(gc, io_table, strings, "open", native_io_open);
    register_fn(gc, io_table, strings, "close", native_io_close);
    register_fn(gc, io_table, strings, "read", native_io_read);
    register_fn(gc, io_table, strings, "write", native_io_write);
    register_fn(gc, io_table, strings, "lines", native_io_lines);
    register_fn(gc, io_table, strings, "input", native_io_input);
    register_fn(gc, io_table, strings, "output", native_io_output);
    register_fn(gc, io_table, strings, "tmpfile", native_io_tmpfile);
    register_fn(gc, io_table, strings, "type", native_io_type);
    register_fn(gc, io_table, strings, "flush", native_io_flush);
    register_fn(gc, io_table, strings, "popen", native_io_popen);

    let io_name = strings.intern(b"io");
    gc.get_table_mut(env_idx)
        .raw_set_str(io_name, TValue::from_table(io_table));
}

// ===========================================================================
// Module-level functions (io.xxx)
// ===========================================================================

// ---------------------------------------------------------------------------
// io.open(filename, mode)
// ---------------------------------------------------------------------------

fn native_io_open(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let filename = get_string_arg(ctx, 0, "open")?;
    let mode_str = get_opt_string_arg(ctx, 1, "open")?.unwrap_or_else(|| "r".to_string());

    // Validate mode: must match [rwa]\+?b?
    if !is_valid_mode(&mode_str) {
        return Err(NativeError::String(format!(
            "bad argument #2 to 'open' (invalid mode '{}')",
            mode_str
        )));
    }

    let file = match open_file(&filename, &mode_str) {
        Ok(f) => f,
        Err(e) => return Ok(io_error_result_with_name(ctx.strings, &filename, e)),
    };

    let lua_file = LuaFile::new_file(file, filename);
    let ud_idx = alloc_file_userdata(ctx.gc, lua_file);
    Ok(vec![TValue::from_userdata(ud_idx)])
}

fn is_valid_mode(mode: &str) -> bool {
    let bytes = mode.as_bytes();
    if bytes.is_empty() {
        return false;
    }
    let mut i = 0;
    // First char must be r, w, or a
    if !matches!(bytes[i], b'r' | b'w' | b'a') {
        return false;
    }
    i += 1;
    // Optional '+'
    if i < bytes.len() && bytes[i] == b'+' {
        i += 1;
    }
    // Optional 'b'
    if i < bytes.len() && bytes[i] == b'b' {
        i += 1;
    }
    i == bytes.len()
}

fn open_file(filename: &str, mode: &str) -> io::Result<std::fs::File> {
    // Strip trailing 'b' (binary mode - no-op on Unix)
    let mode = mode.trim_end_matches('b');
    match mode {
        "r" => std::fs::File::open(filename),
        "w" => std::fs::File::create(filename),
        "a" => std::fs::OpenOptions::new()
            .append(true)
            .create(true)
            .open(filename),
        "r+" => std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .open(filename),
        "w+" => std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(true)
            .open(filename),
        "a+" => std::fs::OpenOptions::new()
            .read(true)
            .append(true)
            .create(true)
            .open(filename),
        _ => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("invalid mode '{}'", mode),
        )),
    }
}

// ---------------------------------------------------------------------------
// io.close([file])
// ---------------------------------------------------------------------------

fn native_io_close(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let ud_idx = if ctx.args.first().copied().unwrap_or(TValue::nil()).is_nil() {
        // Close default output
        DEFAULT_OUTPUT
            .with(|cell| *cell.borrow())
            .ok_or_else(|| NativeError::String("default output file is not set".to_string()))?
    } else {
        get_file_arg(ctx, 0, "close")?
    };

    close_file(ctx.gc, ctx.strings, ud_idx)
}

fn close_file(
    gc: &mut GcHeap,
    strings: &mut StringInterner,
    ud_idx: GcIdx<Userdata>,
) -> Result<Vec<TValue>, NativeError> {
    let ud = gc.get_userdata_mut(ud_idx);
    let lua_file = ud
        .data
        .downcast_mut::<LuaFile>()
        .ok_or_else(|| NativeError::String("not a file".to_string()))?;

    if lua_file.is_closed {
        return Err(NativeError::String(
            "attempt to use a closed file".to_string(),
        ));
    }

    if lua_file.is_stdio() {
        return Ok(vec![
            TValue::nil(),
            TValue::from_string_id(strings.intern(b"cannot close standard file")),
        ]);
    }

    lua_file.is_closed = true;
    let _ = lua_file.flush();
    Ok(vec![TValue::from_bool(true)])
}

// ---------------------------------------------------------------------------
// io.read(...)
// ---------------------------------------------------------------------------

fn native_io_read(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let ud_idx = DEFAULT_INPUT
        .with(|cell| *cell.borrow())
        .ok_or_else(|| NativeError::String("default input file is not set".to_string()))?;

    // Parse formats before borrowing the file mutably
    let formats: Vec<ReadFormat> = if ctx.args.is_empty() {
        vec![ReadFormat::Line]
    } else {
        let mut fmts = Vec::with_capacity(ctx.args.len());
        for &arg in ctx.args.iter() {
            fmts.push(parse_read_format_full(arg, ctx.gc, ctx.strings)?);
        }
        fmts
    };

    // Use unsafe to get a raw pointer to the LuaFile so we can pass gc/strings
    // to read_one_format without borrow conflicts.
    let lua_file_ptr = unsafe { get_lua_file_ptr(ctx.gc, ud_idx) };
    if lua_file_ptr.is_null() {
        return Err(NativeError::String(
            "default input is not a file".to_string(),
        ));
    }
    let lua_file = unsafe { &mut *lua_file_ptr };

    if lua_file.is_closed {
        return Err(NativeError::String(
            "standard input file is closed".to_string(),
        ));
    }

    let mut results = Vec::with_capacity(formats.len());
    for fmt in &formats {
        match read_one_format(lua_file, fmt, ctx.gc, ctx.strings) {
            Ok(val) => results.push(val),
            Err(NativeError::IoError(msg, errno)) => {
                let msg_sid = ctx.strings.intern_or_create(msg.as_bytes());
                return Ok(vec![
                    TValue::nil(),
                    TValue::from_string_id(msg_sid),
                    TValue::from_integer(errno as i64),
                ]);
            }
            Err(e) => return Err(e),
        }
    }
    Ok(results)
}

// ---------------------------------------------------------------------------
// io.write(...)
// ---------------------------------------------------------------------------

fn native_io_write(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let ud_idx = DEFAULT_OUTPUT
        .with(|cell| *cell.borrow())
        .ok_or_else(|| NativeError::String("default output file is not set".to_string()))?;

    let file_tval = TValue::from_userdata(ud_idx);
    let args: Vec<TValue> = ctx.args.to_vec();

    let lua_file_ptr = unsafe { get_lua_file_ptr(ctx.gc, ud_idx) };
    if lua_file_ptr.is_null() {
        return Err(NativeError::String(
            "default output is not a file".to_string(),
        ));
    }
    let lua_file = unsafe { &mut *lua_file_ptr };

    if lua_file.is_closed {
        return Err(NativeError::String(
            "standard output file is closed".to_string(),
        ));
    }

    match do_write(lua_file, &args, ctx.gc, ctx.strings, file_tval) {
        Ok(r) => Ok(r),
        Err(NativeError::IoError(msg, errno)) => {
            let msg_sid = ctx.strings.intern_or_create(msg.as_bytes());
            Ok(vec![
                TValue::nil(),
                TValue::from_string_id(msg_sid),
                TValue::from_integer(errno as i64),
            ])
        }
        Err(e) => Err(e),
    }
}

// ---------------------------------------------------------------------------
// io.input([file])
// ---------------------------------------------------------------------------

fn native_io_input(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let arg = ctx.args.first().copied().unwrap_or(TValue::nil());

    if arg.is_nil() {
        let ud_idx = DEFAULT_INPUT
            .with(|cell| *cell.borrow())
            .ok_or_else(|| NativeError::String("default input file is not set".to_string()))?;
        return Ok(vec![TValue::from_userdata(ud_idx)]);
    }

    // String argument: open file for reading and set as default
    if let Some(sid) = arg.as_string_id() {
        let bytes = ctx.strings.get_bytes(sid).to_vec();
        let filename = String::from_utf8(bytes)
            .map_err(|_| NativeError::String("invalid UTF-8 in filename".to_string()))?;
        let file = open_file(&filename, "r")
            .map_err(|e| NativeError::String(format!("{}: {}", filename, e)))?;
        let lua_file = LuaFile::new_file(file, filename);
        let ud_idx = alloc_file_userdata(ctx.gc, lua_file);
        DEFAULT_INPUT.with(|cell| {
            *cell.borrow_mut() = Some(ud_idx);
        });
        return Ok(vec![TValue::from_userdata(ud_idx)]);
    }

    // Userdata argument: set as default input
    if let Some(ud_idx) = arg.as_userdata_idx() {
        let ud = ctx.gc.get_userdata(ud_idx);
        if ud.data.downcast_ref::<LuaFile>().is_some() {
            DEFAULT_INPUT.with(|cell| {
                *cell.borrow_mut() = Some(ud_idx);
            });
            return Ok(vec![TValue::from_userdata(ud_idx)]);
        }
    }

    let tname = selune_core::object::obj_type_name(arg, ctx.gc, ctx.strings);
    Err(NativeError::String(format!(
        "bad argument #1 to 'input' (FILE* expected, got {})",
        tname
    )))
}

// ---------------------------------------------------------------------------
// io.output([file])
// ---------------------------------------------------------------------------

fn native_io_output(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let arg = ctx.args.first().copied().unwrap_or(TValue::nil());

    if arg.is_nil() {
        let ud_idx = DEFAULT_OUTPUT
            .with(|cell| *cell.borrow())
            .ok_or_else(|| NativeError::String("default output file is not set".to_string()))?;
        return Ok(vec![TValue::from_userdata(ud_idx)]);
    }

    // String argument: open file for writing and set as default
    if let Some(sid) = arg.as_string_id() {
        let bytes = ctx.strings.get_bytes(sid).to_vec();
        let filename = String::from_utf8(bytes)
            .map_err(|_| NativeError::String("invalid UTF-8 in filename".to_string()))?;
        let file = open_file(&filename, "w")
            .map_err(|e| NativeError::String(format!("{}: {}", filename, e)))?;
        let lua_file = LuaFile::new_file(file, filename);
        let ud_idx = alloc_file_userdata(ctx.gc, lua_file);
        DEFAULT_OUTPUT.with(|cell| {
            *cell.borrow_mut() = Some(ud_idx);
        });
        return Ok(vec![TValue::from_userdata(ud_idx)]);
    }

    // Userdata argument: set as default output
    if let Some(ud_idx) = arg.as_userdata_idx() {
        let ud = ctx.gc.get_userdata(ud_idx);
        if ud.data.downcast_ref::<LuaFile>().is_some() {
            DEFAULT_OUTPUT.with(|cell| {
                *cell.borrow_mut() = Some(ud_idx);
            });
            return Ok(vec![TValue::from_userdata(ud_idx)]);
        }
    }

    Err(NativeError::String(
        "bad argument #1 to 'output' (string or FILE* expected)".to_string(),
    ))
}

// ---------------------------------------------------------------------------
// io.tmpfile()
// ---------------------------------------------------------------------------

fn native_io_tmpfile(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    use std::sync::atomic::{AtomicU64, Ordering};
    static COUNTER: AtomicU64 = AtomicU64::new(0);

    let pid = std::process::id();
    let cnt = COUNTER.fetch_add(1, Ordering::Relaxed);
    let name = format!("/tmp/lua_tmpfile_{}_{}", pid, cnt);

    let file = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(true)
        .open(&name);

    match file {
        Ok(f) => {
            // Try to delete the file so it's truly temporary (Unix unlink semantics)
            let _ = std::fs::remove_file(&name);
            let lua_file = LuaFile::new_file(f, name);
            let ud_idx = alloc_file_userdata(ctx.gc, lua_file);
            Ok(vec![TValue::from_userdata(ud_idx)])
        }
        Err(e) => Ok(io_error_result(ctx.strings, e)),
    }
}

// ---------------------------------------------------------------------------
// io.type(obj)
// ---------------------------------------------------------------------------

fn native_io_type(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let arg = ctx.args.first().copied().unwrap_or(TValue::nil());

    if let Some(ud_idx) = arg.as_userdata_idx() {
        let ud = ctx.gc.get_userdata(ud_idx);
        if let Some(lua_file) = ud.data.downcast_ref::<LuaFile>() {
            let result = if lua_file.is_closed {
                "closed file"
            } else {
                "file"
            };
            let sid = ctx.strings.intern(result.as_bytes());
            return Ok(vec![TValue::from_string_id(sid)]);
        }
    }

    // Not a file handle
    Ok(vec![TValue::nil()])
}

// ---------------------------------------------------------------------------
// io.flush()
// ---------------------------------------------------------------------------

fn native_io_flush(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let ud_idx = DEFAULT_OUTPUT
        .with(|cell| *cell.borrow())
        .ok_or_else(|| NativeError::String("default output file is not set".to_string()))?;

    let file_tval = TValue::from_userdata(ud_idx);
    let ud = ctx.gc.get_userdata_mut(ud_idx);
    let lua_file = ud
        .data
        .downcast_mut::<LuaFile>()
        .ok_or_else(|| NativeError::String("default output is not a file".to_string()))?;

    if lua_file.is_closed {
        return Err(NativeError::String(
            "attempt to use a closed file".to_string(),
        ));
    }

    lua_file
        .flush()
        .map_err(|e| NativeError::String(e.to_string()))?;

    Ok(vec![file_tval])
}

// ---------------------------------------------------------------------------
// io.popen(prog, mode) - stub
// ---------------------------------------------------------------------------

fn native_io_popen(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let msg = ctx.strings.intern_or_create(b"popen not supported");
    Ok(vec![TValue::nil(), TValue::from_string_id(msg)])
}

// ---------------------------------------------------------------------------
// io.lines([filename, ...])
// ---------------------------------------------------------------------------

fn native_io_lines(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    const MAXARGLINE: usize = 250;
    let first_arg = ctx.args.first().copied().unwrap_or(TValue::nil());

    // Parse format arguments (args after filename)
    let fmt_args = if ctx.args.len() > 1 {
        &ctx.args[1..]
    } else {
        &[]
    };
    if fmt_args.len() > MAXARGLINE {
        return Err(NativeError::String("too many arguments".to_string()));
    }
    let formats: Vec<ReadFormat> = {
        let mut fmts = Vec::with_capacity(fmt_args.len());
        for &arg in fmt_args {
            fmts.push(parse_read_format_full(arg, ctx.gc, ctx.strings)?);
        }
        fmts
    };

    if first_arg.is_nil() {
        // No filename: iterate on default input
        let ud_idx = DEFAULT_INPUT
            .with(|cell| *cell.borrow())
            .ok_or_else(|| NativeError::String("default input file is not set".to_string()))?;

        let state = LinesIterState {
            file_ud_idx: ud_idx,
            close_on_eof: false,
            formats,
        };
        let state_ud = ctx.gc.alloc_userdata(Box::new(state), None);
        let upvalue = TValue::from_userdata(state_ud);

        let iter_fn =
            ctx.gc
                .alloc_native_with_upvalue(native_lines_iterator, "io.lines iterator", upvalue);
        return Ok(vec![TValue::from_native(iter_fn)]);
    }

    // With filename: open the file, create iterator that closes on EOF
    if let Some(sid) = first_arg.as_string_id() {
        let bytes = ctx.strings.get_bytes(sid).to_vec();
        let filename = String::from_utf8(bytes)
            .map_err(|_| NativeError::String("invalid UTF-8 in filename".to_string()))?;
        let file = open_file(&filename, "r")
            .map_err(|e| NativeError::String(format!("{}: {}", filename, e)))?;
        let lua_file = LuaFile::new_file(file, filename);
        let ud_idx = alloc_file_userdata(ctx.gc, lua_file);

        let state = LinesIterState {
            file_ud_idx: ud_idx,
            close_on_eof: true,
            formats,
        };
        let state_ud = ctx.gc.alloc_userdata(Box::new(state), None);
        let upvalue = TValue::from_userdata(state_ud);

        let iter_fn =
            ctx.gc
                .alloc_native_with_upvalue(native_lines_iterator, "io.lines iterator", upvalue);
        let file_tval = TValue::from_userdata(ud_idx);
        // Return 4 values: (iter, file, nil, file) for the to-be-closed protocol
        return Ok(vec![
            TValue::from_native(iter_fn),
            file_tval,
            TValue::nil(),
            file_tval,
        ]);
    }

    Err(NativeError::String(
        "bad argument #1 to 'lines' (string expected)".to_string(),
    ))
}

/// State for a lines iterator.
struct LinesIterState {
    file_ud_idx: GcIdx<Userdata>,
    close_on_eof: bool,
    /// Read formats for each iteration call. Empty means default "l".
    formats: Vec<ReadFormat>,
}

fn native_lines_iterator(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let state_ud_idx = ctx
        .upvalue
        .as_userdata_idx()
        .ok_or_else(|| NativeError::String("lines iterator: no state".to_string()))?;

    let state_ud = ctx.gc.get_userdata(state_ud_idx);
    let state = state_ud
        .data
        .downcast_ref::<LinesIterState>()
        .ok_or_else(|| NativeError::String("lines iterator: invalid state".to_string()))?;
    let file_ud_idx = state.file_ud_idx;
    let close_on_eof = state.close_on_eof;
    let formats = state.formats.clone();

    // Use unsafe pointer to avoid borrow conflict between userdata and gc/strings
    let lua_file_ptr = unsafe { get_lua_file_ptr(ctx.gc, file_ud_idx) };
    if lua_file_ptr.is_null() {
        return Err(NativeError::String(
            "lines iterator: not a file".to_string(),
        ));
    }
    let lua_file = unsafe { &mut *lua_file_ptr };

    if lua_file.is_closed {
        return Err(NativeError::String("file is already closed".to_string()));
    }

    if formats.is_empty() {
        // Default: read one line
        let val = read_one_format(lua_file, &ReadFormat::Line, ctx.gc, ctx.strings)?;
        if val.is_nil() {
            if close_on_eof {
                let file_ud = ctx.gc.get_userdata_mut(file_ud_idx);
                let lua_file2 = file_ud.data.downcast_mut::<LuaFile>().unwrap();
                let _ = lua_file2.flush();
                lua_file2.is_closed = true;
            }
            return Ok(vec![TValue::nil()]);
        }
        Ok(vec![val])
    } else {
        // Multiple formats: read one value per format
        let mut results = Vec::with_capacity(formats.len());
        for fmt in &formats {
            let val = read_one_format(lua_file, fmt, ctx.gc, ctx.strings)?;
            results.push(val);
        }
        // Check if first result is nil (EOF)
        if results.first().map_or(true, |v| v.is_nil()) {
            if close_on_eof {
                let file_ud = ctx.gc.get_userdata_mut(file_ud_idx);
                let lua_file2 = file_ud.data.downcast_mut::<LuaFile>().unwrap();
                let _ = lua_file2.flush();
                lua_file2.is_closed = true;
            }
            return Ok(vec![TValue::nil()]);
        }
        Ok(results)
    }
}

// ===========================================================================
// File method functions (f:xxx) - called via __index metatable
// ===========================================================================

// ---------------------------------------------------------------------------
// f:read(...)
// ---------------------------------------------------------------------------

fn native_file_read(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let ud_idx = get_file_arg(ctx, 0, "read")?;

    // Parse formats (args after self)
    let format_args = if ctx.args.len() > 1 {
        &ctx.args[1..]
    } else {
        &[]
    };

    let formats: Vec<ReadFormat> = if format_args.is_empty() {
        vec![ReadFormat::Line]
    } else {
        let mut fmts = Vec::with_capacity(format_args.len());
        for &arg in format_args {
            fmts.push(parse_read_format_full(arg, ctx.gc, ctx.strings)?);
        }
        fmts
    };

    let lua_file_ptr = unsafe { get_lua_file_ptr(ctx.gc, ud_idx) };
    if lua_file_ptr.is_null() {
        return Err(NativeError::String("not a file".to_string()));
    }
    let lua_file = unsafe { &mut *lua_file_ptr };

    if lua_file.is_closed {
        return Err(NativeError::String(
            "attempt to use a closed file".to_string(),
        ));
    }

    let mut results = Vec::with_capacity(formats.len());
    for fmt in &formats {
        match read_one_format(lua_file, fmt, ctx.gc, ctx.strings) {
            Ok(val) => results.push(val),
            Err(NativeError::IoError(msg, errno)) => {
                // IO errors return (nil, msg, errno) instead of raising
                let msg_sid = ctx.strings.intern_or_create(msg.as_bytes());
                return Ok(vec![
                    TValue::nil(),
                    TValue::from_string_id(msg_sid),
                    TValue::from_integer(errno as i64),
                ]);
            }
            Err(e) => return Err(e),
        }
    }
    Ok(results)
}

// ---------------------------------------------------------------------------
// f:write(...)
// ---------------------------------------------------------------------------

fn native_file_write(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let ud_idx = get_file_arg(ctx, 0, "write")?;
    let file_tval = ctx.args[0];
    let args: Vec<TValue> = if ctx.args.len() > 1 {
        ctx.args[1..].to_vec()
    } else {
        Vec::new()
    };

    let lua_file_ptr = unsafe { get_lua_file_ptr(ctx.gc, ud_idx) };
    if lua_file_ptr.is_null() {
        return Err(NativeError::String("not a file".to_string()));
    }
    let lua_file = unsafe { &mut *lua_file_ptr };

    match do_write(lua_file, &args, ctx.gc, ctx.strings, file_tval) {
        Ok(r) => Ok(r),
        Err(NativeError::IoError(msg, errno)) => {
            let msg_sid = ctx.strings.intern_or_create(msg.as_bytes());
            Ok(vec![
                TValue::nil(),
                TValue::from_string_id(msg_sid),
                TValue::from_integer(errno as i64),
            ])
        }
        Err(e) => Err(e),
    }
}

// ---------------------------------------------------------------------------
// f:close()
// ---------------------------------------------------------------------------

fn native_file_close(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let ud_idx = get_file_arg(ctx, 0, "close")?;
    close_file(ctx.gc, ctx.strings, ud_idx)
}

// ---------------------------------------------------------------------------
// f:seek([whence [, offset]])
// ---------------------------------------------------------------------------

fn native_file_seek(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let ud_idx = get_file_arg(ctx, 0, "seek")?;

    let whence_arg = ctx.args.get(1).copied().unwrap_or(TValue::nil());
    let offset_arg = ctx.args.get(2).copied().unwrap_or(TValue::nil());

    let whence_str = if whence_arg.is_nil() {
        "cur".to_string()
    } else if let Some(sid) = whence_arg.as_string_id() {
        let bytes = ctx.strings.get_bytes(sid).to_vec();
        String::from_utf8(bytes)
            .map_err(|_| NativeError::String("bad argument #2 to 'seek' (invalid UTF-8)".into()))?
    } else {
        return Err(NativeError::String(
            "bad argument #2 to 'seek' (string expected)".into(),
        ));
    };

    let offset = if offset_arg.is_nil() {
        0i64
    } else if let Some(i) = offset_arg.as_full_integer(ctx.gc) {
        i
    } else if let Some(f) = offset_arg.as_float() {
        f as i64
    } else {
        return Err(NativeError::String(
            "bad argument #3 to 'seek' (number expected)".into(),
        ));
    };

    let seek_from = match whence_str.as_str() {
        "set" => SeekFrom::Start(offset as u64),
        "cur" => SeekFrom::Current(offset),
        "end" => SeekFrom::End(offset),
        _ => {
            return Err(NativeError::String(format!(
                "bad argument #2 to 'seek' (invalid option '{}')",
                whence_str
            )));
        }
    };

    let ud = ctx.gc.get_userdata_mut(ud_idx);
    let lua_file = ud
        .data
        .downcast_mut::<LuaFile>()
        .ok_or_else(|| NativeError::String("not a file".to_string()))?;

    if lua_file.is_closed {
        return Err(NativeError::String(
            "attempt to use a closed file".to_string(),
        ));
    }

    match lua_file.seek(seek_from) {
        Ok(pos) => Ok(vec![TValue::from_full_integer(pos as i64, ctx.gc)]),
        Err(e) => Ok(io_error_result(ctx.strings, e)),
    }
}

// ---------------------------------------------------------------------------
// f:setvbuf(mode [, size]) - stub/no-op
// ---------------------------------------------------------------------------

fn native_file_setvbuf(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let ud_idx = get_file_arg(ctx, 0, "setvbuf")?;
    let mode_sid = ctx
        .args
        .get(1)
        .and_then(|v| v.as_string_id())
        .ok_or_else(|| {
            NativeError::String("bad argument #1 to 'setvbuf' (string expected)".to_string())
        })?;
    let mode_str = std::str::from_utf8(ctx.strings.get_bytes(mode_sid)).unwrap_or("");
    let size = ctx
        .args
        .get(2)
        .and_then(|v| v.as_full_integer(ctx.gc))
        .unwrap_or(0) as usize;

    let lua_file: &mut LuaFile = ctx
        .gc
        .get_userdata_mut(ud_idx)
        .data
        .downcast_mut::<LuaFile>()
        .ok_or_else(|| NativeError::String("not a file".to_string()))?;

    // Helper: extract raw File from BufferedFile
    fn unwrap_bufwriter(mut bw: std::io::BufWriter<std::fs::File>) -> std::fs::File {
        let _ = bw.flush();
        // into_parts extracts the inner writer, discarding any buffered data
        let (file, _) = bw.into_parts();
        file
    }

    match mode_str {
        "no" => {
            // Disable buffering — switch back to raw File if currently buffered
            lua_file.line_buffered = false;
            let old = std::mem::replace(&mut lua_file.inner, LuaFileInner::Stdout);
            lua_file.inner = match old {
                LuaFileInner::BufferedFile(bw) => LuaFileInner::File(unwrap_bufwriter(bw)),
                other => other,
            };
        }
        "full" => {
            // Full buffering
            lua_file.line_buffered = false;
            let buf_size = if size > 0 { size } else { 8192 };
            let old = std::mem::replace(&mut lua_file.inner, LuaFileInner::Stdout);
            lua_file.inner = match old {
                LuaFileInner::File(f) => {
                    LuaFileInner::BufferedFile(std::io::BufWriter::with_capacity(buf_size, f))
                }
                LuaFileInner::BufferedFile(bw) => {
                    let f = unwrap_bufwriter(bw);
                    LuaFileInner::BufferedFile(std::io::BufWriter::with_capacity(buf_size, f))
                }
                other => other, // Can't buffer stdio
            };
        }
        "line" => {
            // Line buffering: use BufWriter + flush on newline
            lua_file.line_buffered = true;
            let buf_size = if size > 0 { size } else { 8192 };
            let old = std::mem::replace(&mut lua_file.inner, LuaFileInner::Stdout);
            lua_file.inner = match old {
                LuaFileInner::File(f) => {
                    LuaFileInner::BufferedFile(std::io::BufWriter::with_capacity(buf_size, f))
                }
                LuaFileInner::BufferedFile(bw) => {
                    let f = unwrap_bufwriter(bw);
                    LuaFileInner::BufferedFile(std::io::BufWriter::with_capacity(buf_size, f))
                }
                other => other,
            };
        }
        _ => {
            return Err(NativeError::String(format!(
                "bad argument #1 to 'setvbuf' (invalid option '{}')",
                mode_str
            )));
        }
    }

    Ok(vec![ctx.args[0]])
}

// ---------------------------------------------------------------------------
// f:lines(...)
// ---------------------------------------------------------------------------

fn native_file_lines(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let ud_idx = get_file_arg(ctx, 0, "lines")?;

    // Parse format arguments (args after self)
    let fmt_args = if ctx.args.len() > 1 {
        &ctx.args[1..]
    } else {
        &[]
    };
    let formats: Vec<ReadFormat> = {
        let mut fmts = Vec::with_capacity(fmt_args.len());
        for &arg in fmt_args {
            fmts.push(parse_read_format_full(arg, ctx.gc, ctx.strings)?);
        }
        fmts
    };

    let state = LinesIterState {
        file_ud_idx: ud_idx,
        close_on_eof: false, // f:lines() does NOT close the file on EOF
        formats,
    };
    let state_ud = ctx.gc.alloc_userdata(Box::new(state), None);
    let upvalue = TValue::from_userdata(state_ud);

    let iter_fn =
        ctx.gc
            .alloc_native_with_upvalue(native_lines_iterator, "file:lines iterator", upvalue);
    Ok(vec![TValue::from_native(iter_fn)])
}

// ---------------------------------------------------------------------------
// f:flush()
// ---------------------------------------------------------------------------

fn native_file_flush(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let ud_idx = get_file_arg(ctx, 0, "flush")?;
    let file_tval = ctx.args[0];

    let ud = ctx.gc.get_userdata_mut(ud_idx);
    let lua_file = ud
        .data
        .downcast_mut::<LuaFile>()
        .ok_or_else(|| NativeError::String("not a file".to_string()))?;

    if lua_file.is_closed {
        return Err(NativeError::String(
            "attempt to use a closed file".to_string(),
        ));
    }

    lua_file
        .flush()
        .map_err(|e| NativeError::String(e.to_string()))?;

    Ok(vec![file_tval])
}

// ---------------------------------------------------------------------------
// __tostring metamethod for file handles
// ---------------------------------------------------------------------------

fn native_file_tostring(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let arg = ctx.args.first().copied().unwrap_or(TValue::nil());

    if let Some(ud_idx) = arg.as_userdata_idx() {
        let ud = ctx.gc.get_userdata(ud_idx);
        if let Some(lua_file) = ud.data.downcast_ref::<LuaFile>() {
            let s = if lua_file.is_closed {
                "file (closed)".to_string()
            } else {
                format!("file (0x{:x})", ud_idx.index())
            };
            let sid = ctx.strings.intern_or_create(s.as_bytes());
            return Ok(vec![TValue::from_string_id(sid)]);
        }
    }

    let sid = ctx.strings.intern(b"file (?)");
    Ok(vec![TValue::from_string_id(sid)])
}

// ---------------------------------------------------------------------------
// __gc / __close metamethod for file handles
// ---------------------------------------------------------------------------

fn native_file_gc(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let arg = ctx.args.first().copied().unwrap_or(TValue::nil());

    if let Some(ud_idx) = arg.as_userdata_idx() {
        let ud = ctx.gc.get_userdata_mut(ud_idx);
        if let Some(lua_file) = ud.data.downcast_mut::<LuaFile>() {
            if !lua_file.is_closed && !lua_file.is_stdio() {
                let _ = lua_file.flush();
                lua_file.is_closed = true;
            }
        }
        Ok(vec![])
    } else {
        let tname = selune_core::object::obj_type_name(arg, ctx.gc, ctx.strings);
        Err(NativeError::String(format!(
            "bad argument #1 to '__gc' (FILE* expected, got {})",
            if arg.is_nil() {
                "no value".to_string()
            } else {
                tname
            }
        )))
    }
}
