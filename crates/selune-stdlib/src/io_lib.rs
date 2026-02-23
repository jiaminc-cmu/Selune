//! Lua 5.4 io library.

use selune_core::gc::{GcHeap, GcIdx, NativeContext, NativeError, Userdata};
use selune_core::string::StringInterner;
use selune_core::table::Table;
use selune_core::value::TValue;
use std::cell::RefCell;
use std::io::{self, BufRead, BufReader, Read, Seek, SeekFrom, Write};

// ---------------------------------------------------------------------------
// Thread-local default file handles
// ---------------------------------------------------------------------------

thread_local! {
    static DEFAULT_INPUT: RefCell<Option<GcIdx<Userdata>>> = RefCell::new(None);
    static DEFAULT_OUTPUT: RefCell<Option<GcIdx<Userdata>>> = RefCell::new(None);
    /// Shared metatable for all file handles.
    static FILE_METATABLE: RefCell<Option<GcIdx<Table>>> = RefCell::new(None);
}

// ---------------------------------------------------------------------------
// LuaFile: the data stored inside userdata
// ---------------------------------------------------------------------------

/// Internal file representation for the io library.
pub struct LuaFile {
    pub inner: LuaFileInner,
    pub name: String,
    pub is_closed: bool,
}

/// Variants for the backing file stream.
pub enum LuaFileInner {
    Stdin(BufReader<io::Stdin>),
    Stdout,
    Stderr,
    File(std::fs::File),
}

impl LuaFile {
    fn new_stdin() -> Self {
        LuaFile {
            inner: LuaFileInner::Stdin(BufReader::new(io::stdin())),
            name: "stdin".to_string(),
            is_closed: false,
        }
    }

    fn new_stdout() -> Self {
        LuaFile {
            inner: LuaFileInner::Stdout,
            name: "stdout".to_string(),
            is_closed: false,
        }
    }

    fn new_stderr() -> Self {
        LuaFile {
            inner: LuaFileInner::Stderr,
            name: "stderr".to_string(),
            is_closed: false,
        }
    }

    fn new_file(file: std::fs::File, name: String) -> Self {
        LuaFile {
            inner: LuaFileInner::File(file),
            name,
            is_closed: false,
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
        }
    }
}

impl Write for LuaFile {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        match &mut self.inner {
            LuaFileInner::Stdin(_) => Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "cannot write to stdin",
            )),
            LuaFileInner::Stdout => io::stdout().write(buf),
            LuaFileInner::Stderr => io::stderr().write(buf),
            LuaFileInner::File(f) => f.write(buf),
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        match &mut self.inner {
            LuaFileInner::Stdin(_) => Ok(()),
            LuaFileInner::Stdout => io::stdout().flush(),
            LuaFileInner::Stderr => io::stderr().flush(),
            LuaFileInner::File(f) => f.flush(),
        }
    }
}

impl Seek for LuaFile {
    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
        match &mut self.inner {
            LuaFileInner::File(f) => f.seek(pos),
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
    Err(NativeError::String(format!(
        "bad argument #{} to '{}' (FILE* expected)",
        idx + 1,
        fname
    )))
}

/// Return a Lua-style I/O error: nil, errmsg.
fn io_error_result(strings: &mut StringInterner, err: io::Error) -> Vec<TValue> {
    let msg = err.to_string();
    let sid = strings.intern_or_create(msg.as_bytes());
    vec![TValue::nil(), TValue::from_string_id(sid)]
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
            "n" => Ok(ReadFormat::Number),
            "l" => Ok(ReadFormat::Line),
            "L" => Ok(ReadFormat::LineWithNL),
            "a" => Ok(ReadFormat::All),
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
    match &mut lua_file.inner {
        LuaFileInner::Stdin(reader) => reader
            .read_until(b'\n', buf)
            .map_err(|e| NativeError::String(e.to_string())),
        LuaFileInner::File(f) => {
            // Read byte by byte for files.
            let mut total = 0;
            let mut byte = [0u8; 1];
            loop {
                match f.read(&mut byte) {
                    Ok(0) => break, // EOF
                    Ok(_) => {
                        buf.push(byte[0]);
                        total += 1;
                        if byte[0] == b'\n' {
                            break;
                        }
                    }
                    Err(e) => return Err(NativeError::String(e.to_string())),
                }
            }
            Ok(total)
        }
        _ => Err(NativeError::String(
            "cannot read from this file".to_string(),
        )),
    }
}

fn read_all(
    lua_file: &mut LuaFile,
    strings: &mut StringInterner,
) -> Result<TValue, NativeError> {
    let mut buf = Vec::new();
    lua_file
        .read_to_end(&mut buf)
        .map_err(|e| NativeError::String(e.to_string()))?;
    let sid = strings.intern_or_create(&buf);
    Ok(TValue::from_string_id(sid))
}

fn read_number(lua_file: &mut LuaFile, gc: &mut GcHeap) -> Result<TValue, NativeError> {
    // Read whitespace-separated token and parse as number.
    let mut token = String::new();
    let mut started = false;

    loop {
        let mut byte = [0u8; 1];
        match lua_file.read(&mut byte) {
            Ok(0) => break, // EOF
            Ok(_) => {
                let ch = byte[0] as char;
                if !started {
                    if ch.is_ascii_whitespace() {
                        continue;
                    }
                    started = true;
                }
                if started {
                    if ch.is_ascii_whitespace() {
                        break;
                    }
                    token.push(ch);
                }
            }
            Err(_) => break,
        }
    }

    if token.is_empty() {
        return Ok(TValue::nil());
    }

    // Try parsing as integer first
    if let Ok(i) = token.parse::<i64>() {
        return Ok(TValue::from_full_integer(i, gc));
    }
    // Handle hex integers (0x...)
    if token.starts_with("0x") || token.starts_with("0X") {
        if let Ok(i) = i64::from_str_radix(&token[2..], 16) {
            return Ok(TValue::from_full_integer(i, gc));
        }
    }
    // Try as float
    if let Ok(f) = token.parse::<f64>() {
        return Ok(TValue::from_float(f));
    }

    Ok(TValue::nil())
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
                // Seek back if possible
                if let LuaFileInner::File(f) = &mut lua_file.inner {
                    let _ = f.seek(SeekFrom::Current(-1));
                }
                let sid = strings.intern(b"");
                return Ok(TValue::from_string_id(sid));
            }
            Err(e) => return Err(NativeError::String(e.to_string())),
        }
    }

    let mut buf = vec![0u8; n];
    let mut total = 0;
    while total < n {
        match lua_file.read(&mut buf[total..]) {
            Ok(0) => break, // EOF
            Ok(read) => total += read,
            Err(e) => return Err(NativeError::String(e.to_string())),
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
                NativeError::String(format!("{}: {}", lua_file.name, e))
            })?;
        } else if let Some(int_val) = arg.as_full_integer(gc) {
            let s = format!("{}", int_val);
            lua_file.write_all(s.as_bytes()).map_err(|e| {
                NativeError::String(format!("{}: {}", lua_file.name, e))
            })?;
        } else if let Some(f) = arg.as_float() {
            let s = format_lua_float(f);
            lua_file.write_all(s.as_bytes()).map_err(|e| {
                NativeError::String(format!("{}: {}", lua_file.name, e))
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
        if exp >= -4 && exp < 14 {
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
pub fn register(
    env_idx: GcIdx<Table>,
    gc: &mut GcHeap,
    strings: &mut StringInterner,
) {
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

    let file = match open_file(&filename, &mode_str) {
        Ok(f) => f,
        Err(e) => return Ok(io_error_result(ctx.strings, e)),
    };

    let lua_file = LuaFile::new_file(file, filename);
    let ud_idx = alloc_file_userdata(ctx.gc, lua_file);
    Ok(vec![TValue::from_userdata(ud_idx)])
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

    close_file(ctx.gc, ud_idx)
}

fn close_file(
    gc: &mut GcHeap,
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
        return Ok(vec![TValue::from_bool(true)]);
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
            "attempt to use a closed file".to_string(),
        ));
    }

    let mut results = Vec::with_capacity(formats.len());
    for fmt in &formats {
        let val = read_one_format(lua_file, fmt, ctx.gc, ctx.strings)?;
        results.push(val);
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

    do_write(lua_file, &args, ctx.gc, ctx.strings, file_tval)
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

    Err(NativeError::String(
        "bad argument #1 to 'input' (string or FILE* expected)".to_string(),
    ))
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
    let first_arg = ctx.args.first().copied().unwrap_or(TValue::nil());

    if first_arg.is_nil() {
        // No filename: iterate on default input with default "l" format
        let ud_idx = DEFAULT_INPUT
            .with(|cell| *cell.borrow())
            .ok_or_else(|| NativeError::String("default input file is not set".to_string()))?;

        let state = LinesIterState {
            file_ud_idx: ud_idx,
            close_on_eof: false,
        };
        let state_ud = ctx.gc.alloc_userdata(Box::new(state), None);

        LINES_ITER_STATE.with(|cell| {
            cell.borrow_mut().push(state_ud);
        });

        let iter_fn = ctx
            .gc
            .alloc_native(native_lines_iterator, "io.lines iterator");
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
        };
        let state_ud = ctx.gc.alloc_userdata(Box::new(state), None);

        LINES_ITER_STATE.with(|cell| {
            cell.borrow_mut().push(state_ud);
        });

        let iter_fn = ctx
            .gc
            .alloc_native(native_lines_iterator, "io.lines iterator");
        return Ok(vec![TValue::from_native(iter_fn)]);
    }

    Err(NativeError::String(
        "bad argument #1 to 'lines' (string expected)".to_string(),
    ))
}

/// State for a lines iterator.
struct LinesIterState {
    file_ud_idx: GcIdx<Userdata>,
    close_on_eof: bool,
}

thread_local! {
    /// Stack of active lines iterator states (most recent = last).
    static LINES_ITER_STATE: RefCell<Vec<GcIdx<Userdata>>> = RefCell::new(Vec::new());
}

fn native_lines_iterator(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let state_ud_idx = LINES_ITER_STATE
        .with(|cell| cell.borrow().last().copied())
        .ok_or_else(|| NativeError::String("lines iterator: no state".to_string()))?;

    let state_ud = ctx.gc.get_userdata(state_ud_idx);
    let state = state_ud
        .data
        .downcast_ref::<LinesIterState>()
        .ok_or_else(|| NativeError::String("lines iterator: invalid state".to_string()))?;
    let file_ud_idx = state.file_ud_idx;
    let close_on_eof = state.close_on_eof;

    // Use unsafe pointer to avoid borrow conflict between userdata and gc/strings
    let lua_file_ptr = unsafe { get_lua_file_ptr(ctx.gc, file_ud_idx) };
    if lua_file_ptr.is_null() {
        return Err(NativeError::String(
            "lines iterator: not a file".to_string(),
        ));
    }
    let lua_file = unsafe { &mut *lua_file_ptr };

    if lua_file.is_closed {
        return Ok(vec![TValue::nil()]);
    }

    // Read one line (default format)
    let val = read_one_format(lua_file, &ReadFormat::Line, ctx.gc, ctx.strings)?;

    if val.is_nil() {
        // EOF reached
        if close_on_eof {
            let file_ud = ctx.gc.get_userdata_mut(file_ud_idx);
            let lua_file2 = file_ud.data.downcast_mut::<LuaFile>().unwrap();
            let _ = lua_file2.flush();
            lua_file2.is_closed = true;
        }
        LINES_ITER_STATE.with(|cell| {
            cell.borrow_mut().pop();
        });
        return Ok(vec![TValue::nil()]);
    }

    Ok(vec![val])
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
        let val = read_one_format(lua_file, fmt, ctx.gc, ctx.strings)?;
        results.push(val);
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

    do_write(lua_file, &args, ctx.gc, ctx.strings, file_tval)
}

// ---------------------------------------------------------------------------
// f:close()
// ---------------------------------------------------------------------------

fn native_file_close(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let ud_idx = get_file_arg(ctx, 0, "close")?;
    close_file(ctx.gc, ud_idx)
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
    let _ud_idx = get_file_arg(ctx, 0, "setvbuf")?;
    // No-op, just return the file
    Ok(vec![ctx.args[0]])
}

// ---------------------------------------------------------------------------
// f:lines(...)
// ---------------------------------------------------------------------------

fn native_file_lines(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let ud_idx = get_file_arg(ctx, 0, "lines")?;

    let state = LinesIterState {
        file_ud_idx: ud_idx,
        close_on_eof: false, // f:lines() does NOT close the file on EOF
    };
    let state_ud = ctx.gc.alloc_userdata(Box::new(state), None);

    LINES_ITER_STATE.with(|cell| {
        cell.borrow_mut().push(state_ud);
    });

    let iter_fn = ctx
        .gc
        .alloc_native(native_lines_iterator, "file:lines iterator");
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
    }

    Ok(vec![])
}
