//! Lua 5.4 string library.

use crate::pattern::{self, CAP_POSITION};
use selune_core::gc::{GcHeap, GcIdx, NativeContext, NativeError, NativeFunction};
use selune_core::string::StringInterner;
use selune_core::table::Table;
use selune_core::value::TValue;

/// Result from string library registration.
pub struct StringLibIndices {
    pub gsub_idx: GcIdx<NativeFunction>,
    pub string_table_idx: GcIdx<Table>,
}

/// Register the string library into _ENV.
/// Returns the GcIdx of string.gsub and the string library table.
pub fn register(
    env_idx: GcIdx<Table>,
    gc: &mut GcHeap,
    strings: &mut StringInterner,
) -> StringLibIndices {
    let string_table = gc.alloc_table(0, 20);

    register_fn(gc, string_table, strings, "len", native_string_len);
    register_fn(gc, string_table, strings, "byte", native_string_byte);
    register_fn(gc, string_table, strings, "char", native_string_char);
    register_fn(gc, string_table, strings, "sub", native_string_sub);
    register_fn(gc, string_table, strings, "rep", native_string_rep);
    register_fn(gc, string_table, strings, "reverse", native_string_reverse);
    register_fn(gc, string_table, strings, "upper", native_string_upper);
    register_fn(gc, string_table, strings, "lower", native_string_lower);
    register_fn(gc, string_table, strings, "format", native_string_format);
    register_fn(gc, string_table, strings, "find", native_string_find);
    register_fn(gc, string_table, strings, "match", native_string_match);
    register_fn(gc, string_table, strings, "gmatch", native_string_gmatch);
    register_fn(gc, string_table, strings, "pack", native_string_pack);
    register_fn(gc, string_table, strings, "unpack", native_string_unpack);
    register_fn(gc, string_table, strings, "packsize", native_string_packsize);

    // string.gsub needs VM access for function replacement
    let gsub_idx = gc.alloc_native(native_string_gsub_stub, "gsub");
    let gsub_val = TValue::from_native(gsub_idx);
    let gsub_name = strings.intern(b"gsub");
    gc.get_table_mut(string_table).raw_set_str(gsub_name, gsub_val);

    let name = strings.intern(b"string");
    gc.get_table_mut(env_idx)
        .raw_set_str(name, TValue::from_table(string_table));

    StringLibIndices {
        gsub_idx,
        string_table_idx: string_table,
    }
}

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

/// Convert Rust's scientific notation (e.g. "1.000000e5") to C printf style ("1.000000e+05").
/// Ensures: sign is always present, exponent is at least 2 digits.
fn fix_scientific_notation(s: &str) -> String {
    // Find the 'e' or 'E'
    let (mantissa, exp_part) = if let Some(pos) = s.find('e') {
        (&s[..pos], &s[pos + 1..])
    } else if let Some(pos) = s.find('E') {
        (&s[..pos], &s[pos + 1..])
    } else {
        return s.to_string();
    };
    let e_char = if s.contains('E') { 'E' } else { 'e' };
    let (sign, digits) = if exp_part.starts_with('-') {
        ("-", &exp_part[1..])
    } else if exp_part.starts_with('+') {
        ("+", &exp_part[1..])
    } else {
        ("+", exp_part)
    };
    let digits = digits.trim_start_matches('0');
    let digits = if digits.is_empty() { "0" } else { digits };
    if digits.len() < 2 {
        format!("{}{}{}{:0>2}", mantissa, e_char, sign, digits)
    } else {
        format!("{}{}{}{}", mantissa, e_char, sign, digits)
    }
}

fn get_string_arg<'a>(
    ctx: &'a NativeContext,
    idx: usize,
    fname: &str,
) -> Result<(&'a [u8], selune_core::string::StringId), NativeError> {
    let val = ctx.args.get(idx).copied().unwrap_or(TValue::nil());
    if let Some(sid) = val.as_string_id() {
        Ok((ctx.strings.get_bytes(sid), sid))
    } else {
        Err(NativeError::String(format!(
            "bad argument #{} to '{}' (string expected)",
            idx + 1,
            fname,
        )))
    }
}

/// Convert a Lua 1-based (possibly negative) index to a 0-based byte index.
fn lua_index(i: i64, len: usize) -> usize {
    if i >= 0 {
        let idx = (i as usize).saturating_sub(1);
        idx.min(len)
    } else {
        let back = (-i) as usize;
        if back > len {
            0
        } else {
            len - back
        }
    }
}

// ---- Simple string functions ----

fn native_string_len(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let (bytes, _) = get_string_arg(ctx, 0, "len")?;
    Ok(vec![TValue::from_full_integer(bytes.len() as i64, ctx.gc)])
}

fn native_string_byte(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let (bytes, _) = get_string_arg(ctx, 0, "byte")?;
    let len = bytes.len();

    let i = ctx
        .args
        .get(1)
        .and_then(|v| v.as_full_integer(ctx.gc))
        .unwrap_or(1);
    let j = ctx
        .args
        .get(2)
        .and_then(|v| v.as_full_integer(ctx.gc))
        .unwrap_or(i);

    // Lua 5.4 posrelatI for start: 1-based
    let start_1 = if i > 0 {
        i as usize
    } else if i == 0 {
        1
    } else {
        let neg = i.unsigned_abs() as usize;
        if neg > len { 0 } else { len - neg + 1 }
    };
    // Lua 5.4 getendpos for end: 1-based
    let end_1 = if j > (len as i64) {
        len
    } else if j >= 0 {
        j as usize
    } else {
        let neg = j.unsigned_abs() as usize;
        if neg > len { 0 } else { len - neg + 1 }
    };
    let start_1 = if start_1 < 1 { 1 } else { start_1 };

    let mut results = Vec::new();
    if start_1 <= end_1 {
        for idx in (start_1 - 1)..end_1 {
            results.push(TValue::from_integer(bytes[idx] as i64));
        }
    }
    Ok(results)
}

fn native_string_char(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let mut result = Vec::with_capacity(ctx.args.len());
    for (i, arg) in ctx.args.iter().enumerate() {
        let val = arg
            .as_full_integer(ctx.gc)
            .ok_or_else(|| {
                NativeError::String(format!(
                    "bad argument #{} to 'char' (number expected)",
                    i + 1
                ))
            })?;
        if val < 0 || val > 255 {
            return Err(NativeError::String(format!(
                "bad argument #{} to 'char' (value out of range)",
                i + 1
            )));
        }
        result.push(val as u8);
    }
    let sid = ctx.strings.intern_or_create(&result);
    Ok(vec![TValue::from_string_id(sid)])
}

fn native_string_sub(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let (bytes, _) = get_string_arg(ctx, 0, "sub")?;
    let len = bytes.len();
    let bytes = bytes.to_vec(); // clone to release borrow on ctx.strings

    let i = ctx
        .args
        .get(1)
        .and_then(|v| v.as_full_integer(ctx.gc))
        .unwrap_or(1);
    let j = ctx
        .args
        .get(2)
        .and_then(|v| v.as_full_integer(ctx.gc))
        .unwrap_or(-1);

    // Lua 5.4 posrelatI for start: 1-based, clamp to [0, len]
    let start_1 = if i > 0 {
        i as usize
    } else if i == 0 {
        1
    } else {
        // i < 0; use unsigned_abs to avoid overflow on i64::MIN
        let neg = i.unsigned_abs() as usize;
        if neg > len { 0 } else { len - neg + 1 }
    };
    // Lua 5.4 getendpos for end: 1-based
    let end_1 = if j > (len as i64) {
        len
    } else if j >= 0 {
        j as usize
    } else {
        // j < 0; use unsigned_abs to avoid overflow on i64::MIN
        let neg = j.unsigned_abs() as usize;
        if neg > len { 0 } else { len - neg + 1 }
    };
    // Clamp start to at least 1
    let start_1 = if start_1 < 1 { 1 } else { start_1 };
    // If start > end, result is empty
    if start_1 > end_1 {
        let sid = ctx.strings.intern(b"");
        return Ok(vec![TValue::from_string_id(sid)]);
    }

    let slice = &bytes[start_1 - 1..end_1];
    let sid = ctx.strings.intern_or_create(slice);
    Ok(vec![TValue::from_string_id(sid)])
}

fn native_string_rep(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let (bytes, _) = get_string_arg(ctx, 0, "rep")?;
    let n = ctx
        .args
        .get(1)
        .and_then(|v| v.as_full_integer(ctx.gc))
        .unwrap_or(0);

    if n <= 0 {
        let sid = ctx.strings.intern(b"");
        return Ok(vec![TValue::from_string_id(sid)]);
    }

    let sep = if ctx.args.len() > 2 {
        if let Some(sid) = ctx.args[2].as_string_id() {
            ctx.strings.get_bytes(sid).to_vec()
        } else {
            Vec::new()
        }
    } else {
        Vec::new()
    };

    let n = n as usize;
    // Lua 5.4 limits string sizes; check for overflow
    let total_len = bytes.len().saturating_mul(n)
        .saturating_add(sep.len().saturating_mul(n.saturating_sub(1)));
    // Lua 5.4 MAX_SIZE is essentially INT_MAX on most platforms
    const MAX_STR_SIZE: usize = 0x7FFF_FFFE; // 2^31 - 2 (Lua 5.4 MAX_SIZE)
    if total_len >= MAX_STR_SIZE {
        return Err(NativeError::String(
            "string result too large".to_string(),
        ));
    }
    let mut result = Vec::with_capacity(total_len);
    for i in 0..n {
        if i > 0 && !sep.is_empty() {
            result.extend_from_slice(&sep);
        }
        result.extend_from_slice(bytes);
    }

    let sid = ctx.strings.intern_or_create(&result);
    Ok(vec![TValue::from_string_id(sid)])
}

fn native_string_reverse(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let (bytes, _) = get_string_arg(ctx, 0, "reverse")?;
    let reversed: Vec<u8> = bytes.iter().rev().copied().collect();
    let sid = ctx.strings.intern_or_create(&reversed);
    Ok(vec![TValue::from_string_id(sid)])
}

fn native_string_upper(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let (bytes, _) = get_string_arg(ctx, 0, "upper")?;
    let upper: Vec<u8> = bytes.iter().map(|b| b.to_ascii_uppercase()).collect();
    let sid = ctx.strings.intern_or_create(&upper);
    Ok(vec![TValue::from_string_id(sid)])
}

fn native_string_lower(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let (bytes, _) = get_string_arg(ctx, 0, "lower")?;
    let lower: Vec<u8> = bytes.iter().map(|b| b.to_ascii_lowercase()).collect();
    let sid = ctx.strings.intern_or_create(&lower);
    Ok(vec![TValue::from_string_id(sid)])
}

fn native_string_format(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let (fmt_bytes, _) = get_string_arg(ctx, 0, "format")?;
    let fmt = fmt_bytes.to_vec(); // clone to avoid borrow issues
    let mut result = Vec::new();
    let mut arg_idx = 1usize;
    let mut i = 0;

    while i < fmt.len() {
        if fmt[i] == b'%' {
            i += 1;
            if i >= fmt.len() {
                break;
            }
            if fmt[i] == b'%' {
                result.push(b'%');
                i += 1;
                continue;
            }

            // Parse flags
            let mut flags = Vec::new();
            while i < fmt.len() && matches!(fmt[i], b'-' | b'+' | b' ' | b'0' | b'#') {
                flags.push(fmt[i]);
                i += 1;
            }

            // Parse width
            let mut width = String::new();
            while i < fmt.len() && fmt[i].is_ascii_digit() {
                width.push(fmt[i] as char);
                i += 1;
            }

            // Parse precision
            let mut precision = String::new();
            if i < fmt.len() && fmt[i] == b'.' {
                i += 1;
                while i < fmt.len() && fmt[i].is_ascii_digit() {
                    precision.push(fmt[i] as char);
                    i += 1;
                }
            }

            if i >= fmt.len() {
                break;
            }

            let spec = fmt[i];
            i += 1;

            let val = ctx.args.get(arg_idx).copied().unwrap_or(TValue::nil());
            arg_idx += 1;

            match spec {
                b'd' | b'i' => {
                    let n = if let Some(i) = val.as_full_integer(ctx.gc) {
                        i
                    } else if let Some(f) = val.as_float() {
                        f as i64
                    } else if let Some(sid) = val.as_string_id() {
                        // Try string-to-number coercion
                        let s = std::str::from_utf8(ctx.strings.get_bytes(sid)).unwrap_or("");
                        let s = s.trim();
                        s.parse::<i64>().or_else(|_| s.parse::<f64>().map(|f| f as i64))
                            .map_err(|_| NativeError::String(
                                format!("bad argument #{} to 'format' (number expected, got string)", arg_idx)
                            ))?
                    } else {
                        return Err(NativeError::String(
                            format!("bad argument #{} to 'format' (number has no integer representation)", arg_idx)
                        ));
                    };
                    let w: usize = width.parse().unwrap_or(0);
                    let formatted = if flags.contains(&b'-') {
                        format!("{:<width$}", n, width = w)
                    } else if flags.contains(&b'0') && !flags.contains(&b'-') {
                        format!("{:0>width$}", n, width = w)
                    } else {
                        format!("{:>width$}", n, width = w)
                    };
                    result.extend_from_slice(formatted.as_bytes());
                }
                b'u' => {
                    let n = val
                        .as_full_integer(ctx.gc)
                        .or_else(|| val.as_float().map(|f| f as i64))
                        .unwrap_or(0) as u64;
                    result.extend_from_slice(format!("{}", n).as_bytes());
                }
                b'f' => {
                    let f = val
                        .as_number(ctx.gc)
                        .unwrap_or(0.0);
                    let prec: usize = precision.parse().unwrap_or(6);
                    result.extend_from_slice(format!("{:.prec$}", f, prec = prec).as_bytes());
                }
                b'e' | b'E' => {
                    let f = val.as_number(ctx.gc).unwrap_or(0.0);
                    let prec: usize = precision.parse().unwrap_or(6);
                    let s = if spec == b'e' {
                        fix_scientific_notation(&format!("{:.prec$e}", f, prec = prec))
                    } else {
                        fix_scientific_notation(&format!("{:.prec$E}", f, prec = prec))
                    };
                    result.extend_from_slice(s.as_bytes());
                }
                b'g' | b'G' => {
                    let f = val.as_number(ctx.gc).unwrap_or(0.0);
                    let prec: usize = precision.parse().unwrap_or(6).max(1);
                    // C %g: use %e if exponent < -4 or >= precision, else %f
                    // significant digits = prec (not decimal places)
                    let sci = format!("{:.prec$e}", f, prec = prec.saturating_sub(1));
                    // Parse exponent from sci notation to decide format
                    let exp = sci.rfind('e')
                        .and_then(|pos| sci[pos + 1..].parse::<i32>().ok())
                        .unwrap_or(0);
                    let s = if exp < -4 || exp >= prec as i32 {
                        fix_scientific_notation(&sci)
                    } else {
                        // Use fixed notation with enough decimal places
                        let decimal_places = if prec as i32 > exp + 1 {
                            (prec as i32 - exp - 1) as usize
                        } else {
                            0
                        };
                        format!("{:.prec$}", f, prec = decimal_places)
                    };
                    // Trim trailing zeros after decimal point (C %g behavior)
                    let s = if s.contains('.') {
                        s.trim_end_matches('0').trim_end_matches('.').to_string()
                    } else {
                        s.to_string()
                    };
                    if spec == b'G' {
                        result.extend_from_slice(s.to_uppercase().as_bytes());
                    } else {
                        result.extend_from_slice(s.as_bytes());
                    }
                }
                b's' => {
                    let s = if let Some(sid) = val.as_string_id() {
                        ctx.strings.get_bytes(sid).to_vec()
                    } else if let Some(int) = val.as_full_integer(ctx.gc) {
                        format!("{}", int).into_bytes()
                    } else if let Some(f) = val.as_float() {
                        format!("{}", f).into_bytes()
                    } else if val.is_nil() {
                        b"nil".to_vec()
                    } else if let Some(b) = val.as_bool() {
                        if b { b"true".to_vec() } else { b"false".to_vec() }
                    } else {
                        b"?".to_vec()
                    };
                    if !precision.is_empty() {
                        let max_len: usize = precision.parse().unwrap_or(usize::MAX);
                        let truncated = &s[..s.len().min(max_len)];
                        let w: usize = width.parse().unwrap_or(0);
                        if flags.contains(&b'-') {
                            result.extend_from_slice(truncated);
                            for _ in truncated.len()..w {
                                result.push(b' ');
                            }
                        } else {
                            for _ in truncated.len()..w {
                                result.push(b' ');
                            }
                            result.extend_from_slice(truncated);
                        }
                    } else {
                        let w: usize = width.parse().unwrap_or(0);
                        if flags.contains(&b'-') {
                            result.extend_from_slice(&s);
                            for _ in s.len()..w {
                                result.push(b' ');
                            }
                        } else {
                            for _ in s.len()..w {
                                result.push(b' ');
                            }
                            result.extend_from_slice(&s);
                        }
                    }
                }
                b'q' => {
                    // Lua 5.4 %q: quoted format for various types
                    if !width.is_empty() || !precision.is_empty() || !flags.is_empty() {
                        return Err(NativeError::String(
                            "invalid conversion specifier '%q' — cannot have modifiers".to_string(),
                        ));
                    }
                    if let Some(sid) = val.as_string_id() {
                        let s = ctx.strings.get_bytes(sid).to_vec();
                        result.push(b'"');
                        let slen = s.len();
                        for idx in 0..slen {
                            let b = s[idx];
                            match b {
                                b'\\' => result.extend_from_slice(b"\\\\"),
                                b'"' => result.extend_from_slice(b"\\\""),
                                b'\n' => { result.push(b'\\'); result.push(b'\n'); }
                                b'\r' => result.extend_from_slice(b"\\r"),
                                0x1a => result.extend_from_slice(b"\\26"),
                                b'\0' => {
                                    // \0 followed by 00 if next char is digit (making \000)
                                    // so the parser reads exactly 3 digits
                                    if idx + 1 < slen && s[idx + 1].is_ascii_digit() {
                                        result.extend_from_slice(b"\\000");
                                    } else {
                                        result.extend_from_slice(b"\\0");
                                    }
                                }
                                _ if b < 32 => {
                                    // Other control characters: \ddd or \d
                                    if idx + 1 < slen && s[idx + 1].is_ascii_digit() {
                                        let esc = format!("\\{:03}", b);
                                        result.extend_from_slice(esc.as_bytes());
                                    } else {
                                        let esc = format!("\\{}", b);
                                        result.extend_from_slice(esc.as_bytes());
                                    }
                                }
                                _ => result.push(b),
                            }
                        }
                        result.push(b'"');
                    } else if let Some(n) = val.as_full_integer(ctx.gc) {
                        result.extend_from_slice(format!("{}", n).as_bytes());
                    } else if let Some(f) = val.as_float() {
                        if f.is_nan() {
                            result.extend_from_slice(b"(0/0)");
                        } else if f.is_infinite() {
                            if f > 0.0 {
                                result.extend_from_slice(b"1/0");
                            } else {
                                result.extend_from_slice(b"-1/0");
                            }
                        } else {
                            // Lua uses %.17g-like format for full precision
                            let s = format!("{:.17e}", f);
                            // Convert to a format that round-trips
                            let reparsed: f64 = s.parse().unwrap_or(f);
                            if reparsed == f {
                                // Use a simpler representation if possible
                                let simple = format!("{:.14}", f);
                                if simple.parse::<f64>().ok() == Some(f) {
                                    result.extend_from_slice(simple.as_bytes());
                                } else {
                                    result.extend_from_slice(s.as_bytes());
                                }
                            } else {
                                result.extend_from_slice(s.as_bytes());
                            }
                        }
                    } else if let Some(b) = val.as_bool() {
                        if b { result.extend_from_slice(b"true"); }
                        else { result.extend_from_slice(b"false"); }
                    } else if val.is_nil() {
                        result.extend_from_slice(b"nil");
                    } else {
                        return Err(NativeError::String(
                            "no literal for non-basic type".to_string(),
                        ));
                    }
                }
                b'c' => {
                    let n = val
                        .as_full_integer(ctx.gc)
                        .unwrap_or(0);
                    result.push((n & 0xFF) as u8);
                }
                b'x' | b'X' => {
                    let n = val
                        .as_full_integer(ctx.gc)
                        .or_else(|| val.as_float().map(|f| f as i64))
                        .unwrap_or(0);
                    if spec == b'x' {
                        result.extend_from_slice(format!("{:x}", n).as_bytes());
                    } else {
                        result.extend_from_slice(format!("{:X}", n).as_bytes());
                    }
                }
                b'o' => {
                    let n = val
                        .as_full_integer(ctx.gc)
                        .or_else(|| val.as_float().map(|f| f as i64))
                        .unwrap_or(0);
                    result.extend_from_slice(format!("{:o}", n).as_bytes());
                }
                b'p' => {
                    // %p: pointer format
                    // nil, booleans, numbers => "(null)"
                    // tables, functions, threads, userdata, strings => hex address
                    let ptr_str = if val.is_nil() || val.as_bool().is_some() || val.as_float().is_some()
                        || val.as_integer().is_some()
                    {
                        "(null)".to_string()
                    } else {
                        // Use raw bits as a unique identifier
                        format!("0x{:014x}", val.raw_bits())
                    };
                    let w: usize = width.parse().unwrap_or(0);
                    if flags.contains(&b'-') {
                        result.extend_from_slice(ptr_str.as_bytes());
                        for _ in ptr_str.len()..w {
                            result.push(b' ');
                        }
                    } else {
                        for _ in ptr_str.len()..w {
                            result.push(b' ');
                        }
                        result.extend_from_slice(ptr_str.as_bytes());
                    }
                }
                _ => {
                    result.push(b'%');
                    result.push(spec);
                }
            }
        } else {
            result.push(fmt[i]);
            i += 1;
        }
    }

    let sid = ctx.strings.intern_or_create(&result);
    Ok(vec![TValue::from_string_id(sid)])
}

// ---- Pattern functions ----

fn native_string_find(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let (subject, _) = get_string_arg(ctx, 0, "find")?;
    let (pat, _) = get_string_arg(ctx, 1, "find")?;
    let subject = subject.to_vec();
    let pat = pat.to_vec();

    let init = ctx
        .args
        .get(2)
        .and_then(|v| v.as_full_integer(ctx.gc))
        .unwrap_or(1);
    let plain = ctx
        .args
        .get(3)
        .map(|v| v.is_truthy())
        .unwrap_or(false);

    let start = if init >= 1 {
        (init as usize).saturating_sub(1)
    } else {
        let back = (-init) as usize;
        if back > subject.len() { 0 } else { subject.len() - back }
    };

    if plain {
        // Plain string search
        if let Some(pos) = find_plain(&subject, &pat, start) {
            let results = vec![
                TValue::from_full_integer((pos + 1) as i64, ctx.gc),
                TValue::from_full_integer((pos + pat.len()) as i64, ctx.gc),
            ];
            return Ok(results);
        }
        return Ok(vec![TValue::nil()]);
    }

    // Validate pattern before matching
    pattern::validate_pattern(&pat)
        .map_err(|e| NativeError::String(format!("bad argument #2 to 'find' ({e})")))?;

    // Pattern search
    match pattern::pattern_find(&subject, &pat, start) {
        Some(ms) => {
            let (match_start, match_end) = ms.captures[0];
            let mut results = vec![
                TValue::from_full_integer((match_start + 1) as i64, ctx.gc),
                TValue::from_full_integer(match_end as i64, ctx.gc),
            ];
            // Add captures
            for i in 1..ms.captures.len() {
                let (cs, ce) = ms.captures[i];
                if ce == CAP_POSITION {
                    results.push(TValue::from_full_integer((cs + 1) as i64, ctx.gc));
                } else {
                    let slice = &subject[cs..ce];
                    let sid = ctx.strings.intern_or_create(slice);
                    results.push(TValue::from_string_id(sid));
                }
            }
            Ok(results)
        }
        None => Ok(vec![TValue::nil()]),
    }
}

fn find_plain(subject: &[u8], pat: &[u8], start: usize) -> Option<usize> {
    if pat.is_empty() {
        return Some(start);
    }
    if pat.len() > subject.len() {
        return None;
    }
    for i in start..=subject.len() - pat.len() {
        if subject[i..i + pat.len()] == *pat {
            return Some(i);
        }
    }
    None
}

fn native_string_match(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let (subject, _) = get_string_arg(ctx, 0, "match")?;
    let (pat, _) = get_string_arg(ctx, 1, "match")?;
    let subject = subject.to_vec();
    let pat = pat.to_vec();

    let init = ctx
        .args
        .get(2)
        .and_then(|v| v.as_full_integer(ctx.gc))
        .unwrap_or(1);
    let start = if init >= 1 {
        (init as usize).saturating_sub(1)
    } else {
        let back = (-init) as usize;
        if back > subject.len() { 0 } else { subject.len() - back }
    };

    pattern::validate_pattern(&pat)
        .map_err(|e| NativeError::String(format!("bad argument #2 to 'match' ({e})")))?;

    match pattern::pattern_find(&subject, &pat, start) {
        Some(ms) => {
            if ms.captures.len() <= 1 {
                // No explicit captures — return full match
                let (s, e) = ms.captures[0];
                let slice = &subject[s..e];
                let sid = ctx.strings.intern_or_create(slice);
                Ok(vec![TValue::from_string_id(sid)])
            } else {
                // Return captures
                let mut results = Vec::new();
                for i in 1..ms.captures.len() {
                    let (cs, ce) = ms.captures[i];
                    if ce == CAP_POSITION {
                        results.push(TValue::from_full_integer((cs + 1) as i64, ctx.gc));
                    } else {
                        let slice = &subject[cs..ce];
                        let sid = ctx.strings.intern_or_create(slice);
                        results.push(TValue::from_string_id(sid));
                    }
                }
                Ok(results)
            }
        }
        None => Ok(vec![TValue::nil()]),
    }
}

/// string.gmatch: returns an iterator function.
/// We store state in a table (subject, pattern, position) and return a native that reads it.
fn native_string_gmatch(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let (pat_bytes, pat_sid) = get_string_arg(ctx, 1, "gmatch")?;
    let pat_bytes = pat_bytes.to_vec();
    pattern::validate_pattern(&pat_bytes)
        .map_err(|e| NativeError::String(format!("bad argument #2 to 'gmatch' ({e})")))?;
    let (_, subj_sid) = get_string_arg(ctx, 0, "gmatch")?;

    // Create state table: {subject_sid, pattern_sid, position}
    let state_table = ctx.gc.alloc_table(4, 0);
    ctx.gc
        .get_table_mut(state_table)
        .raw_seti(1, TValue::from_string_id(subj_sid));
    ctx.gc
        .get_table_mut(state_table)
        .raw_seti(2, TValue::from_string_id(pat_sid));
    ctx.gc
        .get_table_mut(state_table)
        .raw_seti(3, TValue::from_integer(1)); // 1-based position

    // Return (gmatch_iter, state_table)
    let iter_idx = ctx.gc.alloc_native(native_gmatch_iter, "gmatch_iter");
    let iter_val = TValue::from_native(iter_idx);
    Ok(vec![iter_val, TValue::from_table(state_table)])
}

fn native_gmatch_iter(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    // First arg is the state table
    let state_idx = ctx.args[0]
        .as_table_idx()
        .ok_or_else(|| NativeError::String("gmatch: invalid state".to_string()))?;

    let subj_sid = ctx.gc.get_table(state_idx).raw_geti(1).as_string_id()
        .ok_or_else(|| NativeError::String("gmatch: invalid subject".to_string()))?;
    let pat_sid = ctx.gc.get_table(state_idx).raw_geti(2).as_string_id()
        .ok_or_else(|| NativeError::String("gmatch: invalid pattern".to_string()))?;
    let pos = ctx.gc.get_table(state_idx).raw_geti(3)
        .as_full_integer(ctx.gc)
        .unwrap_or(1);

    let subject = ctx.strings.get_bytes(subj_sid).to_vec();
    let pat = ctx.strings.get_bytes(pat_sid).to_vec();

    let start = if pos >= 1 { (pos as usize) - 1 } else { 0 };

    if start > subject.len() {
        return Ok(vec![TValue::nil()]);
    }

    match pattern::pattern_find(&subject, &pat, start) {
        Some(ms) => {
            let (match_start, match_end) = ms.captures[0];
            // Update position in state
            let new_pos = if match_end == match_start {
                match_end + 2 // 1-based, skip past empty match
            } else {
                match_end + 1 // 1-based
            };
            let pos_val = TValue::from_full_integer(new_pos as i64, ctx.gc);
            ctx.gc
                .get_table_mut(state_idx)
                .raw_seti(3, pos_val);

            if ms.captures.len() <= 1 {
                // No explicit captures — return full match
                let slice = &subject[match_start..match_end];
                let sid = ctx.strings.intern_or_create(slice);
                Ok(vec![TValue::from_string_id(sid)])
            } else {
                let mut results = Vec::new();
                for i in 1..ms.captures.len() {
                    let (cs, ce) = ms.captures[i];
                    if ce == CAP_POSITION {
                        results.push(TValue::from_full_integer((cs + 1) as i64, ctx.gc));
                    } else {
                        let slice = &subject[cs..ce];
                        let sid = ctx.strings.intern_or_create(slice);
                        results.push(TValue::from_string_id(sid));
                    }
                }
                Ok(results)
            }
        }
        None => Ok(vec![TValue::nil()]),
    }
}

/// Stub for string.gsub — actual dispatch happens in call_function
fn native_string_gsub_stub(_ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    Err(NativeError::String(
        "string.gsub stub should not be called directly".to_string(),
    ))
}

// ===========================================================================
// string.pack / string.unpack / string.packsize
// ===========================================================================

/// Maximum number of bytes for an integer in pack/unpack.
const PACK_MAX_INTSIZE: usize = 16;
/// Default native int size.
const PACK_NATIVE_INT: usize = 4;
/// Default native alignment.
const PACK_NATIVE_ALIGN: usize = 8;
/// Default size for 'h'/'H' (short).
const PACK_SIZE_SHORT: usize = 2;
/// Default size for 'l'/'L' (long).
const PACK_SIZE_LONG: usize = 8;
/// Default size for 'j'/'J' (Lua integer).
const PACK_SIZE_LUA_INT: usize = 8;
/// Default size for 'T' (size_t).
const PACK_SIZE_SIZE_T: usize = 8;
/// Default size for 'f' (float).
const PACK_SIZE_FLOAT: usize = 4;
/// Default size for 'd' (double).
const PACK_SIZE_DOUBLE: usize = 8;
// Lua number = double, same as PACK_SIZE_DOUBLE.

/// Byte order for pack/unpack.
#[derive(Clone, Copy, PartialEq)]
enum PackEndian {
    Little,
    Big,
}

/// A parsed format option from a pack/unpack format string.
#[derive(Debug, Clone)]
enum PackOption {
    /// Signed integer of n bytes.
    IntSigned(usize),
    /// Unsigned integer of n bytes.
    IntUnsigned(usize),
    /// 32-bit float.
    Float,
    /// 64-bit double.
    Double,
    /// Zero-terminated string.
    ZString,
    /// Length-prefixed string with n-byte length prefix.
    SString(usize),
    /// Fixed-length string of n bytes.
    CString(usize),
    /// One byte of padding (0x00).
    Padding,
    /// Alignment padding to align to the given option's natural size.
    AlignPad(usize),
    /// Set little-endian.
    SetLittle,
    /// Set big-endian.
    SetBig,
    /// Set native endian.
    SetNative,
    /// Set max alignment.
    SetAlign(usize),
    /// Space (ignored).
    Space,
}

impl PackOption {
    /// Return the natural alignment of this option (before clamping by max_align).
    fn natural_align(&self) -> usize {
        match self {
            PackOption::IntSigned(n) | PackOption::IntUnsigned(n) => *n,
            PackOption::Float => PACK_SIZE_FLOAT,
            PackOption::Double => PACK_SIZE_DOUBLE,
            _ => 1,
        }
    }

    /// Whether this option is valid as an alignment target for 'X'.
    /// Only integer and float formats are valid (not strings, padding, etc.)
    fn is_valid_for_x_align(&self) -> bool {
        matches!(
            self,
            PackOption::IntSigned(_)
                | PackOption::IntUnsigned(_)
                | PackOption::Float
                | PackOption::Double
        )
    }
}

/// Parse an optional integer suffix from format bytes starting at position `pos`.
/// Returns (value, new_pos). If no digits, returns (default, pos).
fn parse_fmt_int(fmt: &[u8], pos: usize, default: usize) -> Result<(usize, usize), NativeError> {
    if pos >= fmt.len() || !fmt[pos].is_ascii_digit() {
        return Ok((default, pos));
    }
    let mut i = pos;
    // Guard against absurdly long digit strings to prevent overflow
    let mut val: u64 = 0;
    while i < fmt.len() && fmt[i].is_ascii_digit() {
        val = val
            .checked_mul(10)
            .and_then(|v| v.checked_add((fmt[i] - b'0') as u64))
            .ok_or_else(|| NativeError::String("invalid format (count overflow)".to_string()))?;
        if val > i32::MAX as u64 {
            return Err(NativeError::String(
                "invalid format (count overflow)".to_string(),
            ));
        }
        i += 1;
    }
    Ok((val as usize, i))
}

/// Parse the next format option from `fmt` at position `pos`.
/// Returns (option, new_pos).
fn parse_next_option(fmt: &[u8], pos: usize) -> Result<(PackOption, usize), NativeError> {
    if pos >= fmt.len() {
        return Err(NativeError::String("unexpected end of format".to_string()));
    }
    let c = fmt[pos];
    let next = pos + 1;
    match c {
        b'b' => Ok((PackOption::IntSigned(1), next)),
        b'B' => Ok((PackOption::IntUnsigned(1), next)),
        b'h' => Ok((PackOption::IntSigned(PACK_SIZE_SHORT), next)),
        b'H' => Ok((PackOption::IntUnsigned(PACK_SIZE_SHORT), next)),
        b'l' => Ok((PackOption::IntSigned(PACK_SIZE_LONG), next)),
        b'L' => Ok((PackOption::IntUnsigned(PACK_SIZE_LONG), next)),
        b'j' => Ok((PackOption::IntSigned(PACK_SIZE_LUA_INT), next)),
        b'J' => Ok((PackOption::IntUnsigned(PACK_SIZE_LUA_INT), next)),
        b'T' => Ok((PackOption::IntUnsigned(PACK_SIZE_SIZE_T), next)),
        b'f' => Ok((PackOption::Float, next)),
        b'd' => Ok((PackOption::Double, next)),
        b'n' => Ok((PackOption::Double, next)), // Lua number = double
        b'i' => {
            let (n, p) = parse_fmt_int(fmt, next, PACK_NATIVE_INT)?;
            if n < 1 || n > PACK_MAX_INTSIZE {
                return Err(NativeError::String(format!(
                    "integral size ({n}) out of limits [1,{PACK_MAX_INTSIZE}]"
                )));
            }
            Ok((PackOption::IntSigned(n), p))
        }
        b'I' => {
            let (n, p) = parse_fmt_int(fmt, next, PACK_NATIVE_INT)?;
            if n < 1 || n > PACK_MAX_INTSIZE {
                return Err(NativeError::String(format!(
                    "integral size ({n}) out of limits [1,{PACK_MAX_INTSIZE}]"
                )));
            }
            Ok((PackOption::IntUnsigned(n), p))
        }
        b's' => {
            let (n, p) = parse_fmt_int(fmt, next, PACK_SIZE_SIZE_T)?;
            if n < 1 || n > PACK_MAX_INTSIZE {
                return Err(NativeError::String(format!(
                    "integral size ({n}) out of limits [1,{PACK_MAX_INTSIZE}]"
                )));
            }
            Ok((PackOption::SString(n), p))
        }
        b'z' => Ok((PackOption::ZString, next)),
        b'c' => {
            if next >= fmt.len() || !fmt[next].is_ascii_digit() {
                return Err(NativeError::String(
                    "missing size for format option 'c'".to_string(),
                ));
            }
            let (n, p) = parse_fmt_int(fmt, next, 0)?;
            Ok((PackOption::CString(n), p))
        }
        b'x' => Ok((PackOption::Padding, next)),
        b'X' => {
            // Alignment to next option's size. Parse the next option to get its size.
            if next >= fmt.len() {
                return Err(NativeError::String(
                    "invalid next option for option 'X'".to_string(),
                ));
            }
            let (inner, p) = parse_next_option(fmt, next)?;
            if !inner.is_valid_for_x_align() {
                return Err(NativeError::String(
                    "invalid next option for option 'X'".to_string(),
                ));
            }
            let align_to = inner.natural_align();
            Ok((PackOption::AlignPad(align_to), p))
        }
        b'<' => Ok((PackOption::SetLittle, next)),
        b'>' => Ok((PackOption::SetBig, next)),
        b'=' => Ok((PackOption::SetNative, next)),
        b'!' => {
            let (n, p) = parse_fmt_int(fmt, next, PACK_NATIVE_ALIGN)?;
            if n > PACK_MAX_INTSIZE {
                return Err(NativeError::String(format!(
                    "alignment ({n}) out of limits [1,{PACK_MAX_INTSIZE}]"
                )));
            }
            // n=0 is not valid for alignment, but !0 isn't meaningful. Lua allows !1..!16.
            // However `!` (no number) = native align = 8.
            if n == 0 {
                return Err(NativeError::String(format!(
                    "alignment ({n}) out of limits [1,{PACK_MAX_INTSIZE}]"
                )));
            }
            if !n.is_power_of_two() {
                return Err(NativeError::String(format!(
                    "alignment {n} is not power of 2"
                )));
            }
            Ok((PackOption::SetAlign(n), p))
        }
        b' ' => Ok((PackOption::Space, next)),
        _ => Err(NativeError::String(format!(
            "invalid format option '{}'",
            c as char
        ))),
    }
}

/// Compute alignment padding needed to align `offset` to `align` (clamped by `max_align`).
fn alignment_padding(offset: usize, natural_align: usize, max_align: usize) -> usize {
    let align = natural_align.min(max_align);
    if align <= 1 {
        return 0;
    }
    let remainder = offset % align;
    if remainder == 0 {
        0
    } else {
        align - remainder
    }
}

/// Pack a signed integer value into `n` bytes with the given endianness.
fn pack_int_signed(
    val: i64,
    n: usize,
    endian: PackEndian,
    buf: &mut Vec<u8>,
) -> Result<(), NativeError> {
    // Check that val fits in n bytes (signed range)
    if n < 8 {
        let max = (1i64 << (n * 8 - 1)) - 1;
        let min = -(1i64 << (n * 8 - 1));
        if val > max || val < min {
            return Err(NativeError::String(format!(
                "{val} overflow in format 'i{n}'"
            )));
        }
    }
    // Write n bytes
    let bytes = val.to_le_bytes(); // always start from LE representation
    match endian {
        PackEndian::Little => {
            // For signed, sign-extend if n > 8
            for i in 0..n {
                if i < 8 {
                    buf.push(bytes[i]);
                } else {
                    // sign extension
                    buf.push(if val < 0 { 0xFF } else { 0x00 });
                }
            }
        }
        PackEndian::Big => {
            // Write in big-endian order
            for i in (0..n).rev() {
                if i < 8 {
                    buf.push(bytes[i]);
                } else {
                    buf.push(if val < 0 { 0xFF } else { 0x00 });
                }
            }
        }
    }
    Ok(())
}

/// Pack an unsigned integer value into `n` bytes with the given endianness.
fn pack_int_unsigned(
    val: i64,
    n: usize,
    endian: PackEndian,
    buf: &mut Vec<u8>,
) -> Result<(), NativeError> {
    // For unsigned packing, val interpreted as unsigned
    // Check range: if n < 8, then val must fit in [0, 2^(n*8)-1]
    if n < 8 {
        let umax = (1u64 << (n * 8)) - 1;
        let uval = val as u64;
        // If val is negative (as i64), but n < 8, it's an overflow
        if val < 0 || uval > umax {
            return Err(NativeError::String(format!(
                "{val} overflow in format 'I{n}'"
            )));
        }
    } else if n == 8 {
        // Any i64 is valid as u64 when n >= 8
    }
    let uval = val as u64;
    let bytes = uval.to_le_bytes();
    match endian {
        PackEndian::Little => {
            for i in 0..n {
                if i < 8 {
                    buf.push(bytes[i]);
                } else {
                    buf.push(0x00);
                }
            }
        }
        PackEndian::Big => {
            for i in (0..n).rev() {
                if i < 8 {
                    buf.push(bytes[i]);
                } else {
                    buf.push(0x00);
                }
            }
        }
    }
    Ok(())
}

/// Unpack a signed integer from `n` bytes. For n > 8, check that the value
/// fits in a Lua integer (i64).
fn unpack_int_signed_checked(
    data: &[u8],
    n: usize,
    endian: PackEndian,
) -> Result<i64, NativeError> {
    let mut le_bytes = [0u8; 16];
    match endian {
        PackEndian::Little => {
            le_bytes[..n].copy_from_slice(&data[..n]);
        }
        PackEndian::Big => {
            for i in 0..n {
                le_bytes[i] = data[n - 1 - i];
            }
        }
    }

    // For n <= 8, just sign-extend and read
    if n <= 8 {
        let sign = if le_bytes[n - 1] & 0x80 != 0 {
            0xFF
        } else {
            0x00
        };
        for i in n..8 {
            le_bytes[i] = sign;
        }
        return Ok(i64::from_le_bytes([
            le_bytes[0],
            le_bytes[1],
            le_bytes[2],
            le_bytes[3],
            le_bytes[4],
            le_bytes[5],
            le_bytes[6],
            le_bytes[7],
        ]));
    }

    // For n > 8, the extra bytes must be sign-extension of byte 7
    let sign = if le_bytes[7] & 0x80 != 0 {
        0xFF
    } else {
        0x00
    };
    for i in 8..n {
        if le_bytes[i] != sign {
            return Err(NativeError::String(format!(
                "{n}-byte integer does not fit into Lua Integer"
            )));
        }
    }
    Ok(i64::from_le_bytes([
        le_bytes[0],
        le_bytes[1],
        le_bytes[2],
        le_bytes[3],
        le_bytes[4],
        le_bytes[5],
        le_bytes[6],
        le_bytes[7],
    ]))
}

/// Unpack an unsigned integer from `n` bytes, checking if it fits in Lua integer.
fn unpack_int_unsigned_checked(
    data: &[u8],
    n: usize,
    endian: PackEndian,
) -> Result<i64, NativeError> {
    let mut le_bytes = [0u8; 16];
    match endian {
        PackEndian::Little => {
            le_bytes[..n].copy_from_slice(&data[..n]);
        }
        PackEndian::Big => {
            for i in 0..n {
                le_bytes[i] = data[n - 1 - i];
            }
        }
    }
    // All bytes beyond index 7 must be 0 for unsigned to fit in u64/i64
    for i in 8..n {
        if le_bytes[i] != 0 {
            return Err(NativeError::String(format!(
                "{n}-byte unsigned integer does not fit into Lua Integer"
            )));
        }
    }
    let val = u64::from_le_bytes([
        le_bytes[0],
        le_bytes[1],
        le_bytes[2],
        le_bytes[3],
        le_bytes[4],
        le_bytes[5],
        le_bytes[6],
        le_bytes[7],
    ]);
    Ok(val as i64)
}

/// string.pack(fmt, v1, v2, ...)
fn native_string_pack(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let (fmt_bytes, _) = get_string_arg(ctx, 0, "pack")?;
    let fmt = fmt_bytes.to_vec();

    let mut buf: Vec<u8> = Vec::new();
    let mut endian = PackEndian::Little; // default: little-endian (native on most platforms)
    let mut max_align: usize = 1; // default: no alignment
    let mut arg_idx = 1usize;
    let mut fpos = 0usize;

    while fpos < fmt.len() {
        let (opt, new_fpos) = parse_next_option(&fmt, fpos)?;
        fpos = new_fpos;

        match opt {
            PackOption::SetLittle => {
                endian = PackEndian::Little;
            }
            PackOption::SetBig => {
                endian = PackEndian::Big;
            }
            PackOption::SetNative => {
                // Native endian detection
                endian = if cfg!(target_endian = "little") {
                    PackEndian::Little
                } else {
                    PackEndian::Big
                };
            }
            PackOption::SetAlign(n) => {
                max_align = n;
            }
            PackOption::Space => {}
            PackOption::IntSigned(n) => {
                // Add alignment padding
                let pad = alignment_padding(buf.len(), n, max_align);
                buf.extend(std::iter::repeat(0u8).take(pad));
                let val = get_int_arg(ctx, arg_idx, "pack")?;
                arg_idx += 1;
                pack_int_signed(val, n, endian, &mut buf)?;
            }
            PackOption::IntUnsigned(n) => {
                let pad = alignment_padding(buf.len(), n, max_align);
                buf.extend(std::iter::repeat(0u8).take(pad));
                let val = get_int_arg(ctx, arg_idx, "pack")?;
                arg_idx += 1;
                pack_int_unsigned(val, n, endian, &mut buf)?;
            }
            PackOption::Float => {
                let pad = alignment_padding(buf.len(), PACK_SIZE_FLOAT, max_align);
                buf.extend(std::iter::repeat(0u8).take(pad));
                let val = get_number_arg(ctx, arg_idx, "pack")?;
                arg_idx += 1;
                let f = val as f32;
                let bytes = f.to_le_bytes();
                match endian {
                    PackEndian::Little => buf.extend_from_slice(&bytes),
                    PackEndian::Big => {
                        for i in (0..4).rev() {
                            buf.push(bytes[i]);
                        }
                    }
                }
            }
            PackOption::Double => {
                let pad = alignment_padding(buf.len(), PACK_SIZE_DOUBLE, max_align);
                buf.extend(std::iter::repeat(0u8).take(pad));
                let val = get_number_arg(ctx, arg_idx, "pack")?;
                arg_idx += 1;
                let bytes = val.to_le_bytes();
                match endian {
                    PackEndian::Little => buf.extend_from_slice(&bytes),
                    PackEndian::Big => {
                        for i in (0..8).rev() {
                            buf.push(bytes[i]);
                        }
                    }
                }
            }
            PackOption::ZString => {
                let (s, _) = get_string_arg_for_pack(ctx, arg_idx, "pack")?;
                arg_idx += 1;
                // Check that string doesn't contain zeros
                if s.contains(&0u8) {
                    return Err(NativeError::String(
                        "string contains zeros".to_string(),
                    ));
                }
                buf.extend_from_slice(&s);
                buf.push(0);
            }
            PackOption::SString(n) => {
                let (s, _) = get_string_arg_for_pack(ctx, arg_idx, "pack")?;
                arg_idx += 1;
                let len = s.len();
                // Check that length fits in n bytes
                if n < 8 {
                    let max_len = (1u64 << (n * 8)) - 1;
                    if (len as u64) > max_len {
                        return Err(NativeError::String(format!(
                            "string length does not fit in given size"
                        )));
                    }
                }
                // Alignment for the length prefix
                let pad = alignment_padding(buf.len(), n, max_align);
                buf.extend(std::iter::repeat(0u8).take(pad));
                // Pack the length as an unsigned integer
                pack_int_unsigned(len as i64, n, endian, &mut buf)?;
                buf.extend_from_slice(&s);
            }
            PackOption::CString(n) => {
                let (s, _) = get_string_arg_for_pack(ctx, arg_idx, "pack")?;
                arg_idx += 1;
                if s.len() > n {
                    return Err(NativeError::String(format!(
                        "string longer than given size"
                    )));
                }
                buf.extend_from_slice(&s);
                // Pad with zeros if string is shorter
                for _ in s.len()..n {
                    buf.push(0);
                }
            }
            PackOption::Padding => {
                buf.push(0);
            }
            PackOption::AlignPad(align_to) => {
                let pad = alignment_padding(buf.len(), align_to, max_align);
                buf.extend(std::iter::repeat(0u8).take(pad));
            }
        }
    }

    let sid = ctx.strings.intern_or_create(&buf);
    Ok(vec![TValue::from_string_id(sid)])
}

/// Get an integer argument, coercing from float or string if needed.
fn get_int_arg(ctx: &NativeContext, idx: usize, fname: &str) -> Result<i64, NativeError> {
    let val = ctx.args.get(idx).copied().unwrap_or(TValue::nil());
    if let Some(i) = val.as_full_integer(ctx.gc) {
        return Ok(i);
    }
    if let Some(f) = val.as_float() {
        // Check that it has an integer representation
        if f == (f as i64) as f64 {
            return Ok(f as i64);
        }
        return Err(NativeError::String(format!(
            "bad argument #{} to '{}' (number has no integer representation)",
            idx + 1,
            fname,
        )));
    }
    Err(NativeError::String(format!(
        "bad argument #{} to '{}' (number expected, got {})",
        idx + 1,
        fname,
        if val.is_nil() {
            "nil"
        } else if val.as_string_id().is_some() {
            "string"
        } else {
            "?"
        }
    )))
}

/// Get a number (float) argument.
fn get_number_arg(ctx: &NativeContext, idx: usize, fname: &str) -> Result<f64, NativeError> {
    let val = ctx.args.get(idx).copied().unwrap_or(TValue::nil());
    if let Some(f) = val.as_number(ctx.gc) {
        return Ok(f);
    }
    Err(NativeError::String(format!(
        "bad argument #{} to '{}' (number expected)",
        idx + 1,
        fname,
    )))
}

/// Get a string argument for pack, returning the bytes (cloned) and StringId.
fn get_string_arg_for_pack(
    ctx: &NativeContext,
    idx: usize,
    fname: &str,
) -> Result<(Vec<u8>, selune_core::string::StringId), NativeError> {
    let val = ctx.args.get(idx).copied().unwrap_or(TValue::nil());
    if let Some(sid) = val.as_string_id() {
        let bytes = ctx.strings.get_bytes(sid).to_vec();
        Ok((bytes, sid))
    } else {
        Err(NativeError::String(format!(
            "bad argument #{} to '{}' (string expected)",
            idx + 1,
            fname,
        )))
    }
}

/// string.unpack(fmt, s [, pos])
fn native_string_unpack(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let (fmt_bytes, _) = get_string_arg(ctx, 0, "unpack")?;
    let fmt = fmt_bytes.to_vec();
    let (data_bytes, _) = get_string_arg(ctx, 1, "unpack")?;
    let data = data_bytes.to_vec();

    // Optional start position (1-based, can be negative)
    let init = ctx
        .args
        .get(2)
        .and_then(|v| v.as_full_integer(ctx.gc))
        .unwrap_or(1);

    // Convert to 0-based index
    let start = if init >= 1 {
        (init as usize) - 1
    } else {
        // Negative index: relative to end
        let back = (-init) as usize;
        if back >= data.len() {
            0
        } else {
            data.len() - back
        }
    };

    if start > data.len() {
        return Err(NativeError::String(
            "initial position out of string".to_string(),
        ));
    }

    let mut results: Vec<TValue> = Vec::new();
    let mut endian = PackEndian::Little;
    let mut max_align: usize = 1;
    let mut offset = start; // 0-based byte offset into data
    let mut fpos = 0usize;

    while fpos < fmt.len() {
        let (opt, new_fpos) = parse_next_option(&fmt, fpos)?;
        fpos = new_fpos;

        match opt {
            PackOption::SetLittle => {
                endian = PackEndian::Little;
            }
            PackOption::SetBig => {
                endian = PackEndian::Big;
            }
            PackOption::SetNative => {
                endian = if cfg!(target_endian = "little") {
                    PackEndian::Little
                } else {
                    PackEndian::Big
                };
            }
            PackOption::SetAlign(n) => {
                max_align = n;
            }
            PackOption::Space => {}
            PackOption::IntSigned(n) => {
                let pad = alignment_padding(offset, n, max_align);
                offset += pad;
                if offset + n > data.len() {
                    return Err(NativeError::String(
                        "data string too short".to_string(),
                    ));
                }
                let val = unpack_int_signed_checked(&data[offset..], n, endian)?;
                results.push(TValue::from_full_integer(val, ctx.gc));
                offset += n;
            }
            PackOption::IntUnsigned(n) => {
                let pad = alignment_padding(offset, n, max_align);
                offset += pad;
                if offset + n > data.len() {
                    return Err(NativeError::String(
                        "data string too short".to_string(),
                    ));
                }
                let val = unpack_int_unsigned_checked(&data[offset..], n, endian)?;
                results.push(TValue::from_full_integer(val, ctx.gc));
                offset += n;
            }
            PackOption::Float => {
                let pad = alignment_padding(offset, PACK_SIZE_FLOAT, max_align);
                offset += pad;
                if offset + 4 > data.len() {
                    return Err(NativeError::String(
                        "data string too short".to_string(),
                    ));
                }
                let mut bytes = [0u8; 4];
                match endian {
                    PackEndian::Little => bytes.copy_from_slice(&data[offset..offset + 4]),
                    PackEndian::Big => {
                        for i in 0..4 {
                            bytes[i] = data[offset + 3 - i];
                        }
                    }
                }
                let f = f32::from_le_bytes(bytes) as f64;
                results.push(TValue::from_float(f));
                offset += 4;
            }
            PackOption::Double => {
                let pad = alignment_padding(offset, PACK_SIZE_DOUBLE, max_align);
                offset += pad;
                if offset + 8 > data.len() {
                    return Err(NativeError::String(
                        "data string too short".to_string(),
                    ));
                }
                let mut bytes = [0u8; 8];
                match endian {
                    PackEndian::Little => bytes.copy_from_slice(&data[offset..offset + 8]),
                    PackEndian::Big => {
                        for i in 0..8 {
                            bytes[i] = data[offset + 7 - i];
                        }
                    }
                }
                let f = f64::from_le_bytes(bytes);
                results.push(TValue::from_float(f));
                offset += 8;
            }
            PackOption::ZString => {
                // Find the next zero byte
                let zpos = data[offset..]
                    .iter()
                    .position(|&b| b == 0)
                    .ok_or_else(|| {
                        NativeError::String("unfinished string for format 'z'".to_string())
                    })?;
                let sid = ctx.strings.intern_or_create(&data[offset..offset + zpos]);
                results.push(TValue::from_string_id(sid));
                offset += zpos + 1; // skip the zero terminator
            }
            PackOption::SString(n) => {
                let pad = alignment_padding(offset, n, max_align);
                offset += pad;
                if offset + n > data.len() {
                    return Err(NativeError::String(
                        "data string too short".to_string(),
                    ));
                }
                // Read length as unsigned integer
                let len_val = unpack_int_unsigned_checked(&data[offset..], n, endian)?;
                let len = len_val as u64 as usize;
                offset += n;
                if offset + len > data.len() {
                    return Err(NativeError::String(
                        "data string too short".to_string(),
                    ));
                }
                let sid = ctx.strings.intern_or_create(&data[offset..offset + len]);
                results.push(TValue::from_string_id(sid));
                offset += len;
            }
            PackOption::CString(n) => {
                if offset + n > data.len() {
                    return Err(NativeError::String(
                        "data string too short".to_string(),
                    ));
                }
                let sid = ctx.strings.intern_or_create(&data[offset..offset + n]);
                results.push(TValue::from_string_id(sid));
                offset += n;
            }
            PackOption::Padding => {
                if offset + 1 > data.len() {
                    return Err(NativeError::String(
                        "data string too short".to_string(),
                    ));
                }
                offset += 1;
            }
            PackOption::AlignPad(align_to) => {
                let pad = alignment_padding(offset, align_to, max_align);
                offset += pad;
            }
        }
    }

    // Return all results plus the final position (1-based)
    results.push(TValue::from_full_integer((offset + 1) as i64, ctx.gc));
    Ok(results)
}

/// string.packsize(fmt)
fn native_string_packsize(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let (fmt_bytes, _) = get_string_arg(ctx, 0, "packsize")?;
    let fmt = fmt_bytes.to_vec();

    let mut total: u64 = 0;
    let mut max_align: usize = 1;
    let mut fpos = 0usize;

    while fpos < fmt.len() {
        let (opt, new_fpos) = parse_next_option(&fmt, fpos)?;
        fpos = new_fpos;

        match opt {
            PackOption::SetLittle | PackOption::SetBig | PackOption::SetNative => {}
            PackOption::SetAlign(n) => {
                max_align = n;
            }
            PackOption::Space => {}
            PackOption::IntSigned(n) | PackOption::IntUnsigned(n) => {
                let pad = alignment_padding(total as usize, n, max_align);
                total += pad as u64 + n as u64;
                if total > i32::MAX as u64 {
                    return Err(NativeError::String(
                        "format result too large".to_string(),
                    ));
                }
            }
            PackOption::Float => {
                let pad = alignment_padding(total as usize, PACK_SIZE_FLOAT, max_align);
                total += pad as u64 + PACK_SIZE_FLOAT as u64;
            }
            PackOption::Double => {
                let pad = alignment_padding(total as usize, PACK_SIZE_DOUBLE, max_align);
                total += pad as u64 + PACK_SIZE_DOUBLE as u64;
            }
            PackOption::ZString | PackOption::SString(_) => {
                return Err(NativeError::String(
                    "variable-length format".to_string(),
                ));
            }
            PackOption::CString(n) => {
                total += n as u64;
                if total > i32::MAX as u64 {
                    return Err(NativeError::String(
                        "format result too large".to_string(),
                    ));
                }
            }
            PackOption::Padding => {
                total += 1;
            }
            PackOption::AlignPad(align_to) => {
                let pad = alignment_padding(total as usize, align_to, max_align);
                total += pad as u64;
            }
        }
    }

    Ok(vec![TValue::from_full_integer(total as i64, ctx.gc)])
}

