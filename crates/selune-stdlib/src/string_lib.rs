//! Lua 5.4 string library.

use crate::pattern::{self, CAP_POSITION};
use selune_core::gc::{GcHeap, GcIdx, NativeContext, NativeError, NativeFunction};
use selune_core::string::StringInterner;
use selune_core::table::Table;
use selune_core::value::TValue;

/// Register the string library into _ENV.
/// Returns the GcIdx of string.gsub for special VM dispatch.
pub fn register(
    env_idx: GcIdx<Table>,
    gc: &mut GcHeap,
    strings: &mut StringInterner,
) -> GcIdx<NativeFunction> {
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

    // string.gsub needs VM access for function replacement
    let gsub_idx = gc.alloc_native(native_string_gsub_stub, "gsub");
    let gsub_val = TValue::from_native(gsub_idx);
    let gsub_name = strings.intern(b"gsub");
    gc.get_table_mut(string_table).raw_set_str(gsub_name, gsub_val);

    let name = strings.intern(b"string");
    gc.get_table_mut(env_idx)
        .raw_set_str(name, TValue::from_table(string_table));

    gsub_idx
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

    let start = lua_index(i, len);
    let end = if j >= 0 { (j as usize).min(len) } else { lua_index(j, len) + 1 };

    let mut results = Vec::new();
    for idx in start..end {
        results.push(TValue::from_integer(bytes[idx] as i64));
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

    let start = lua_index(i, len);
    let end = if j >= 0 {
        (j as usize).min(len)
    } else {
        lua_index(j, len) + 1
    };

    if start >= end {
        let sid = ctx.strings.intern(b"");
        return Ok(vec![TValue::from_string_id(sid)]);
    }

    let slice = &bytes[start..end];
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
    let mut result = Vec::with_capacity(bytes.len() * n + sep.len() * n.saturating_sub(1));
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
                    // Quoted string
                    let s = if let Some(sid) = val.as_string_id() {
                        ctx.strings.get_bytes(sid).to_vec()
                    } else {
                        b"".to_vec()
                    };
                    result.push(b'"');
                    for &b in &s {
                        match b {
                            b'\\' => result.extend_from_slice(b"\\\\"),
                            b'"' => result.extend_from_slice(b"\\\""),
                            b'\n' => result.extend_from_slice(b"\\n"),
                            b'\r' => result.extend_from_slice(b"\\r"),
                            b'\0' => result.extend_from_slice(b"\\0"),
                            _ => result.push(b),
                        }
                    }
                    result.push(b'"');
                    arg_idx -= 0; // q consumes argument already
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

