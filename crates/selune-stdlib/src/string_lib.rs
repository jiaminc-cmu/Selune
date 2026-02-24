//! Lua 5.4 string library.

use crate::pattern::{self, CAP_POSITION};
use selune_core::gc::{GcHeap, GcIdx, NativeContext, NativeError, NativeFunction};
use selune_core::string::StringInterner;
use selune_core::table::Table;
use selune_core::value::TValue;

/// Result from string library registration.
pub struct StringLibIndices {
    pub gsub_idx: GcIdx<NativeFunction>,
    pub format_idx: GcIdx<NativeFunction>,
    pub dump_idx: GcIdx<NativeFunction>,
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
    register_fn(gc, string_table, strings, "find", native_string_find);
    register_fn(gc, string_table, strings, "match", native_string_match);
    register_fn(gc, string_table, strings, "gmatch", native_string_gmatch);
    register_fn(gc, string_table, strings, "pack", native_string_pack);
    register_fn(gc, string_table, strings, "unpack", native_string_unpack);
    register_fn(
        gc,
        string_table,
        strings,
        "packsize",
        native_string_packsize,
    );

    // string.format needs VM access for __tostring metamethod calls
    let format_idx = gc.alloc_native(native_string_format, "format");
    let format_val = TValue::from_native(format_idx);
    let format_name = strings.intern(b"format");
    gc.get_table_mut(string_table)
        .raw_set_str(format_name, format_val);

    // string.gsub needs VM access for function replacement
    let gsub_idx = gc.alloc_native(native_string_gsub_stub, "gsub");
    let gsub_val = TValue::from_native(gsub_idx);
    let gsub_name = strings.intern(b"gsub");
    gc.get_table_mut(string_table)
        .raw_set_str(gsub_name, gsub_val);

    // string.dump needs VM access for proto serialization
    let dump_idx = gc.alloc_native(native_string_dump_stub, "dump");
    let dump_val = TValue::from_native(dump_idx);
    let dump_name = strings.intern(b"dump");
    gc.get_table_mut(string_table)
        .raw_set_str(dump_name, dump_val);

    let name = strings.intern(b"string");
    gc.get_table_mut(env_idx)
        .raw_set_str(name, TValue::from_table(string_table));

    StringLibIndices {
        gsub_idx,
        format_idx,
        dump_idx,
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

/// Try to convert a value to string via __tostring metamethod or __name.
/// Used by string.format "%s" for tables/userdata without direct string conversion.
fn tostring_via_meta(val: TValue, ctx: &mut NativeContext) -> Result<Vec<u8>, NativeError> {
    // Check table metatable for __tostring
    let mt = if let Some(tbl_idx) = val.as_table_idx() {
        ctx.gc.get_table(tbl_idx).metatable
    } else if let Some(ud_idx) = val.as_userdata_idx() {
        ctx.gc.get_userdata(ud_idx).metatable
    } else {
        None
    };

    if let Some(mt_idx) = mt {
        let tostring_key = ctx.strings.intern(b"__tostring");
        let mm = ctx.gc.get_table(mt_idx).raw_get_str(tostring_key);
        if !mm.is_nil() {
            if let Some(native_idx) = mm.as_native_idx() {
                // Call native __tostring
                let native_fn = ctx.gc.get_native(native_idx).func;
                let args = [val];
                let mut sub_ctx = NativeContext {
                    args: &args,
                    gc: ctx.gc,
                    strings: ctx.strings,
                    upvalue: TValue::nil(),
                };
                let results =
                    native_fn(&mut sub_ctx).map_err(|e| NativeError::String(format!("{:?}", e)))?;
                if let Some(sid) = results.first().and_then(|v| v.as_string_id()) {
                    return Ok(ctx.strings.get_bytes(sid).to_vec());
                }
                return Err(NativeError::String(
                    "'__tostring' must return a string".to_string(),
                ));
            }
            if mm.as_closure_idx().is_some() {
                // Can't call Lua closures from native context; return opaque
                // representation. This will be handled properly when string.format
                // is VM-redirected.
            }
        }
        // Check __name for type name fallback
        let name_key = ctx.strings.intern(b"__name");
        let name_val = ctx.gc.get_table(mt_idx).raw_get_str(name_key);
        if let Some(sid) = name_val.as_string_id() {
            let name_bytes = ctx.strings.get_bytes(sid).to_vec();
            // Format as "typename: 0x..."
            let ptr = format!("0x{:014x}", val.raw_bits());
            let mut result = name_bytes;
            result.extend_from_slice(b": ");
            result.extend_from_slice(ptr.as_bytes());
            return Ok(result);
        }
    }
    // Default: "table: 0x..." or "userdata: 0x..."
    let type_name = if val.as_table_idx().is_some() {
        "table"
    } else if val.as_userdata_idx().is_some() {
        "userdata"
    } else {
        "?"
    };
    let ptr = format!("0x{:014x}", val.raw_bits());
    Ok(format!("{}: {}", type_name, ptr).into_bytes())
}

/// Format an unsigned integer with C-style format specifiers (%x, %X, %o, %u).
/// Handles width, zero-padding, left-align, '#' flag.
fn sprintf_int(fmt: &str, n: u64, spec: u8) -> String {
    let bytes = fmt.as_bytes();
    let mut i = 1; // skip '%'
    let mut left_align = false;
    let mut zero_pad = false;
    let mut alt_form = false;
    // Parse flags
    while i < bytes.len() {
        match bytes[i] {
            b'-' => {
                left_align = true;
                i += 1;
            }
            b'0' => {
                zero_pad = true;
                i += 1;
            }
            b'#' => {
                alt_form = true;
                i += 1;
            }
            b'+' | b' ' => {
                i += 1;
            } // ignore for unsigned
            _ => break,
        }
    }
    // Parse width
    let mut width = 0usize;
    while i < bytes.len() && bytes[i].is_ascii_digit() {
        width = width * 10 + (bytes[i] - b'0') as usize;
        i += 1;
    }
    // Parse precision
    let mut prec: Option<usize> = None;
    if i < bytes.len() && bytes[i] == b'.' {
        i += 1;
        let mut p = 0usize;
        while i < bytes.len() && bytes[i].is_ascii_digit() {
            p = p * 10 + (bytes[i] - b'0') as usize;
            i += 1;
        }
        prec = Some(p);
    }
    // Format the number
    let digits = match spec {
        b'x' => format!("{:x}", n),
        b'X' => format!("{:X}", n),
        b'o' => format!("{:o}", n),
        _ => format!("{}", n),
    };
    // Apply precision (minimum digits)
    let digits = if let Some(p) = prec {
        if p == 0 && n == 0 {
            String::new()
        } else if digits.len() < p {
            format!("{:0>width$}", digits, width = p)
        } else {
            digits
        }
    } else {
        digits
    };
    // Build prefix
    let prefix = if alt_form {
        match spec {
            b'x' => {
                if n != 0 {
                    "0x"
                } else {
                    ""
                }
            }
            b'X' => {
                if n != 0 {
                    "0X"
                } else {
                    ""
                }
            }
            b'o' => {
                if !digits.starts_with('0') && !digits.is_empty() {
                    "0"
                } else {
                    ""
                }
            }
            _ => "",
        }
    } else {
        ""
    };
    let content = format!("{}{}", prefix, digits);
    if content.len() >= width {
        content
    } else if left_align {
        format!("{:<width$}", content, width = width)
    } else if zero_pad && prec.is_none() {
        // Zero-pad between prefix and digits
        let pad_len = width - content.len();
        format!("{}{}{}", prefix, "0".repeat(pad_len), digits)
    } else {
        format!("{:>width$}", content, width = width)
    }
}

/// Format a signed integer with C-style format specifiers (%d, %i).
/// Handles width, zero-padding, left-align, '+', ' ' flags, and precision.
fn sprintf_signed(fmt: &str, n: i64) -> String {
    let bytes = fmt.as_bytes();
    let mut i = 1; // skip '%'
    let mut left_align = false;
    let mut zero_pad = false;
    let mut plus_flag = false;
    let mut space_flag = false;
    while i < bytes.len() {
        match bytes[i] {
            b'-' => {
                left_align = true;
                i += 1;
            }
            b'0' => {
                zero_pad = true;
                i += 1;
            }
            b'+' => {
                plus_flag = true;
                i += 1;
            }
            b' ' => {
                space_flag = true;
                i += 1;
            }
            b'#' => {
                i += 1;
            }
            _ => break,
        }
    }
    let mut width = 0usize;
    while i < bytes.len() && bytes[i].is_ascii_digit() {
        width = width * 10 + (bytes[i] - b'0') as usize;
        i += 1;
    }
    let mut prec: Option<usize> = None;
    if i < bytes.len() && bytes[i] == b'.' {
        i += 1;
        let mut p = 0usize;
        while i < bytes.len() && bytes[i].is_ascii_digit() {
            p = p * 10 + (bytes[i] - b'0') as usize;
            i += 1;
        }
        prec = Some(p);
    }
    let abs_n = if n == i64::MIN {
        format!("{}", n as u64) // handle overflow
    } else {
        format!("{}", n.unsigned_abs())
    };
    // Apply precision
    let digits = if let Some(p) = prec {
        if p == 0 && n == 0 {
            String::new()
        } else if abs_n.len() < p {
            format!("{:0>width$}", abs_n, width = p)
        } else {
            abs_n
        }
    } else {
        abs_n
    };
    // Build sign
    let sign = if n < 0 {
        "-"
    } else if plus_flag {
        "+"
    } else if space_flag {
        " "
    } else {
        ""
    };
    let content = format!("{}{}", sign, digits);
    if content.len() >= width {
        content
    } else if left_align {
        format!("{:<width$}", content, width = width)
    } else if zero_pad && prec.is_none() {
        // Zero-pad between sign and digits
        let pad_len = width - content.len();
        format!("{}{}{}", sign, "0".repeat(pad_len), digits)
    } else {
        format!("{:>width$}", content, width = width)
    }
}

/// Format a floating-point number in hexadecimal format (%a / %A).
/// Produces format like: [-]0x1.HHHHHHHHHHHHHp+EE
fn format_hex_float(
    f: f64,
    upper: bool,
    prec: Option<usize>,
    flags: &[u8],
    width_str: &str,
) -> String {
    let p_char = if upper { 'P' } else { 'p' };
    let x_char = if upper { 'X' } else { 'x' };
    let flag_plus = flags.contains(&b'+');
    let flag_space = flags.contains(&b' ');
    let flag_minus = flags.contains(&b'-');
    let flag_zero = flags.contains(&b'0');
    let w: usize = width_str.parse().unwrap_or(0);

    // Determine sign prefix
    let sign_prefix = |negative: bool| -> &'static str {
        if negative {
            "-"
        } else if flag_plus {
            "+"
        } else if flag_space {
            " "
        } else {
            ""
        }
    };

    if f.is_nan() {
        let core = if upper { "NAN" } else { "nan" };
        let s = format!("{}{}", sign_prefix(false), core);
        return pad_string(&s, w, flag_minus, false);
    }
    if f.is_infinite() {
        let neg = f < 0.0;
        let core = if upper { "INF" } else { "inf" };
        let s = format!("{}{}", sign_prefix(neg), core);
        return pad_string(&s, w, flag_minus, false);
    }

    let negative = f.is_sign_negative();
    let f_abs = f.abs();
    let sp = sign_prefix(negative);

    if f_abs == 0.0 {
        let core = match prec {
            Some(0) => format!("0{}0{}+0", x_char, p_char),
            Some(p) => format!("0{}0.{}{}+0", x_char, "0".repeat(p), p_char),
            None => format!("0{}0{}+0", x_char, p_char),
        };
        let s = format!("{}{}", sp, core);
        return pad_string(&s, w, flag_minus, flag_zero && !flag_minus);
    }

    let bits = f_abs.to_bits();
    let exp_raw = ((bits >> 52) & 0x7ff) as i64;
    let mantissa_bits = bits & 0x000fffffffffffff;

    let (exp, full_mantissa) = if exp_raw == 0 {
        // Denormalized number
        let mut m = mantissa_bits;
        let mut e: i64 = -1022;
        // Normalize: shift until we have a leading 1 in bit 52
        while m != 0 && (m & (1u64 << 52)) == 0 {
            m <<= 1;
            e -= 1;
        }
        (e, m & 0x000fffffffffffff)
    } else {
        (exp_raw - 1023, mantissa_bits)
    };

    let exp_str = if exp >= 0 {
        format!("+{}", exp)
    } else {
        format!("{}", exp)
    };

    // 52 mantissa bits = 13 hex digits
    let all_hex = if upper {
        format!("{:013X}", full_mantissa)
    } else {
        format!("{:013x}", full_mantissa)
    };

    let core = match prec {
        Some(0) => {
            format!("0{}1{}{}", x_char, p_char, exp_str)
        }
        Some(p) => {
            let hex = if p >= 13 {
                format!("{}{}", all_hex, "0".repeat(p - 13))
            } else {
                all_hex[..p].to_string()
            };
            format!("0{}1.{}{}{}", x_char, hex, p_char, exp_str)
        }
        None => {
            // Trim trailing zeros
            let hex = all_hex.trim_end_matches('0');
            if hex.is_empty() {
                format!("0{}1{}{}", x_char, p_char, exp_str)
            } else {
                format!("0{}1.{}{}{}", x_char, hex, p_char, exp_str)
            }
        }
    };

    let s = format!("{}{}", sp, core);
    pad_string(&s, w, flag_minus, flag_zero && !flag_minus)
}

fn pad_string(s: &str, width: usize, left_align: bool, zero_pad: bool) -> String {
    if s.len() >= width {
        return s.to_string();
    }
    let padding = width - s.len();
    if left_align {
        format!("{}{}", s, " ".repeat(padding))
    } else if zero_pad {
        // Insert zeros after sign and 0x prefix
        let mut prefix_len = 0;
        let bytes = s.as_bytes();
        if !bytes.is_empty() && (bytes[0] == b'+' || bytes[0] == b'-' || bytes[0] == b' ') {
            prefix_len = 1;
        }
        // Check for 0x/0X after sign
        if prefix_len + 1 < bytes.len()
            && bytes[prefix_len] == b'0'
            && (bytes[prefix_len + 1] == b'x' || bytes[prefix_len + 1] == b'X')
        {
            prefix_len += 2;
        }
        format!(
            "{}{}{}",
            &s[..prefix_len],
            "0".repeat(padding),
            &s[prefix_len..]
        )
    } else {
        format!("{}{}", " ".repeat(padding), s)
    }
}

/// Format a float with C-style flags, width, precision for %f/%e/%E/%g/%G.
fn sprintf_float(f: f64, spec: u8, flags: &[u8], width: &str, precision: &str) -> String {
    let flag_plus = flags.contains(&b'+');
    let flag_space = flags.contains(&b' ');
    let flag_minus = flags.contains(&b'-');
    let flag_zero = flags.contains(&b'0');
    let flag_hash = flags.contains(&b'#');
    let w: usize = width.parse().unwrap_or(0);
    let prec: usize = precision.parse().unwrap_or(6);

    // Generate the core number string without sign
    let abs_f = f.abs();
    let negative = f.is_sign_negative() && !f.is_nan();

    let core = match spec {
        b'f' => {
            let s = format!("{:.prec$}", abs_f, prec = prec);
            if flag_hash && prec == 0 && !s.contains('.') {
                format!("{}.", s)
            } else {
                s
            }
        }
        b'e' | b'E' => {
            let raw = if spec == b'e' {
                format!("{:.prec$e}", abs_f, prec = prec)
            } else {
                format!("{:.prec$E}", abs_f, prec = prec)
            };
            let s = fix_scientific_notation(&raw);
            if flag_hash && prec == 0 {
                // Insert '.' before 'e'/'E'
                if let Some(epos) = s.find(['e', 'E']) {
                    format!("{}.{}", &s[..epos], &s[epos..])
                } else {
                    s
                }
            } else {
                s
            }
        }
        b'g' | b'G' => {
            let gprec = if prec == 0 { 1 } else { prec };
            let sci = format!("{:.prec$e}", abs_f, prec = gprec.saturating_sub(1));
            let exp = sci
                .rfind('e')
                .and_then(|pos| sci[pos + 1..].parse::<i32>().ok())
                .unwrap_or(0);
            let s = if exp < -4 || exp >= gprec as i32 {
                let raw = if spec == b'G' {
                    format!("{:.prec$E}", abs_f, prec = gprec.saturating_sub(1))
                } else {
                    sci
                };
                fix_scientific_notation(&raw)
            } else {
                let decimal_places = if gprec as i32 > exp + 1 {
                    (gprec as i32 - exp - 1) as usize
                } else {
                    0
                };
                let s = format!("{:.prec$}", abs_f, prec = decimal_places);
                if spec == b'G' {
                    s.to_uppercase()
                } else {
                    s
                }
            };
            // Trim trailing zeros unless # flag
            if !flag_hash {
                if s.contains('.') {
                    s.trim_end_matches('0').trim_end_matches('.').to_string()
                } else {
                    s
                }
            } else {
                s
            }
        }
        _ => unreachable!(),
    };

    // Build sign prefix
    let sign = if negative {
        "-"
    } else if flag_plus {
        "+"
    } else if flag_space {
        " "
    } else {
        ""
    };

    let full = format!("{}{}", sign, core);
    if full.len() >= w {
        return full;
    }
    let padding = w - full.len();
    if flag_minus {
        format!("{}{}", full, " ".repeat(padding))
    } else if flag_zero {
        // Insert zeros after sign
        format!("{}{}{}", sign, "0".repeat(padding), core)
    } else {
        format!("{}{}", " ".repeat(padding), full)
    }
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
    let (sign, digits) = if let Some(stripped) = exp_part.strip_prefix('-') {
        ("-", stripped)
    } else if let Some(stripped) = exp_part.strip_prefix('+') {
        ("+", stripped)
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
            "bad argument #{} to '{}' (string expected, got {})",
            idx + 1,
            fname,
            type_name_of(val),
        )))
    }
}

/// Get string argument with number-to-string coercion (Lua 5.4 behavior).
/// Returns owned bytes since coerced strings are newly created.
/// Check an argument is an integer (luaL_checkinteger equivalent).
/// Tries float→int conversion. Errors with "number has no integer representation".
fn check_integer_arg(ctx: &mut NativeContext, idx: usize, fname: &str) -> Result<i64, NativeError> {
    let val = ctx.args.get(idx).copied().unwrap_or(TValue::nil());
    if let Some(i) = val.as_full_integer(ctx.gc) {
        return Ok(i);
    }
    if let Some(f) = val.as_float() {
        if f.is_finite() && f.floor() == f && f >= i64::MIN as f64 && f <= i64::MAX as f64 {
            return Ok(f as i64);
        }
        return Err(NativeError::String(format!(
            "bad argument #{} to '{}' (number has no integer representation)",
            idx + 1,
            fname,
        )));
    }
    // Try string coercion
    if let Some(sid) = val.as_string_id() {
        let s = std::str::from_utf8(ctx.strings.get_bytes(sid)).unwrap_or("");
        let s = s.trim();
        if let Ok(i) = s.parse::<i64>() {
            return Ok(i);
        }
        if let Ok(f) = s.parse::<f64>() {
            if f.is_finite() && f.floor() == f && f >= i64::MIN as f64 && f <= i64::MAX as f64 {
                return Ok(f as i64);
            }
            return Err(NativeError::String(format!(
                "bad argument #{} to '{}' (number has no integer representation)",
                idx + 1,
                fname,
            )));
        }
    }
    Err(NativeError::String(format!(
        "bad argument #{} to '{}' (number expected, got {})",
        idx + 1,
        fname,
        type_name_of(val),
    )))
}

/// Like check_integer_arg but returns a default if the argument is absent/nil.
fn opt_integer_arg(
    ctx: &mut NativeContext,
    idx: usize,
    fname: &str,
    default: i64,
) -> Result<i64, NativeError> {
    let val = ctx.args.get(idx).copied().unwrap_or(TValue::nil());
    if val.is_nil() {
        return Ok(default);
    }
    check_integer_arg(ctx, idx, fname)
}

fn get_string_arg_coerce(
    ctx: &mut NativeContext,
    idx: usize,
    fname: &str,
) -> Result<(Vec<u8>, selune_core::string::StringId), NativeError> {
    let val = ctx.args.get(idx).copied().unwrap_or(TValue::nil());
    if let Some(sid) = val.as_string_id() {
        let bytes = ctx.strings.get_bytes(sid).to_vec();
        return Ok((bytes, sid));
    }
    if let Some((bytes, sid)) = coerce_to_string(val, ctx) {
        return Ok((bytes, sid));
    }
    Err(NativeError::String(format!(
        "bad argument #{} to '{}' (string expected, got {})",
        idx + 1,
        fname,
        type_name_of(val),
    )))
}

/// Coerce a value to a string, returning owned bytes.
/// Handles strings directly and coerces numbers (int/float) to their string representation.
fn coerce_to_string(
    val: TValue,
    ctx: &mut NativeContext,
) -> Option<(Vec<u8>, selune_core::string::StringId)> {
    if let Some(sid) = val.as_string_id() {
        let bytes = ctx.strings.get_bytes(sid).to_vec();
        return Some((bytes, sid));
    }
    // Coerce integers
    if let Some(i) = val.as_integer() {
        let s = format!("{}", i);
        let sid = ctx.strings.intern(s.as_bytes());
        let bytes = ctx.strings.get_bytes(sid).to_vec();
        return Some((bytes, sid));
    }
    // Coerce floats
    if let Some(f) = val.as_float() {
        let s = format_float_lua(f);
        let sid = ctx.strings.intern(s.as_bytes());
        let bytes = ctx.strings.get_bytes(sid).to_vec();
        return Some((bytes, sid));
    }
    // Coerce boxed integers
    if let Some(i) = val.as_full_integer(ctx.gc) {
        let s = format!("{}", i);
        let sid = ctx.strings.intern(s.as_bytes());
        let bytes = ctx.strings.get_bytes(sid).to_vec();
        return Some((bytes, sid));
    }
    None
}

fn type_name_of(val: TValue) -> &'static str {
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
        "value"
    }
}

/// Format a float for Lua string coercion (matches %.14g behavior).
fn format_float_lua(f: f64) -> String {
    if f.is_nan() {
        return "-nan".to_string();
    }
    if f.is_infinite() {
        return if f.is_sign_positive() {
            "inf".to_string()
        } else {
            "-inf".to_string()
        };
    }
    // Use Lua-compatible %.14g formatting
    let s = format!("{}", f);
    // Ensure there's a decimal point to distinguish from integers
    if !s.contains('.') && !s.contains('e') && !s.contains('E') {
        format!("{}.0", s)
    } else {
        s
    }
}

/// Convert a Lua 1-based (possibly negative) index to a 0-based byte index.
#[allow(dead_code)]
fn lua_index(i: i64, len: usize) -> usize {
    if i >= 0 {
        let idx = (i as usize).saturating_sub(1);
        idx.min(len)
    } else {
        let back = (-i) as usize;
        len.saturating_sub(back)
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
        if neg > len {
            0
        } else {
            len - neg + 1
        }
    };
    // Lua 5.4 getendpos for end: 1-based
    let end_1 = if j > (len as i64) {
        len
    } else if j >= 0 {
        j as usize
    } else {
        let neg = j.unsigned_abs() as usize;
        if neg > len {
            0
        } else {
            len - neg + 1
        }
    };
    let start_1 = if start_1 < 1 { 1 } else { start_1 };

    let mut results = Vec::new();
    if start_1 <= end_1 {
        for &b in bytes.iter().take(end_1).skip(start_1 - 1) {
            results.push(TValue::from_integer(b as i64));
        }
    }
    Ok(results)
}

fn native_string_char(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let mut result = Vec::with_capacity(ctx.args.len());
    for (i, arg) in ctx.args.iter().enumerate() {
        let val = arg.as_full_integer(ctx.gc).ok_or_else(|| {
            NativeError::String(format!(
                "bad argument #{} to 'char' (number expected)",
                i + 1
            ))
        })?;
        if !(0..=255).contains(&val) {
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
    let (bytes, _) = get_string_arg_coerce(ctx, 0, "sub")?;
    let len = bytes.len();

    let i = check_integer_arg(ctx, 1, "sub")?;
    let j = opt_integer_arg(ctx, 2, "sub", -1)?;

    // Lua 5.4 posrelatI for start: 1-based, clamp to [0, len]
    let start_1 = if i > 0 {
        i as usize
    } else if i == 0 {
        1
    } else {
        // i < 0; use unsigned_abs to avoid overflow on i64::MIN
        let neg = i.unsigned_abs() as usize;
        if neg > len {
            0
        } else {
            len - neg + 1
        }
    };
    // Lua 5.4 getendpos for end: 1-based
    let end_1 = if j > (len as i64) {
        len
    } else if j >= 0 {
        j as usize
    } else {
        // j < 0; use unsigned_abs to avoid overflow on i64::MIN
        let neg = j.unsigned_abs() as usize;
        if neg > len {
            0
        } else {
            len - neg + 1
        }
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
    let n = match ctx.args.get(1) {
        Some(v) => {
            if let Some(i) = v.as_full_integer(ctx.gc) {
                i
            } else if let Some(f) = v.as_float() {
                // Coerce float to integer if it's a whole number
                if f == (f as i64 as f64) && f >= i64::MIN as f64 && f <= i64::MAX as f64 {
                    f as i64
                } else {
                    return Err(NativeError::String(
                        "bad argument #2 to 'rep' (number has no integer representation)"
                            .to_string(),
                    ));
                }
            } else {
                0
            }
        }
        None => 0,
    };

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
    let total_len = bytes
        .len()
        .saturating_mul(n)
        .saturating_add(sep.len().saturating_mul(n.saturating_sub(1)));
    // Lua 5.4 MAX_SIZE is essentially INT_MAX on most platforms
    const MAX_STR_SIZE: usize = 0x7FFF_FFFE; // 2^31 - 2 (Lua 5.4 MAX_SIZE)
    if total_len >= MAX_STR_SIZE {
        return Err(NativeError::String("string result too large".to_string()));
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
            let mut has_dot = false;
            if i < fmt.len() && fmt[i] == b'.' {
                has_dot = true;
                i += 1;
                while i < fmt.len() && fmt[i].is_ascii_digit() {
                    precision.push(fmt[i] as char);
                    i += 1;
                }
                // In C printf, "%.d" means "%.0d" - dot with no digits = precision 0
                if precision.is_empty() {
                    precision = "0".to_string();
                }
            }
            if i >= fmt.len() {
                break;
            }

            let spec = fmt[i];
            i += 1;

            // Calculate total format item length (from % to spec)
            let fmt_item_len =
                flags.len() + width.len() + if has_dot { 1 + precision.len() } else { 0 } + 1;

            // Check for "too long" format item (Lua 5.4 MAX_ITEM ~ 120)
            if fmt_item_len > 50 {
                return Err(NativeError::String("invalid format (too long)".to_string()));
            }

            // Validate width and precision limits (max 99 in Lua 5.4)
            let w_val: usize = width.parse().unwrap_or(0);
            let p_val: usize = precision.parse().unwrap_or(0);

            // Validate specifier-specific constraints
            match spec {
                b'd' | b'i' | b'u' | b'x' | b'X' | b'o' => {
                    // Integer specifiers: '#' only valid for x/X/o
                    if flags.contains(&b'#') && !matches!(spec, b'x' | b'X' | b'o') {
                        return Err(NativeError::String(format!(
                            "invalid conversion specification: '%{}'",
                            std::str::from_utf8(&[spec]).unwrap_or("?")
                        )));
                    }
                    if w_val > 99 || p_val > 99 {
                        return Err(NativeError::String(format!(
                            "invalid conversion specification: '%{}'",
                            std::str::from_utf8(&[spec]).unwrap_or("?")
                        )));
                    }
                }
                b'f' | b'e' | b'E' | b'g' | b'G' => {
                    if w_val > 99 || p_val > 99 {
                        return Err(NativeError::String(format!(
                            "invalid conversion specification: '%{}'",
                            std::str::from_utf8(&[spec]).unwrap_or("?")
                        )));
                    }
                }
                b'c' => {
                    // %c: no flags (except -), no zero-padding, no precision
                    if flags.contains(&b'0')
                        || has_dot
                        || flags.contains(&b'#')
                        || flags.contains(&b'+')
                        || flags.contains(&b' ')
                    {
                        return Err(NativeError::String(
                            "invalid conversion specification: '%c'".to_string(),
                        ));
                    }
                }
                b's' => {
                    // %s: '0' flag and '#' flag are invalid
                    if flags.contains(&b'0') || flags.contains(&b'#') {
                        return Err(NativeError::String(
                            "invalid conversion specification: '%s'".to_string(),
                        ));
                    }
                    if w_val > 99 || p_val > 99 {
                        return Err(NativeError::String(
                            "invalid conversion specification: '%s'".to_string(),
                        ));
                    }
                }
                b'p' => {
                    // %p allows width and '-' flag, but not precision or other modifiers
                    if has_dot {
                        return Err(NativeError::String(
                            "invalid conversion specification: '%p'".to_string(),
                        ));
                    }
                }
                b'q' => {
                    // Handled below (already has modifier check)
                }
                b'a' | b'A' => {
                    // hex float - allow modifiers
                }
                b'F' => {
                    // %F is not valid in Lua 5.4
                    return Err(NativeError::String(
                        "invalid conversion specification: '%F'".to_string(),
                    ));
                }
                _ => {
                    // Unknown specifier
                    return Err(NativeError::String(format!(
                        "invalid conversion specification: '%{}'",
                        if spec.is_ascii() {
                            String::from(spec as char)
                        } else {
                            format!("\\x{:02x}", spec)
                        }
                    )));
                }
            }

            // Check "no value" - not enough arguments
            if arg_idx >= ctx.args.len() {
                return Err(NativeError::String(format!(
                    "bad argument #{} to 'format' (no value)",
                    arg_idx + 1
                )));
            }

            let val = ctx.args.get(arg_idx).copied().unwrap_or(TValue::nil());
            arg_idx += 1;

            match spec {
                b'd' | b'i' => {
                    let n = if let Some(i) = val.as_full_integer(ctx.gc) {
                        i
                    } else if let Some(f) = val.as_float() {
                        f as i64
                    } else if let Some(sid) = val.as_string_id() {
                        let s = std::str::from_utf8(ctx.strings.get_bytes(sid)).unwrap_or("");
                        let s = s.trim();
                        s.parse::<i64>()
                            .or_else(|_| s.parse::<f64>().map(|f| f as i64))
                            .map_err(|_| {
                                NativeError::String(format!(
                                    "bad argument #{} to 'format' (number expected, got string)",
                                    arg_idx
                                ))
                            })?
                    } else {
                        return Err(NativeError::String(format!(
                            "bad argument #{} to 'format' (number has no integer representation)",
                            arg_idx
                        )));
                    };
                    let mut fmt = String::from("%");
                    for &f in &flags {
                        fmt.push(f as char);
                    }
                    fmt.push_str(&width);
                    if !precision.is_empty() {
                        fmt.push('.');
                        fmt.push_str(&precision);
                    }
                    fmt.push('d');
                    let formatted = sprintf_signed(&fmt, n);
                    result.extend_from_slice(formatted.as_bytes());
                }
                b'u' => {
                    let n = val
                        .as_full_integer(ctx.gc)
                        .or_else(|| val.as_float().map(|f| f as i64))
                        .unwrap_or(0) as u64;
                    let mut fmt = String::from("%");
                    for &f in &flags {
                        fmt.push(f as char);
                    }
                    fmt.push_str(&width);
                    if !precision.is_empty() {
                        fmt.push('.');
                        fmt.push_str(&precision);
                    }
                    fmt.push('u');
                    let formatted = sprintf_int(&fmt, n, b'u');
                    result.extend_from_slice(formatted.as_bytes());
                }
                b'f' | b'e' | b'E' | b'g' | b'G' => {
                    let f = val.as_number(ctx.gc).unwrap_or(0.0);
                    let formatted = sprintf_float(f, spec, &flags, &width, &precision);
                    result.extend_from_slice(formatted.as_bytes());
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
                        if b {
                            b"true".to_vec()
                        } else {
                            b"false".to_vec()
                        }
                    } else {
                        // Try __tostring metamethod for tables/userdata
                        tostring_via_meta(val, ctx)?
                    };
                    // When %s has modifiers (width/precision/flags), NUL bytes
                    // would cause C sprintf to truncate. Error like Lua 5.4.
                    let has_modifiers =
                        !width.is_empty() || !precision.is_empty() || !flags.is_empty();
                    if has_modifiers && s.contains(&0u8) {
                        return Err(NativeError::String("string contains zeros".to_string()));
                    }
                    if !precision.is_empty() {
                        let max_len: usize = precision.parse().unwrap_or(usize::MAX);
                        let truncated = &s[..s.len().min(max_len)];
                        let w: usize = width.parse().unwrap_or(0);
                        if flags.contains(&b'-') {
                            result.extend_from_slice(truncated);
                            if w > truncated.len() {
                                result.resize(result.len() + w - truncated.len(), b' ');
                            }
                        } else {
                            if w > truncated.len() {
                                result.resize(result.len() + w - truncated.len(), b' ');
                            }
                            result.extend_from_slice(truncated);
                        }
                    } else {
                        let w: usize = width.parse().unwrap_or(0);
                        if flags.contains(&b'-') {
                            result.extend_from_slice(&s);
                            if w > s.len() {
                                result.resize(result.len() + w - s.len(), b' ');
                            }
                        } else {
                            if w > s.len() {
                                result.resize(result.len() + w - s.len(), b' ');
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
                                b'\n' => {
                                    result.push(b'\\');
                                    result.push(b'\n');
                                }
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
                        // For negative numbers, the Lua parser treats them as
                        // -(positive_literal), so if the absolute value overflows
                        // i64 (i.e. n == i64::MIN), we must use hex format.
                        if n == i64::MIN {
                            result.extend_from_slice(format!("0x{:x}", n as u64).as_bytes());
                        } else {
                            result.extend_from_slice(format!("{}", n).as_bytes());
                        }
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
                        if b {
                            result.extend_from_slice(b"true");
                        } else {
                            result.extend_from_slice(b"false");
                        }
                    } else if val.is_nil() {
                        result.extend_from_slice(b"nil");
                    } else {
                        return Err(NativeError::String(
                            "no literal for non-basic type".to_string(),
                        ));
                    }
                }
                b'c' => {
                    let n = val.as_full_integer(ctx.gc).unwrap_or(0);
                    let ch = (n & 0xFF) as u8;
                    let w: usize = width.parse().unwrap_or(0);
                    if w <= 1 {
                        result.push(ch);
                    } else if flags.contains(&b'-') {
                        result.push(ch);
                        result.resize(result.len() + w - 1, b' ');
                    } else {
                        result.resize(result.len() + w - 1, b' ');
                        result.push(ch);
                    }
                }
                b'x' | b'X' | b'o' => {
                    let n = val
                        .as_full_integer(ctx.gc)
                        .or_else(|| val.as_float().map(|f| f as i64))
                        .unwrap_or(0);
                    // Build the C-style format string and delegate to sprintf_int
                    let mut fmt = String::from("%");
                    for &f in &flags {
                        fmt.push(f as char);
                    }
                    fmt.push_str(&width);
                    if !precision.is_empty() {
                        fmt.push('.');
                        fmt.push_str(&precision);
                    }
                    fmt.push(spec as char);
                    let formatted = sprintf_int(&fmt, n as u64, spec);
                    result.extend_from_slice(formatted.as_bytes());
                }
                b'p' => {
                    // %p: pointer format
                    // nil, booleans, numbers => "(null)"
                    // tables, functions, threads, userdata, strings => hex address
                    let ptr_str = if val.is_nil()
                        || val.as_bool().is_some()
                        || val.as_float().is_some()
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
                        if w > ptr_str.len() {
                            result.resize(result.len() + w - ptr_str.len(), b' ');
                        }
                    } else {
                        if w > ptr_str.len() {
                            result.resize(result.len() + w - ptr_str.len(), b' ');
                        }
                        result.extend_from_slice(ptr_str.as_bytes());
                    }
                }
                b'a' | b'A' => {
                    let f = val.as_number(ctx.gc).unwrap_or(0.0);
                    let prec: Option<usize> = if precision.is_empty() {
                        None
                    } else {
                        Some(precision.parse().unwrap_or(0))
                    };
                    let formatted = format_hex_float(f, spec == b'A', prec, &flags, &width);
                    result.extend_from_slice(formatted.as_bytes());
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
    let plain = ctx.args.get(3).map(|v| v.is_truthy()).unwrap_or(false);

    let start = if init >= 1 {
        (init as usize).saturating_sub(1)
    } else {
        let back = (-init) as usize;
        if back > subject.len() {
            0
        } else {
            subject.len() - back
        }
    };

    // If init position is past the end of the string + 1, return nil
    if start > subject.len() {
        return Ok(vec![TValue::nil()]);
    }

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
        Ok(Some(ms)) => {
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
        Ok(None) => Ok(vec![TValue::nil()]),
        Err(e) => Err(NativeError::String(e)),
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
        if back > subject.len() {
            0
        } else {
            subject.len() - back
        }
    };

    pattern::validate_pattern(&pat)
        .map_err(|e| NativeError::String(format!("bad argument #2 to 'match' ({e})")))?;

    match pattern::pattern_find(&subject, &pat, start) {
        Ok(Some(ms)) => {
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
        Ok(None) => Ok(vec![TValue::nil()]),
        Err(e) => Err(NativeError::String(e)),
    }
}

/// string.gmatch: returns an iterator function.
/// We store state in a table (subject, pattern, position) and return a native that reads it.
fn native_string_gmatch(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let (pat_bytes, pat_sid) = get_string_arg(ctx, 1, "gmatch")?;
    let pat_bytes = pat_bytes.to_vec();
    pattern::validate_pattern(&pat_bytes)
        .map_err(|e| NativeError::String(format!("bad argument #2 to 'gmatch' ({e})")))?;
    let (subj_bytes, subj_sid) = get_string_arg(ctx, 0, "gmatch")?;
    let subj_len = subj_bytes.len();

    // Handle optional init parameter (3rd arg, default 1)
    let init = ctx
        .args
        .get(2)
        .and_then(|v| v.as_full_integer(ctx.gc))
        .unwrap_or(1);
    let start_pos = if init >= 1 {
        init
    } else {
        // Negative index: count from end
        let back = (-init) as usize;
        if back > subj_len {
            1
        } else {
            (subj_len - back + 1) as i64
        }
    };

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
        .raw_seti(3, TValue::from_integer(start_pos)); // 1-based position

    // Return gmatch_iter with state stored as upvalue
    let state_val = TValue::from_table(state_table);
    let iter_idx = ctx
        .gc
        .alloc_native_with_upvalue(native_gmatch_iter, "gmatch_iter", state_val);
    let iter_val = TValue::from_native(iter_idx);
    Ok(vec![iter_val, state_val])
}

fn native_gmatch_iter(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    // State table is stored as upvalue (also passed as arg by generic-for, but upvalue is reliable)
    let state_val = if !ctx.upvalue.is_nil() {
        ctx.upvalue
    } else if !ctx.args.is_empty() {
        ctx.args[0]
    } else {
        return Err(NativeError::String(
            "gmatch: no state available".to_string(),
        ));
    };
    let state_idx = state_val
        .as_table_idx()
        .ok_or_else(|| NativeError::String("gmatch: invalid state".to_string()))?;

    let subj_sid = ctx
        .gc
        .get_table(state_idx)
        .raw_geti(1)
        .as_string_id()
        .ok_or_else(|| NativeError::String("gmatch: invalid subject".to_string()))?;
    let pat_sid = ctx
        .gc
        .get_table(state_idx)
        .raw_geti(2)
        .as_string_id()
        .ok_or_else(|| NativeError::String("gmatch: invalid pattern".to_string()))?;
    let pos = ctx
        .gc
        .get_table(state_idx)
        .raw_geti(3)
        .as_full_integer(ctx.gc)
        .unwrap_or(1);
    // lastmatch stored in slot 4 (0 = none, positive = 1-based position)
    let lastmatch_val = ctx
        .gc
        .get_table(state_idx)
        .raw_geti(4)
        .as_full_integer(ctx.gc)
        .unwrap_or(0);

    let subject = ctx.strings.get_bytes(subj_sid).to_vec();
    let pat = ctx.strings.get_bytes(pat_sid).to_vec();

    let mut src = if pos >= 1 { (pos as usize) - 1 } else { 0 };
    let lastmatch: Option<usize> = if lastmatch_val > 0 {
        Some((lastmatch_val - 1) as usize)
    } else {
        None
    };

    let anchor = !pat.is_empty() && pat[0] == b'^';
    let match_pat = if anchor { &pat[1..] } else { &pat };

    // Search forward from src, using lastmatch to avoid repeated empty matches
    loop {
        if src > subject.len() {
            return Ok(vec![TValue::nil()]);
        }

        // Try to match at position src
        let mut matcher = pattern::PatternMatcher::new(&subject, match_pat);
        let ms = matcher.try_match_at(src).map_err(NativeError::String)?;
        if let Some(ms) = ms {
            let (_match_start, match_end) = ms.captures[0];

            // Guard against repeated empty match at same position
            if match_end == src && lastmatch == Some(match_end) {
                // Skip: advance past this position
                if src < subject.len() {
                    src += 1;
                    if anchor {
                        return Ok(vec![TValue::nil()]);
                    }
                    continue;
                } else {
                    return Ok(vec![TValue::nil()]);
                }
            }

            // Update state: new pos (1-based) and lastmatch (1-based)
            let new_pos = TValue::from_full_integer((match_end + 1) as i64, ctx.gc);
            ctx.gc.get_table_mut(state_idx).raw_seti(3, new_pos);
            let new_lastmatch = TValue::from_full_integer((match_end + 1) as i64, ctx.gc);
            ctx.gc.get_table_mut(state_idx).raw_seti(4, new_lastmatch);

            if ms.captures.len() <= 1 {
                let slice = &subject[src..match_end];
                let sid = ctx.strings.intern_or_create(slice);
                return Ok(vec![TValue::from_string_id(sid)]);
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
                return Ok(results);
            }
        } else {
            // No match at src — advance
            if anchor || src >= subject.len() {
                return Ok(vec![TValue::nil()]);
            }
            src += 1;
        }
    }
}

/// Stub for string.gsub — actual dispatch happens in call_function
fn native_string_gsub_stub(_ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    Err(NativeError::String(
        "string.gsub stub should not be called directly".to_string(),
    ))
}

fn native_string_dump_stub(_ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    Err(NativeError::String(
        "string.dump stub should not be called directly".to_string(),
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
            if !(1..=PACK_MAX_INTSIZE).contains(&n) {
                return Err(NativeError::String(format!(
                    "integral size ({n}) out of limits [1,{PACK_MAX_INTSIZE}]"
                )));
            }
            Ok((PackOption::IntSigned(n), p))
        }
        b'I' => {
            let (n, p) = parse_fmt_int(fmt, next, PACK_NATIVE_INT)?;
            if !(1..=PACK_MAX_INTSIZE).contains(&n) {
                return Err(NativeError::String(format!(
                    "integral size ({n}) out of limits [1,{PACK_MAX_INTSIZE}]"
                )));
            }
            Ok((PackOption::IntUnsigned(n), p))
        }
        b's' => {
            let (n, p) = parse_fmt_int(fmt, next, PACK_SIZE_SIZE_T)?;
            if !(1..=PACK_MAX_INTSIZE).contains(&n) {
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
fn alignment_padding(
    offset: usize,
    natural_align: usize,
    max_align: usize,
) -> Result<usize, NativeError> {
    let align = natural_align.min(max_align);
    if align > 1 && !align.is_power_of_two() {
        return Err(NativeError::String(
            "format asks for alignment not power of 2".to_string(),
        ));
    }
    if align <= 1 {
        return Ok(0);
    }
    let remainder = offset % align;
    if remainder == 0 {
        Ok(0)
    } else {
        Ok(align - remainder)
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
            let sign_ext = if val < 0 { 0xFF } else { 0x00 };
            let copy_len = n.min(8);
            buf.extend_from_slice(&bytes[..copy_len]);
            for _ in copy_len..n {
                buf.push(sign_ext);
            }
        }
        PackEndian::Big => {
            // Write in big-endian order
            let sign_ext = if val < 0 { 0xFF } else { 0x00 };
            for i in (0..n).rev() {
                if i < 8 {
                    buf.push(bytes[i]);
                } else {
                    buf.push(sign_ext);
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
            let copy_len = n.min(8);
            buf.extend_from_slice(&bytes[..copy_len]);
            for _ in copy_len..n {
                buf.push(0x00);
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
        for b in le_bytes.iter_mut().take(8).skip(n) {
            *b = sign;
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
    let sign = if le_bytes[7] & 0x80 != 0 { 0xFF } else { 0x00 };
    for &b in le_bytes.iter().take(n).skip(8) {
        if b != sign {
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
    for &b in le_bytes.iter().take(n).skip(8) {
        if b != 0 {
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
                let pad = alignment_padding(buf.len(), n, max_align)?;
                buf.extend(std::iter::repeat(0u8).take(pad));
                let val = get_int_arg(ctx, arg_idx, "pack")?;
                arg_idx += 1;
                pack_int_signed(val, n, endian, &mut buf)?;
            }
            PackOption::IntUnsigned(n) => {
                let pad = alignment_padding(buf.len(), n, max_align)?;
                buf.extend(std::iter::repeat(0u8).take(pad));
                let val = get_int_arg(ctx, arg_idx, "pack")?;
                arg_idx += 1;
                pack_int_unsigned(val, n, endian, &mut buf)?;
            }
            PackOption::Float => {
                let pad = alignment_padding(buf.len(), PACK_SIZE_FLOAT, max_align)?;
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
                let pad = alignment_padding(buf.len(), PACK_SIZE_DOUBLE, max_align)?;
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
                    return Err(NativeError::String("string contains zeros".to_string()));
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
                        return Err(NativeError::String(
                            "string length does not fit in given size".to_string(),
                        ));
                    }
                }
                // Alignment for the length prefix
                let pad = alignment_padding(buf.len(), n, max_align)?;
                buf.extend(std::iter::repeat(0u8).take(pad));
                // Pack the length as an unsigned integer
                pack_int_unsigned(len as i64, n, endian, &mut buf)?;
                buf.extend_from_slice(&s);
            }
            PackOption::CString(n) => {
                let (s, _) = get_string_arg_for_pack(ctx, arg_idx, "pack")?;
                arg_idx += 1;
                if s.len() > n {
                    return Err(NativeError::String(
                        "string longer than given size".to_string(),
                    ));
                }
                buf.extend_from_slice(&s);
                // Pad with zeros if string is shorter
                buf.resize(buf.len() + n - s.len(), 0);
            }
            PackOption::Padding => {
                buf.push(0);
            }
            PackOption::AlignPad(align_to) => {
                let pad = alignment_padding(buf.len(), align_to, max_align)?;
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
                let pad = alignment_padding(offset, n, max_align)?;
                offset += pad;
                if offset + n > data.len() {
                    return Err(NativeError::String("data string too short".to_string()));
                }
                let val = unpack_int_signed_checked(&data[offset..], n, endian)?;
                results.push(TValue::from_full_integer(val, ctx.gc));
                offset += n;
            }
            PackOption::IntUnsigned(n) => {
                let pad = alignment_padding(offset, n, max_align)?;
                offset += pad;
                if offset + n > data.len() {
                    return Err(NativeError::String("data string too short".to_string()));
                }
                let val = unpack_int_unsigned_checked(&data[offset..], n, endian)?;
                results.push(TValue::from_full_integer(val, ctx.gc));
                offset += n;
            }
            PackOption::Float => {
                let pad = alignment_padding(offset, PACK_SIZE_FLOAT, max_align)?;
                offset += pad;
                if offset + 4 > data.len() {
                    return Err(NativeError::String("data string too short".to_string()));
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
                let pad = alignment_padding(offset, PACK_SIZE_DOUBLE, max_align)?;
                offset += pad;
                if offset + 8 > data.len() {
                    return Err(NativeError::String("data string too short".to_string()));
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
                let zpos = data[offset..].iter().position(|&b| b == 0).ok_or_else(|| {
                    NativeError::String("unfinished string for format 'z'".to_string())
                })?;
                let sid = ctx.strings.intern_or_create(&data[offset..offset + zpos]);
                results.push(TValue::from_string_id(sid));
                offset += zpos + 1; // skip the zero terminator
            }
            PackOption::SString(n) => {
                let pad = alignment_padding(offset, n, max_align)?;
                offset += pad;
                if offset + n > data.len() {
                    return Err(NativeError::String("data string too short".to_string()));
                }
                // Read length as unsigned integer
                let len_val = unpack_int_unsigned_checked(&data[offset..], n, endian)?;
                let len = len_val as u64 as usize;
                offset += n;
                if offset + len > data.len() {
                    return Err(NativeError::String("data string too short".to_string()));
                }
                let sid = ctx.strings.intern_or_create(&data[offset..offset + len]);
                results.push(TValue::from_string_id(sid));
                offset += len;
            }
            PackOption::CString(n) => {
                if offset + n > data.len() {
                    return Err(NativeError::String("data string too short".to_string()));
                }
                let sid = ctx.strings.intern_or_create(&data[offset..offset + n]);
                results.push(TValue::from_string_id(sid));
                offset += n;
            }
            PackOption::Padding => {
                if offset + 1 > data.len() {
                    return Err(NativeError::String("data string too short".to_string()));
                }
                offset += 1;
            }
            PackOption::AlignPad(align_to) => {
                let pad = alignment_padding(offset, align_to, max_align)?;
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
                let pad = alignment_padding(total as usize, n, max_align)?;
                total += pad as u64 + n as u64;
                if total > i32::MAX as u64 {
                    return Err(NativeError::String("format result too large".to_string()));
                }
            }
            PackOption::Float => {
                let pad = alignment_padding(total as usize, PACK_SIZE_FLOAT, max_align)?;
                total += pad as u64 + PACK_SIZE_FLOAT as u64;
            }
            PackOption::Double => {
                let pad = alignment_padding(total as usize, PACK_SIZE_DOUBLE, max_align)?;
                total += pad as u64 + PACK_SIZE_DOUBLE as u64;
            }
            PackOption::ZString | PackOption::SString(_) => {
                return Err(NativeError::String("variable-length format".to_string()));
            }
            PackOption::CString(n) => {
                total += n as u64;
                if total > i32::MAX as u64 {
                    return Err(NativeError::String("format result too large".to_string()));
                }
            }
            PackOption::Padding => {
                total += 1;
            }
            PackOption::AlignPad(align_to) => {
                let pad = alignment_padding(total as usize, align_to, max_align)?;
                total += pad as u64;
            }
        }
    }

    Ok(vec![TValue::from_full_integer(total as i64, ctx.gc)])
}
