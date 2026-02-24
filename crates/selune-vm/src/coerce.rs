//! Type coercion helpers for Lua 5.4 semantics.

use selune_core::gc::GcHeap;
use selune_core::string::{StringId, StringInterner};
use selune_core::value::TValue;

/// Try to convert a TValue to f64 (number coercion).
/// Integers convert to float; strings that look like numbers also convert.
pub fn to_number(v: TValue, gc: &GcHeap, strings: &StringInterner) -> Option<f64> {
    if let Some(f) = v.as_float() {
        Some(f)
    } else if let Some(i) = v.as_full_integer(gc) {
        Some(i as f64)
    } else if let Some(sid) = v.as_string_id() {
        let s = std::str::from_utf8(strings.get_bytes(sid)).ok()?;
        let s = s.trim();
        // Try parsing as float or integer
        if let Ok(f) = s.parse::<f64>() {
            Some(f)
        } else if let Some(result) = parse_hex_number(s) {
            Some(result as f64)
        } else {
            parse_hex_float(s)
        }
    } else {
        None
    }
}

/// Try to convert a TValue to i64 (integer coercion).
pub fn to_integer(v: TValue, gc: &GcHeap, strings: &StringInterner) -> Option<i64> {
    if let Some(i) = v.as_full_integer(gc) {
        Some(i)
    } else if let Some(f) = v.as_float() {
        float_to_integer(f)
    } else if let Some(sid) = v.as_string_id() {
        let s = std::str::from_utf8(strings.get_bytes(sid)).ok()?;
        let s = s.trim();
        // Try integer first, then hex
        if let Ok(i) = s.parse::<i64>() {
            Some(i)
        } else if let Some(i) = parse_hex_number(s) {
            Some(i)
        } else if let Ok(f) = s.parse::<f64>() {
            float_to_integer(f)
        } else {
            None
        }
    } else {
        None
    }
}

/// Convert a float to integer if it has no fractional part and fits in i64.
pub fn float_to_integer(f: f64) -> Option<i64> {
    if !f.is_finite() {
        return None;
    }
    // Check for fractional part
    if f.floor() != f {
        return None;
    }
    // Range check: f must be in [i64::MIN, i64::MAX].
    // i64::MIN (-2^63) is exactly representable as f64.
    // i64::MAX (2^63-1) is NOT exactly representable, but (i64::MAX as f64) rounds
    // up to 2^63. So we check f < 2^63 (which is i64::MIN as f64, negated)
    // and f >= i64::MIN as f64.
    const IMIN: f64 = i64::MIN as f64; // -9223372036854775808.0 (exact)
    const IMAX_P1: f64 = -(i64::MIN as f64); // 9223372036854775808.0 = 2^63 (exact)
    if !(IMIN..IMAX_P1).contains(&f) {
        return None;
    }
    // Safe to cast: f is integral and in [i64::MIN, i64::MAX]
    Some(f as i64)
}

/// Parse a hex number string, handling optional sign prefix.
/// Handles "0x...", "0X...", "-0x...", "-0X...", "+0x...", "+0X..."
/// Large hex integers wrap around (unsigned modulo 2^64), matching Lua 5.4 behavior.
fn parse_hex_number(s: &str) -> Option<i64> {
    let (neg, rest) = if let Some(r) = s.strip_prefix('-') {
        (true, r)
    } else if let Some(r) = s.strip_prefix('+') {
        (false, r)
    } else {
        (false, s)
    };
    let hex = rest
        .strip_prefix("0x")
        .or_else(|| rest.strip_prefix("0X"))?;
    if hex.is_empty() {
        return None;
    }
    // Also handle hex floats like 0x1.0p10 - parse as float
    if hex.contains('.') || hex.contains('p') || hex.contains('P') {
        let full = if neg {
            format!("-0x{}", hex)
        } else {
            format!("0x{}", hex)
        };
        return parse_hex_float(&full).and_then(float_to_integer);
    }
    // Parse hex digits with wrapping (Lua 5.4 wraps large hex integers)
    let mut val: u64 = 0;
    for c in hex.chars() {
        let digit = c.to_digit(16)? as u64;
        val = val.wrapping_mul(16).wrapping_add(digit);
    }
    let result = val as i64;
    if neg {
        Some(result.wrapping_neg())
    } else {
        Some(result)
    }
}

/// Convert a string to a TValue number (integer or float).
/// Handles hex integers (with wrapping), negative hex, decimal integers, and floats.
/// Used by both `tonumber(x)` and arithmetic coercion.
pub fn tonumber_from_str(s: &str, gc: &mut GcHeap) -> Option<TValue> {
    // Check if this looks like a hex number
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
        // Check if it's a hex float (has '.' or 'p'/'P')
        if trimmed.contains('.') || trimmed.contains('p') || trimmed.contains('P') {
            return parse_hex_float(trimmed).map(TValue::from_float);
        }
        // Hex integer (with wrapping on overflow)
        return parse_hex_number(trimmed).map(|i| TValue::from_full_integer(i, gc));
    }

    // Try decimal integer first
    if let Ok(i) = trimmed.parse::<i64>() {
        return Some(TValue::from_full_integer(i, gc));
    }

    // Try float (but reject "inf", "nan", "infinity" which Rust accepts but Lua doesn't)
    {
        let lower = trimmed.to_ascii_lowercase();
        let stripped = lower.trim_start_matches(['+', '-']);
        if !stripped.starts_with("inf") && !stripped.starts_with("nan") {
            if let Ok(f) = trimmed.parse::<f64>() {
                return Some(TValue::from_float(f));
            }
        }
    }

    None
}

/// Parse a hex float string like "0x1.8p1" = 3.0
/// Handles arbitrarily long mantissas by accumulating as f64 with a separate
/// base-2 exponent, avoiding u64 overflow.
fn parse_hex_float(s: &str) -> Option<f64> {
    let (neg, rest) = if let Some(r) = s.strip_prefix('-') {
        (true, r)
    } else if let Some(r) = s.strip_prefix('+') {
        (false, r)
    } else {
        (false, s)
    };
    let hex = rest
        .strip_prefix("0x")
        .or_else(|| rest.strip_prefix("0X"))?;

    // Split on 'p' or 'P' for exponent
    let (mantissa_str, exp) = if let Some(p_pos) = hex.find(['p', 'P']) {
        let exp: i64 = hex[p_pos + 1..].parse().ok()?;
        (&hex[..p_pos], exp)
    } else {
        (hex, 0i64)
    };

    // Parse mantissa (integer.fraction in hex)
    let (int_part, frac_part) = if let Some(dot_pos) = mantissa_str.find('.') {
        (&mantissa_str[..dot_pos], Some(&mantissa_str[dot_pos + 1..]))
    } else {
        (mantissa_str, None)
    };

    // Accumulate mantissa as f64 with a separate base-2 exponent to handle
    // arbitrarily long hex strings (e.g. 0xe03 followed by 1000 zeros).
    let mut value: f64 = 0.0;
    let mut bin_exp: i64 = exp; // total binary exponent

    // Integer part: each hex digit multiplies by 16 = 2^4
    for c in int_part.chars() {
        let digit = c.to_digit(16)? as f64;
        value = value * 16.0 + digit;
        // Renormalize to avoid infinity for very large mantissas
        if value > 1e18 {
            // Shift value down, increase exponent
            value *= 1.0 / (1u64 << 52) as f64;
            bin_exp += 52;
        }
    }

    // Fractional part: each hex digit has weight 16^(-position) = 2^(-4*position)
    // We accumulate fractional digits into value and adjust bin_exp to compensate.
    if let Some(frac) = frac_part {
        for c in frac.chars() {
            let digit = c.to_digit(16)? as f64;
            value = value * 16.0 + digit;
            bin_exp -= 4; // compensate: multiplying by 16 = adding 4 to bin_exp
                          // Renormalize to avoid infinity
            if value > 1e18 {
                value *= 1.0 / (1u64 << 52) as f64;
                bin_exp += 52;
            }
        }
    }

    // Apply binary exponent using ldexp-style computation
    // Split into manageable chunks since powi only takes i32
    while bin_exp > 1023 {
        value *= (2.0f64).powi(1023);
        bin_exp -= 1023;
    }
    while bin_exp < -1023 {
        value *= (2.0f64).powi(-1023);
        bin_exp += 1023;
    }
    value *= (2.0f64).powi(bin_exp as i32);

    if neg {
        value = -value;
    }
    Some(value)
}

/// Convert a value to string for concatenation.
pub fn to_string_for_concat(
    v: TValue,
    gc: &GcHeap,
    strings: &mut StringInterner,
) -> Option<StringId> {
    if let Some(sid) = v.as_string_id() {
        Some(sid)
    } else if let Some(i) = v.as_full_integer(gc) {
        let s = format!("{i}");
        Some(strings.intern_or_create(s.as_bytes()))
    } else if let Some(f) = v.as_float() {
        let s = lua_format_float(f);
        Some(strings.intern_or_create(s.as_bytes()))
    } else {
        None
    }
}

/// Format a float using Lua's %.14g-like format.
pub fn lua_format_float(f: f64) -> String {
    if f.is_nan() {
        return "-nan".to_string();
    }
    if f.is_infinite() {
        return if f > 0.0 {
            "inf".to_string()
        } else {
            "-inf".to_string()
        };
    }
    // Use %.14g equivalent formatting
    format_g14(f)
}

/// Produce output equivalent to C's `%.14g` for a finite float.
fn format_g14(f: f64) -> String {
    if f == 0.0 {
        return if f.is_sign_negative() {
            "-0.0".to_string()
        } else {
            "0.0".to_string()
        };
    }
    // %.14g: use fixed notation if exponent is in [-4, 14), else scientific
    let abs = f.abs();
    let exp = abs.log10().floor() as i32;
    if (-4..14).contains(&exp) {
        // Fixed notation: 14 significant digits
        let decimals = (13 - exp).max(0) as usize;
        let mut s = format!("{:.*}", decimals, f);
        // Remove trailing zeros after decimal point, but keep at least ".0"
        if s.contains('.') {
            let trimmed = s.trim_end_matches('0');
            if trimmed.ends_with('.') {
                s = format!("{}0", trimmed);
            } else {
                s = trimmed.to_string();
            }
        }
        s
    } else {
        // Scientific notation
        let mut s = format!("{:.13e}", f);
        // Rust formats exponent without + sign and variable width
        // C printf uses e+XX format. Fix it.
        s = fix_scientific_notation_g14(&s);
        // Remove trailing zeros in mantissa
        if let Some(e_pos) = s.find('e') {
            let mantissa = &s[..e_pos];
            let exponent = &s[e_pos..];
            let trimmed = if mantissa.contains('.') {
                let t = mantissa.trim_end_matches('0');
                if t.ends_with('.') {
                    format!("{}0", t)
                } else {
                    t.to_string()
                }
            } else {
                mantissa.to_string()
            };
            s = format!("{}{}", trimmed, exponent);
        }
        s
    }
}

/// Fix Rust scientific notation to match C printf format (e+XX).
fn fix_scientific_notation_g14(s: &str) -> String {
    // Rust produces "1.23e5" or "1.23e-5", C produces "1.23e+05" or "1.23e-05"
    if let Some(e_pos) = s.find('e') {
        let mantissa = &s[..e_pos];
        let exp_str = &s[e_pos + 1..];
        let (sign, digits) = if let Some(rest) = exp_str.strip_prefix('-') {
            ("-", rest)
        } else if let Some(rest) = exp_str.strip_prefix('+') {
            ("+", rest)
        } else {
            ("+", exp_str)
        };
        let exp_num: i32 = digits.parse().unwrap_or(0);
        format!("{}e{}{:02}", mantissa, sign, exp_num.abs())
    } else {
        s.to_string()
    }
}
