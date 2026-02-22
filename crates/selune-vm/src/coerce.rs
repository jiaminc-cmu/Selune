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
        } else if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
            i64::from_str_radix(hex, 16).ok().map(|i| i as f64)
        } else {
            None
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
        } else if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
            i64::from_str_radix(hex, 16).ok()
        } else if let Ok(f) = s.parse::<f64>() {
            float_to_integer(f)
        } else {
            None
        }
    } else {
        None
    }
}

/// Convert a float to integer if it has no fractional part.
pub fn float_to_integer(f: f64) -> Option<i64> {
    if f.is_finite() && f == (f as i64 as f64) {
        Some(f as i64)
    } else {
        None
    }
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
    if exp >= -4 && exp < 14 {
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
