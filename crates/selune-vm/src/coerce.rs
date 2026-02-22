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
    if f == 0.0 && f.is_sign_positive() {
        return "0".to_string();
    }
    // Use Rust's default float formatting which is similar to %g
    // Try integer representation first if it's a whole number
    if f.fract() == 0.0 && f.abs() < 1e15 {
        format!("{}", f as i64)
    } else {
        format!("{}", f)
    }
}
