//! Comparison operations with Lua 5.4 semantics.

use selune_core::gc::GcHeap;
use selune_core::string::StringInterner;
use selune_core::value::TValue;

/// Lua equality: numbers compare by value (int==float if same value),
/// strings compare by content, other GC objects compare by identity.
/// Returns (equal, needs_metamethod). If both operands are same-type GC objects
/// (tables/closures) and not raw-equal, needs_metamethod=true.
pub fn lua_eq(a: TValue, b: TValue, gc: &GcHeap, strings: &StringInterner) -> (bool, bool) {
    // Same bits = equal (except NaN)
    if a.raw_bits() == b.raw_bits() {
        // NaN != NaN
        if a.is_float() {
            if let Some(f) = a.as_float() {
                return (!f.is_nan(), false);
            }
        }
        return (true, false);
    }

    // float == float comparison (handles -0.0 == 0.0 which have different bits)
    if let (Some(fa), Some(fb)) = (a.as_float(), b.as_float()) {
        return (fa == fb, false);
    }

    // int == int comparison (handles boxed ints with different GcIdx but same value)
    if let (Some(ia), Some(ib)) = (a.as_full_integer(gc), b.as_full_integer(gc)) {
        return (ia == ib, false);
    }

    // int == float comparison (precision-safe)
    if let (Some(i), Some(f)) = (a.as_full_integer(gc), b.as_float()) {
        return (eq_int_float(i, f), false);
    }
    if let (Some(f), Some(i)) = (a.as_float(), b.as_full_integer(gc)) {
        return (eq_int_float(i, f), false);
    }

    // string comparison
    if let (Some(sa), Some(sb)) = (a.as_string_id(), b.as_string_id()) {
        return (strings.get_bytes(sa) == strings.get_bytes(sb), false);
    }

    // Both tables (different identity) -> might need __eq metamethod
    if a.as_table_idx().is_some() && b.as_table_idx().is_some() {
        return (false, true);
    }

    (false, false)
}

/// Result of comparison that may need metamethod.
pub enum CompareResult {
    Ok(bool),
    NeedMetamethod,
}

/// Lua less-than comparison.
pub fn lua_lt(a: TValue, b: TValue, gc: &GcHeap, strings: &StringInterner) -> CompareResult {
    // Both integers
    if let (Some(ia), Some(ib)) = (a.as_full_integer(gc), b.as_full_integer(gc)) {
        return CompareResult::Ok(ia < ib);
    }
    // Both floats
    if let (Some(fa), Some(fb)) = (a.as_float(), b.as_float()) {
        return CompareResult::Ok(fa < fb);
    }
    // Mixed int/float (precision-safe)
    if let (Some(i), Some(f)) = (a.as_full_integer(gc), b.as_float()) {
        return CompareResult::Ok(lt_int_float(i, f));
    }
    if let (Some(f), Some(i)) = (a.as_float(), b.as_full_integer(gc)) {
        return CompareResult::Ok(lt_float_int(f, i));
    }
    // Both strings
    if let (Some(sa), Some(sb)) = (a.as_string_id(), b.as_string_id()) {
        return CompareResult::Ok(strings.get_bytes(sa) < strings.get_bytes(sb));
    }
    CompareResult::NeedMetamethod
}

/// Lua less-than-or-equal comparison.
pub fn lua_le(a: TValue, b: TValue, gc: &GcHeap, strings: &StringInterner) -> CompareResult {
    // Both integers
    if let (Some(ia), Some(ib)) = (a.as_full_integer(gc), b.as_full_integer(gc)) {
        return CompareResult::Ok(ia <= ib);
    }
    // Both floats
    if let (Some(fa), Some(fb)) = (a.as_float(), b.as_float()) {
        return CompareResult::Ok(fa <= fb);
    }
    // Mixed int/float (precision-safe)
    if let (Some(i), Some(f)) = (a.as_full_integer(gc), b.as_float()) {
        return CompareResult::Ok(le_int_float(i, f));
    }
    if let (Some(f), Some(i)) = (a.as_float(), b.as_full_integer(gc)) {
        return CompareResult::Ok(le_float_int(f, i));
    }
    // Both strings
    if let (Some(sa), Some(sb)) = (a.as_string_id(), b.as_string_id()) {
        return CompareResult::Ok(strings.get_bytes(sa) <= strings.get_bytes(sb));
    }
    CompareResult::NeedMetamethod
}

// ---------------------------------------------------------------------------
// Precision-safe integer/float comparisons (mirrors Lua 5.4 lvm.c)
// ---------------------------------------------------------------------------
// Casting i64 to f64 can lose precision for large values (|i| > 2^53).
// These helpers avoid that by comparing the float against integer boundaries
// and using floor/ceil to handle the fractional part.

/// i64::MIN as f64 (exact: -2^63 is representable)
const IMIN_F: f64 = i64::MIN as f64;   // -9223372036854775808.0
/// (i64::MAX + 1) as f64 (exact: 2^63 is representable)
const IMAX_P1_F: f64 = (i64::MAX as f64) + 1.0;  // 9223372036854775808.0

/// Precision-safe: integer == float
fn eq_int_float(i: i64, f: f64) -> bool {
    // If f is NaN, not equal
    if f.is_nan() {
        return false;
    }
    // If f has a fractional part, it can't equal an integer
    if f.floor() != f {
        return false;
    }
    // If f is outside i64 range, can't be equal
    if f < IMIN_F || f >= IMAX_P1_F {
        return false;
    }
    // f is integral and in range, safe to cast to i64
    i == (f as i64)
}

/// Precision-safe: integer < float
fn lt_int_float(i: i64, f: f64) -> bool {
    // NaN: always false
    if f.is_nan() {
        return false;
    }
    // f >= 2^63: any i64 < f
    if f >= IMAX_P1_F {
        return true;
    }
    // f < -2^63: no i64 < f
    if f < IMIN_F {
        return false;
    }
    // f is in i64 range. Compare i < floor(f) or (i <= floor(f) if f has fraction)
    // If f has fractional part: i < f iff i <= floor(f) (since f = floor(f) + frac)
    // If f is integral: i < f iff i < (f as i64)
    let fi = f.floor() as i64;
    if f.floor() != f {
        // f has fractional part: i < f iff i <= floor(f)
        i <= fi
    } else {
        i < fi
    }
}

/// Precision-safe: float < integer
fn lt_float_int(f: f64, i: i64) -> bool {
    // NaN: always false
    if f.is_nan() {
        return false;
    }
    // f >= 2^63: no way f < any i64
    if f >= IMAX_P1_F {
        return false;
    }
    // f < -2^63: f < any i64
    if f < IMIN_F {
        return true;
    }
    // f is in i64 range. f < i iff ceil(f) < i or (floor(f) < i if f is integral)
    // If f has fractional part: f < i iff ceil(f) <= i (since f < ceil(f))
    //   but more simply: f < i iff floor(f) < i
    // If f is integral: f < i iff (f as i64) < i
    let fi = f.floor() as i64;
    if f.floor() != f {
        // f has fractional part: floor(f) < f < floor(f)+1, so f < i iff floor(f) < i
        fi < i
    } else {
        fi < i
    }
}

/// Precision-safe: integer <= float
fn le_int_float(i: i64, f: f64) -> bool {
    // NaN: always false
    if f.is_nan() {
        return false;
    }
    // For non-NaN: i <= f iff !(f < i)
    !lt_float_int(f, i)
}

/// Precision-safe: float <= integer
fn le_float_int(f: f64, i: i64) -> bool {
    // NaN: always false
    if f.is_nan() {
        return false;
    }
    // For non-NaN: f <= i iff !(i < f)
    !lt_int_float(i, f)
}
