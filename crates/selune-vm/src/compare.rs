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

    // int == float comparison
    if let (Some(i), Some(f)) = (a.as_full_integer(gc), b.as_float()) {
        return (i as f64 == f && (i as f64 as i64) == i, false);
    }
    if let (Some(f), Some(i)) = (a.as_float(), b.as_full_integer(gc)) {
        return (f == i as f64 && (i as f64 as i64) == i, false);
    }

    // string comparison
    if let (Some(sa), Some(sb)) = (a.as_string_id(), b.as_string_id()) {
        return (strings.get_bytes(sa) == strings.get_bytes(sb), false);
    }

    // Both tables (different identity) → might need __eq metamethod
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
pub fn lua_lt(
    a: TValue,
    b: TValue,
    gc: &GcHeap,
    strings: &StringInterner,
) -> CompareResult {
    // Both integers
    if let (Some(ia), Some(ib)) = (a.as_full_integer(gc), b.as_full_integer(gc)) {
        return CompareResult::Ok(ia < ib);
    }
    // Both floats
    if let (Some(fa), Some(fb)) = (a.as_float(), b.as_float()) {
        return CompareResult::Ok(fa < fb);
    }
    // Mixed int/float
    if let (Some(i), Some(f)) = (a.as_full_integer(gc), b.as_float()) {
        return CompareResult::Ok((i as f64) < f);
    }
    if let (Some(f), Some(i)) = (a.as_float(), b.as_full_integer(gc)) {
        return CompareResult::Ok(f < (i as f64));
    }
    // Both strings
    if let (Some(sa), Some(sb)) = (a.as_string_id(), b.as_string_id()) {
        return CompareResult::Ok(strings.get_bytes(sa) < strings.get_bytes(sb));
    }
    CompareResult::NeedMetamethod
}

/// Lua less-than-or-equal comparison.
pub fn lua_le(
    a: TValue,
    b: TValue,
    gc: &GcHeap,
    strings: &StringInterner,
) -> CompareResult {
    // Both integers
    if let (Some(ia), Some(ib)) = (a.as_full_integer(gc), b.as_full_integer(gc)) {
        return CompareResult::Ok(ia <= ib);
    }
    // Both floats
    if let (Some(fa), Some(fb)) = (a.as_float(), b.as_float()) {
        return CompareResult::Ok(fa <= fb);
    }
    // Mixed int/float
    if let (Some(i), Some(f)) = (a.as_full_integer(gc), b.as_float()) {
        return CompareResult::Ok((i as f64) <= f);
    }
    if let (Some(f), Some(i)) = (a.as_float(), b.as_full_integer(gc)) {
        return CompareResult::Ok(f <= (i as f64));
    }
    // Both strings
    if let (Some(sa), Some(sb)) = (a.as_string_id(), b.as_string_id()) {
        return CompareResult::Ok(strings.get_bytes(sa) <= strings.get_bytes(sb));
    }
    CompareResult::NeedMetamethod
}
