//! Arithmetic operations with Lua 5.4 semantics.

use crate::coerce;
use crate::error::LuaError;
use selune_core::gc::GcHeap;
use selune_core::string::StringInterner;
use selune_core::value::TValue;

/// Result of an arithmetic operation that may need a metamethod fallback.
pub enum ArithResult {
    /// Operation succeeded with this value.
    Ok(TValue),
    /// Type mismatch — caller should try metamethod (MMBin).
    NeedMetamethod,
    /// Actual error (e.g. division by zero) — propagate.
    Error(LuaError),
}

/// Perform a binary arithmetic operation.
/// Returns `ArithResult::NeedMetamethod` on type mismatch instead of erroring.
pub fn arith_op(
    op: ArithOp,
    a: TValue,
    b: TValue,
    gc: &mut GcHeap,
    strings: &StringInterner,
) -> ArithResult {
    // Fast path: both integers (except Div and Pow which always produce float)
    if !matches!(op, ArithOp::Div | ArithOp::Pow) {
        if let (Some(ia), Some(ib)) = (a.as_full_integer(gc), b.as_full_integer(gc)) {
            return match int_arith(op, ia, ib, gc) {
                Ok(v) => ArithResult::Ok(v),
                Err(e) => ArithResult::Error(e),
            };
        }

        // String→integer coercion path: if both operands can be coerced to integers,
        // use integer arithmetic (Lua 5.4 semantics: "10" + 5 = 15 as integer)
        let ia = coerce::to_integer(a, gc, strings);
        let ib = coerce::to_integer(b, gc, strings);
        if let (Some(ia), Some(ib)) = (ia, ib) {
            // Only use integer path if at least one operand was a string
            // (if both were already integers, the fast path above would have caught it)
            if a.as_string_id().is_some() || b.as_string_id().is_some() {
                return match int_arith(op, ia, ib, gc) {
                    Ok(v) => ArithResult::Ok(v),
                    Err(e) => ArithResult::Error(e),
                };
            }
        }
    }

    // Float path: try to convert both to numbers
    let fa = coerce::to_number(a, gc, strings);
    let fb = coerce::to_number(b, gc, strings);

    match (fa, fb) {
        (Some(fa), Some(fb)) => match float_arith(op, fa, fb) {
            Ok(result) => ArithResult::Ok(TValue::from_float(result)),
            Err(e) => ArithResult::Error(e),
        },
        _ => ArithResult::NeedMetamethod,
    }
}

/// Integer arithmetic, returning integer result.
fn int_arith(op: ArithOp, a: i64, b: i64, gc: &mut GcHeap) -> Result<TValue, LuaError> {
    let result = match op {
        ArithOp::Add => a.wrapping_add(b),
        ArithOp::Sub => a.wrapping_sub(b),
        ArithOp::Mul => a.wrapping_mul(b),
        ArithOp::IDiv => {
            if b == 0 {
                return Err(LuaError::Runtime("attempt to divide by zero".to_string()));
            }
            lua_idiv(a, b)
        }
        ArithOp::Mod => {
            if b == 0 {
                return Err(LuaError::Runtime("attempt to perform 'n%0'".to_string()));
            }
            lua_imod(a, b)
        }
        ArithOp::BAnd => a & b,
        ArithOp::BOr => a | b,
        ArithOp::BXor => a ^ b,
        ArithOp::Shl => lua_shl(a, b),
        ArithOp::Shr => lua_shr(a, b),
        ArithOp::Pow => {
            // Pow always returns float
            let result = (a as f64).powf(b as f64);
            return Ok(TValue::from_float(result));
        }
        ArithOp::Div => unreachable!("Div handled in float path"),
    };
    Ok(TValue::from_full_integer(result, gc))
}

/// Float arithmetic.
fn float_arith(op: ArithOp, a: f64, b: f64) -> Result<f64, LuaError> {
    Ok(match op {
        ArithOp::Add => a + b,
        ArithOp::Sub => a - b,
        ArithOp::Mul => a * b,
        ArithOp::Div => a / b,
        ArithOp::Pow => a.powf(b),
        ArithOp::IDiv => {
            // Float floor division by zero follows IEEE 754:
            // produces inf, -inf, or NaN (only integer idiv errors on zero)
            (a / b).floor()
        }
        ArithOp::Mod => {
            // Float modulo by zero follows IEEE 754:
            // produces NaN (only integer mod errors on zero)
            lua_fmod(a, b)
        }
        ArithOp::BAnd | ArithOp::BOr | ArithOp::BXor | ArithOp::Shl | ArithOp::Shr => {
            return Err(LuaError::Runtime(
                "number has no integer representation".to_string(),
            ));
        }
    })
}

/// Lua integer division (floor division).
fn lua_idiv(a: i64, b: i64) -> i64 {
    // Use wrapping_div to handle i64::MIN / -1 overflow (produces i64::MIN in Lua)
    let d = a.wrapping_div(b);
    let r = a.wrapping_rem(b);
    // If signs differ and there's a remainder, round towards negative infinity
    if r != 0 && (r ^ b) < 0 {
        d - 1
    } else {
        d
    }
}

/// Lua integer modulo.
fn lua_imod(a: i64, b: i64) -> i64 {
    let r = a.wrapping_rem(b);
    if r != 0 && (r ^ b) < 0 {
        r.wrapping_add(b)
    } else {
        r
    }
}

/// Lua float modulo: a % b = a - floor(a/b)*b
/// Uses sign comparison instead of r*b to avoid underflow with very small numbers.
fn lua_fmod(a: f64, b: f64) -> f64 {
    let r = a % b;  // IEEE 754 fmod (truncated remainder)
    if r != 0.0 && ((r > 0.0) != (b > 0.0)) {
        r + b
    } else {
        r
    }
}

/// Lua left shift.
fn lua_shl(a: i64, b: i64) -> i64 {
    if b >= 64 || b <= -64 {
        0
    } else if b < 0 {
        lua_shr(a, -b)
    } else {
        (a as u64).wrapping_shl(b as u32) as i64
    }
}

/// Lua right shift (unsigned).
fn lua_shr(a: i64, b: i64) -> i64 {
    if b >= 64 || b <= -64 {
        0
    } else if b < 0 {
        lua_shl(a, -b)
    } else {
        (a as u64).wrapping_shr(b as u32) as i64
    }
}

/// Unary minus. Returns NeedMetamethod on type mismatch.
pub fn arith_unm(v: TValue, gc: &mut GcHeap, strings: &StringInterner) -> ArithResult {
    if let Some(i) = v.as_full_integer(gc) {
        ArithResult::Ok(TValue::from_full_integer(i.wrapping_neg(), gc))
    } else if let Some(f) = v.as_float() {
        ArithResult::Ok(TValue::from_float(-f))
    } else if let Some(f) = coerce::to_number(v, gc, strings) {
        ArithResult::Ok(TValue::from_float(-f))
    } else {
        ArithResult::NeedMetamethod
    }
}

/// Bitwise NOT. Returns NeedMetamethod on type mismatch.
pub fn arith_bnot(v: TValue, gc: &mut GcHeap, strings: &StringInterner) -> ArithResult {
    if let Some(i) = v.as_full_integer(gc) {
        ArithResult::Ok(TValue::from_full_integer(!i, gc))
    } else if let Some(i) = coerce::to_integer(v, gc, strings) {
        ArithResult::Ok(TValue::from_full_integer(!i, gc))
    } else if v.is_float() || v.as_number(gc).is_some() {
        // Number but can't convert to integer
        ArithResult::Error(crate::error::LuaError::Runtime(
            "number has no integer representation".to_string(),
        ))
    } else {
        ArithResult::NeedMetamethod
    }
}

/// String length (for # operator on strings).
pub fn str_len(v: TValue, strings: &StringInterner) -> Option<i64> {
    v.as_string_id()
        .map(|sid| strings.get_bytes(sid).len() as i64)
}

/// Concatenate a slice of TValues into a single string.
/// Returns NeedMetamethod if any value can't be converted to string.
pub fn lua_concat(values: &[TValue], gc: &GcHeap, strings: &mut StringInterner) -> ArithResult {
    let mut result = Vec::new();
    for &v in values.iter() {
        if let Some(sid) = coerce::to_string_for_concat(v, gc, strings) {
            result.extend_from_slice(strings.get_bytes(sid));
        } else {
            return ArithResult::NeedMetamethod;
        }
    }
    let sid = strings.intern_or_create(&result);
    ArithResult::Ok(TValue::from_string_id(sid))
}

/// Bitwise operations that need integer coercion.
/// Returns NeedMetamethod on type mismatch, or Error for float-to-int conversion failures.
pub fn bitwise_op(
    op: ArithOp,
    a: TValue,
    b: TValue,
    gc: &mut GcHeap,
    strings: &StringInterner,
) -> ArithResult {
    let ia = match coerce::to_integer(a, gc, strings) {
        Some(i) => i,
        None => {
            // If `a` is a float that can't convert to int, only error
            // immediately when the other operand (`b`) can't possibly
            // have a metamethod (is number/string). Otherwise return
            // NeedMetamethod so dispatch can try `b`'s metamethod.
            if a.is_float() && !could_have_metamethod(b, gc) {
                return ArithResult::Error(LuaError::Runtime(
                    "number has no integer representation".to_string(),
                ));
            }
            return ArithResult::NeedMetamethod;
        }
    };
    let ib = match coerce::to_integer(b, gc, strings) {
        Some(i) => i,
        None => {
            if b.is_float() && !could_have_metamethod(a, gc) {
                return ArithResult::Error(LuaError::Runtime(
                    "number has no integer representation".to_string(),
                ));
            }
            return ArithResult::NeedMetamethod;
        }
    };
    match int_arith(op, ia, ib, gc) {
        Ok(v) => ArithResult::Ok(v),
        Err(e) => ArithResult::Error(e),
    }
}

/// Check if a value could possibly have metamethods (table, userdata,
/// or a type with a type-wide metatable set).
fn could_have_metamethod(v: TValue, gc: &GcHeap) -> bool {
    if v.is_table() || v.is_userdata() {
        return true;
    }
    // Check for type-wide metatables
    if (v.is_number() || v.gc_sub_tag() == Some(selune_core::gc::GC_SUB_BOXED_INT))
        && gc.number_metatable.is_some()
    {
        return true;
    }
    if v.is_bool() && gc.boolean_metatable.is_some() {
        return true;
    }
    if v.is_nil() && gc.nil_metatable.is_some() {
        return true;
    }
    if v.is_string() && gc.string_metatable.is_some() {
        return true;
    }
    false
}

/// Arithmetic operation enum.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArithOp {
    Add,
    Sub,
    Mul,
    Div,
    IDiv,
    Mod,
    Pow,
    BAnd,
    BOr,
    BXor,
    Shl,
    Shr,
}
