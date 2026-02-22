//! Arithmetic operations with Lua 5.4 semantics.

use crate::coerce;
use crate::error::LuaError;
use selune_core::gc::GcHeap;
use selune_core::string::StringInterner;
use selune_core::value::TValue;

/// Perform a binary arithmetic operation.
pub fn arith_op(
    op: ArithOp,
    a: TValue,
    b: TValue,
    gc: &mut GcHeap,
    strings: &StringInterner,
) -> Result<TValue, LuaError> {
    // Fast path: both integers (except Div and Pow which always produce float)
    if !matches!(op, ArithOp::Div | ArithOp::Pow) {
        if let (Some(ia), Some(ib)) = (a.as_full_integer(gc), b.as_full_integer(gc)) {
            return int_arith(op, ia, ib, gc);
        }
    }

    // Float path: try to convert both to numbers
    let fa = coerce::to_number(a, gc, strings);
    let fb = coerce::to_number(b, gc, strings);

    match (fa, fb) {
        (Some(fa), Some(fb)) => {
            let result = float_arith(op, fa, fb)?;
            Ok(TValue::from_float(result))
        }
        _ => Err(LuaError::Runtime(format!(
            "attempt to perform arithmetic on a {} value",
            type_name_of(a, gc)
        ))),
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
                return Err(LuaError::Runtime("attempt to perform 'n//0'".to_string()));
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
            if b == 0.0 {
                return Err(LuaError::Runtime("attempt to perform 'n//0'".to_string()));
            }
            (a / b).floor()
        }
        ArithOp::Mod => {
            if b == 0.0 {
                return Err(LuaError::Runtime("attempt to perform 'n%0'".to_string()));
            }
            lua_fmod(a, b)
        }
        ArithOp::BAnd | ArithOp::BOr | ArithOp::BXor | ArithOp::Shl | ArithOp::Shr => {
            return Err(LuaError::Runtime(
                "attempt to perform bitwise operation on a float value".to_string(),
            ));
        }
    })
}

/// Lua integer division (floor division).
fn lua_idiv(a: i64, b: i64) -> i64 {
    let d = a / b;
    // If signs differ and there's a remainder, round towards negative infinity
    if (a ^ b) < 0 && d * b != a {
        d - 1
    } else {
        d
    }
}

/// Lua integer modulo.
fn lua_imod(a: i64, b: i64) -> i64 {
    let r = a % b;
    if r != 0 && (r ^ b) < 0 {
        r + b
    } else {
        r
    }
}

/// Lua float modulo.
fn lua_fmod(a: f64, b: f64) -> f64 {
    let r = a % b;
    if r != 0.0 && (r * b) < 0.0 {
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

/// Unary minus.
pub fn arith_unm(v: TValue, gc: &mut GcHeap, strings: &StringInterner) -> Result<TValue, LuaError> {
    if let Some(i) = v.as_full_integer(gc) {
        Ok(TValue::from_full_integer(i.wrapping_neg(), gc))
    } else if let Some(f) = v.as_float() {
        Ok(TValue::from_float(-f))
    } else if let Some(f) = coerce::to_number(v, gc, strings) {
        Ok(TValue::from_float(-f))
    } else {
        Err(LuaError::Runtime(format!(
            "attempt to perform arithmetic on a {} value",
            type_name_of(v, gc)
        )))
    }
}

/// Bitwise NOT.
pub fn arith_bnot(
    v: TValue,
    gc: &mut GcHeap,
    strings: &StringInterner,
) -> Result<TValue, LuaError> {
    if let Some(i) = v.as_full_integer(gc) {
        Ok(TValue::from_full_integer(!i, gc))
    } else if let Some(i) = coerce::to_integer(v, gc, strings) {
        Ok(TValue::from_full_integer(!i, gc))
    } else {
        Err(LuaError::Runtime(format!(
            "attempt to perform bitwise operation on a {} value",
            type_name_of(v, gc)
        )))
    }
}

/// String length (for # operator on strings).
pub fn str_len(v: TValue, strings: &StringInterner) -> Option<i64> {
    if let Some(sid) = v.as_string_id() {
        Some(strings.get_bytes(sid).len() as i64)
    } else {
        None
    }
}

/// Concatenate a slice of TValues into a single string.
pub fn lua_concat(
    values: &[TValue],
    gc: &GcHeap,
    strings: &mut StringInterner,
) -> Result<TValue, LuaError> {
    let mut result = Vec::new();
    for &v in values.iter() {
        if let Some(sid) = coerce::to_string_for_concat(v, gc, strings) {
            result.extend_from_slice(strings.get_bytes(sid));
        } else {
            return Err(LuaError::Runtime(format!(
                "attempt to concatenate a {} value",
                type_name_of(v, gc)
            )));
        }
    }
    let sid = strings.intern_or_create(&result);
    Ok(TValue::from_string_id(sid))
}

fn type_name_of(v: TValue, gc: &GcHeap) -> &'static str {
    selune_core::object::lua_type_name(v, gc)
}

/// Bitwise operations that need integer coercion.
pub fn bitwise_op(
    op: ArithOp,
    a: TValue,
    b: TValue,
    gc: &mut GcHeap,
    strings: &StringInterner,
) -> Result<TValue, LuaError> {
    let ia = coerce::to_integer(a, gc, strings).ok_or_else(|| {
        LuaError::Runtime(format!(
            "attempt to perform bitwise operation on a {} value",
            type_name_of(a, gc)
        ))
    })?;
    let ib = coerce::to_integer(b, gc, strings).ok_or_else(|| {
        LuaError::Runtime(format!(
            "attempt to perform bitwise operation on a {} value",
            type_name_of(b, gc)
        ))
    })?;
    int_arith(op, ia, ib, gc)
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
