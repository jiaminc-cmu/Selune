//! Lua 5.4 math library.

use selune_core::gc::{GcHeap, GcIdx, NativeContext, NativeError};
use selune_core::string::StringInterner;
use selune_core::table::Table;
use selune_core::value::TValue;
use std::cell::RefCell;

thread_local! {
    static RNG_STATE: RefCell<u64> = RefCell::new(0x12345678_9abcdef0);
}

/// Simple xoshiro256** PRNG.
fn prng_next() -> u64 {
    RNG_STATE.with(|state| {
        let mut s = state.borrow_mut();
        // SplitMix64 for simplicity and quality
        *s = s.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = *s;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    })
}

fn prng_seed(seed: u64) {
    RNG_STATE.with(|state| {
        *state.borrow_mut() = seed;
    });
}

/// Register the math library into _ENV.
pub fn register(
    env_idx: GcIdx<Table>,
    gc: &mut GcHeap,
    strings: &mut StringInterner,
) {
    let math_table = gc.alloc_table(0, 32);

    register_fn(gc, math_table, strings, "abs", native_math_abs);
    register_fn(gc, math_table, strings, "ceil", native_math_ceil);
    register_fn(gc, math_table, strings, "floor", native_math_floor);
    register_fn(gc, math_table, strings, "sqrt", native_math_sqrt);
    register_fn(gc, math_table, strings, "sin", native_math_sin);
    register_fn(gc, math_table, strings, "cos", native_math_cos);
    register_fn(gc, math_table, strings, "tan", native_math_tan);
    register_fn(gc, math_table, strings, "asin", native_math_asin);
    register_fn(gc, math_table, strings, "acos", native_math_acos);
    register_fn(gc, math_table, strings, "atan", native_math_atan);
    register_fn(gc, math_table, strings, "exp", native_math_exp);
    register_fn(gc, math_table, strings, "log", native_math_log);
    register_fn(gc, math_table, strings, "deg", native_math_deg);
    register_fn(gc, math_table, strings, "rad", native_math_rad);
    register_fn(gc, math_table, strings, "fmod", native_math_fmod);
    register_fn(gc, math_table, strings, "modf", native_math_modf);
    register_fn(gc, math_table, strings, "max", native_math_max);
    register_fn(gc, math_table, strings, "min", native_math_min);
    register_fn(gc, math_table, strings, "random", native_math_random);
    register_fn(gc, math_table, strings, "randomseed", native_math_randomseed);
    register_fn(gc, math_table, strings, "tointeger", native_math_tointeger);
    register_fn(gc, math_table, strings, "type", native_math_type);

    // Constants
    let pi_name = strings.intern(b"pi");
    gc.get_table_mut(math_table)
        .raw_set_str(pi_name, TValue::from_float(std::f64::consts::PI));

    let huge_name = strings.intern(b"huge");
    gc.get_table_mut(math_table)
        .raw_set_str(huge_name, TValue::from_float(f64::INFINITY));

    let maxint_name = strings.intern(b"maxinteger");
    let maxint_val = TValue::from_full_integer(i64::MAX, gc);
    gc.get_table_mut(math_table)
        .raw_set_str(maxint_name, maxint_val);

    let minint_name = strings.intern(b"mininteger");
    let minint_val = TValue::from_full_integer(i64::MIN, gc);
    gc.get_table_mut(math_table)
        .raw_set_str(minint_name, minint_val);

    let name = strings.intern(b"math");
    gc.get_table_mut(env_idx)
        .raw_set_str(name, TValue::from_table(math_table));
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

/// Get a numeric arg as f64, coercing integers.
fn get_number_arg(ctx: &NativeContext, idx: usize, fname: &str) -> Result<f64, NativeError> {
    let val = ctx.args.get(idx).copied().unwrap_or(TValue::nil());
    if let Some(f) = val.as_float() {
        return Ok(f);
    }
    if let Some(i) = val.as_full_integer(ctx.gc) {
        return Ok(i as f64);
    }
    Err(NativeError::String(format!(
        "bad argument #{} to '{}' (number expected, got {})",
        idx + 1,
        fname,
        type_name(val)
    )))
}

fn type_name(val: TValue) -> &'static str {
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
        "userdata"
    }
}

fn native_math_abs(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let val = ctx.args.first().copied().unwrap_or(TValue::nil());
    if let Some(i) = val.as_full_integer(ctx.gc) {
        return Ok(vec![TValue::from_full_integer(i.wrapping_abs(), ctx.gc)]);
    }
    let f = get_number_arg(ctx, 0, "abs")?;
    Ok(vec![TValue::from_float(f.abs())])
}

fn native_math_ceil(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let val = ctx.args.first().copied().unwrap_or(TValue::nil());
    if val.as_full_integer(ctx.gc).is_some() {
        return Ok(vec![val]); // already integer
    }
    let f = get_number_arg(ctx, 0, "ceil")?;
    let c = f.ceil();
    if c >= i64::MIN as f64 && c <= i64::MAX as f64 && c == (c as i64) as f64 {
        Ok(vec![TValue::from_full_integer(c as i64, ctx.gc)])
    } else {
        Ok(vec![TValue::from_float(c)])
    }
}

fn native_math_floor(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let val = ctx.args.first().copied().unwrap_or(TValue::nil());
    if val.as_full_integer(ctx.gc).is_some() {
        return Ok(vec![val]); // already integer
    }
    let f = get_number_arg(ctx, 0, "floor")?;
    let c = f.floor();
    if c >= i64::MIN as f64 && c <= i64::MAX as f64 && c == (c as i64) as f64 {
        Ok(vec![TValue::from_full_integer(c as i64, ctx.gc)])
    } else {
        Ok(vec![TValue::from_float(c)])
    }
}

fn native_math_sqrt(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let f = get_number_arg(ctx, 0, "sqrt")?;
    Ok(vec![TValue::from_float(f.sqrt())])
}

fn native_math_sin(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let f = get_number_arg(ctx, 0, "sin")?;
    Ok(vec![TValue::from_float(f.sin())])
}

fn native_math_cos(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let f = get_number_arg(ctx, 0, "cos")?;
    Ok(vec![TValue::from_float(f.cos())])
}

fn native_math_tan(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let f = get_number_arg(ctx, 0, "tan")?;
    Ok(vec![TValue::from_float(f.tan())])
}

fn native_math_asin(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let f = get_number_arg(ctx, 0, "asin")?;
    Ok(vec![TValue::from_float(f.asin())])
}

fn native_math_acos(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let f = get_number_arg(ctx, 0, "acos")?;
    Ok(vec![TValue::from_float(f.acos())])
}

fn native_math_atan(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let y = get_number_arg(ctx, 0, "atan")?;
    let x = if ctx.args.len() > 1 {
        get_number_arg(ctx, 1, "atan")?
    } else {
        1.0
    };
    Ok(vec![TValue::from_float(y.atan2(x))])
}

fn native_math_exp(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let f = get_number_arg(ctx, 0, "exp")?;
    Ok(vec![TValue::from_float(f.exp())])
}

fn native_math_log(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let x = get_number_arg(ctx, 0, "log")?;
    if ctx.args.len() > 1 {
        let base = get_number_arg(ctx, 1, "log")?;
        Ok(vec![TValue::from_float(x.ln() / base.ln())])
    } else {
        Ok(vec![TValue::from_float(x.ln())])
    }
}

fn native_math_deg(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let f = get_number_arg(ctx, 0, "deg")?;
    Ok(vec![TValue::from_float(f.to_degrees())])
}

fn native_math_rad(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let f = get_number_arg(ctx, 0, "rad")?;
    Ok(vec![TValue::from_float(f.to_radians())])
}

fn native_math_fmod(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let x = get_number_arg(ctx, 0, "fmod")?;
    let y = get_number_arg(ctx, 1, "fmod")?;
    if y == 0.0 {
        return Err(NativeError::String(
            "bad argument #2 to 'fmod' (zero)".to_string(),
        ));
    }
    // Lua fmod: result has same sign as x
    let r = x % y;
    Ok(vec![TValue::from_float(r)])
}

fn native_math_modf(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let f = get_number_arg(ctx, 0, "modf")?;
    let trunc = f.trunc();
    let frac = f - trunc;
    // Integer part returned as integer if it fits
    let int_part = if trunc >= i64::MIN as f64 && trunc <= i64::MAX as f64 && trunc == (trunc as i64) as f64 {
        TValue::from_full_integer(trunc as i64, ctx.gc)
    } else {
        TValue::from_float(trunc)
    };
    Ok(vec![int_part, TValue::from_float(frac)])
}

fn native_math_max(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    if ctx.args.is_empty() {
        return Err(NativeError::String(
            "bad argument #1 to 'max' (value expected)".to_string(),
        ));
    }
    let mut best = ctx.args[0];
    let mut best_f = get_number_arg(ctx, 0, "max")?;
    for i in 1..ctx.args.len() {
        let f = get_number_arg(ctx, i, "max")?;
        if f > best_f {
            best = ctx.args[i];
            best_f = f;
        }
    }
    Ok(vec![best])
}

fn native_math_min(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    if ctx.args.is_empty() {
        return Err(NativeError::String(
            "bad argument #1 to 'min' (value expected)".to_string(),
        ));
    }
    let mut best = ctx.args[0];
    let mut best_f = get_number_arg(ctx, 0, "min")?;
    for i in 1..ctx.args.len() {
        let f = get_number_arg(ctx, i, "min")?;
        if f < best_f {
            best = ctx.args[i];
            best_f = f;
        }
    }
    Ok(vec![best])
}

fn native_math_random(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let nargs = ctx.args.len();
    if nargs == 0 {
        // Return float in [0, 1)
        let r = (prng_next() >> 11) as f64 / (1u64 << 53) as f64;
        Ok(vec![TValue::from_float(r)])
    } else if nargs == 1 {
        // random(m): return integer in [1, m]
        let m = ctx
            .args[0]
            .as_full_integer(ctx.gc)
            .ok_or_else(|| NativeError::String("bad argument #1 to 'random' (number expected)".to_string()))?;
        if m < 1 {
            return Err(NativeError::String(
                "bad argument #1 to 'random' (interval is empty)".to_string(),
            ));
        }
        let r = (prng_next() % m as u64) as i64 + 1;
        Ok(vec![TValue::from_full_integer(r, ctx.gc)])
    } else {
        // random(m, n): return integer in [m, n]
        let m = ctx
            .args[0]
            .as_full_integer(ctx.gc)
            .ok_or_else(|| NativeError::String("bad argument #1 to 'random' (number expected)".to_string()))?;
        let n = ctx
            .args[1]
            .as_full_integer(ctx.gc)
            .ok_or_else(|| NativeError::String("bad argument #2 to 'random' (number expected)".to_string()))?;
        if m > n {
            return Err(NativeError::String(
                "bad argument #2 to 'random' (interval is empty)".to_string(),
            ));
        }
        let range = (n - m) as u64 + 1;
        let r = (prng_next() % range) as i64 + m;
        Ok(vec![TValue::from_full_integer(r, ctx.gc)])
    }
}

fn native_math_randomseed(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let seed = if ctx.args.is_empty() {
        // Use time-based seed
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos() as u64)
            .unwrap_or(42)
    } else {
        let val = ctx.args[0];
        if let Some(i) = val.as_full_integer(ctx.gc) {
            i as u64
        } else if let Some(f) = val.as_float() {
            f.to_bits()
        } else {
            0
        }
    };
    prng_seed(seed);
    Ok(vec![])
}

fn native_math_tointeger(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let val = ctx.args.first().copied().unwrap_or(TValue::nil());
    if val.as_full_integer(ctx.gc).is_some() {
        return Ok(vec![val]);
    }
    if let Some(f) = val.as_float() {
        if f.fract() == 0.0 && f >= i64::MIN as f64 && f <= i64::MAX as f64 {
            return Ok(vec![TValue::from_full_integer(f as i64, ctx.gc)]);
        }
    }
    Ok(vec![TValue::nil()])
}

fn native_math_type(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let val = ctx.args.first().copied().unwrap_or(TValue::nil());
    if val.as_full_integer(ctx.gc).is_some() {
        let sid = ctx.strings.intern(b"integer");
        Ok(vec![TValue::from_string_id(sid)])
    } else if val.as_float().is_some() {
        let sid = ctx.strings.intern(b"float");
        Ok(vec![TValue::from_string_id(sid)])
    } else {
        Ok(vec![TValue::from_bool(false)])
    }
}
