//! Lua 5.4 math library.

use selune_core::gc::{GcHeap, GcIdx, NativeContext, NativeError};
use selune_core::string::StringInterner;
use selune_core::table::Table;
use selune_core::value::TValue;
use std::cell::RefCell;

/// Lua 5.4 xoshiro256** PRNG state
struct RanState {
    s: [u64; 4],
}

thread_local! {
    static RNG_STATE: RefCell<RanState> = RefCell::new(RanState { s: [0; 4] });
}

fn rotl(x: u64, n: i32) -> u64 {
    x.rotate_left(n as u32)
}

/// xoshiro256** next random value — matches Lua 5.4 exactly
fn nextrand(state: &mut RanState) -> u64 {
    let s = &mut state.s;
    let res = rotl(s[1].wrapping_mul(5), 7).wrapping_mul(9);
    let t = s[1] << 17;
    s[2] ^= s[0];
    s[3] ^= s[1];
    s[1] ^= s[2];
    s[0] ^= s[3];
    s[2] ^= t;
    s[3] = rotl(s[3], 45);
    res
}

/// Seed the PRNG — matches Lua 5.4's `randseed` in lmathlib.c
fn setseed(state: &mut RanState, n1: u64, n2: u64) {
    state.s[0] = n1;
    state.s[1] = 0xff; // FIXEDMARK
    state.s[2] = n2;
    state.s[3] = 0;
    for _ in 0..16 {
        nextrand(state);
    }
}

/// Convert random u64 to float in [0, 1) — matches Lua 5.4's I2d
fn i2d(x: u64) -> f64 {
    let shifted = (x >> 11) as i64; // shift right by (64 - 53)
    let r = (shifted as f64) * (1.0 / 9007199254740992.0); // * 2^(-53)
    if r < 0.0 { r + 1.0 } else { r }
}

/// Project random u64 into [0, n] with rejection sampling — matches Lua 5.4
fn project(rv: u64, n: u64, state: &mut RanState) -> u64 {
    if n == 0 {
        return 0;
    }
    // Find smallest (2^b - 1) >= n by filling bits
    let mut lim = n;
    // fill 'lim' with 1s in all positions after the highest 1-bit
    lim |= lim >> 1;
    lim |= lim >> 2;
    lim |= lim >> 4;
    lim |= lim >> 8;
    lim |= lim >> 16;
    lim |= lim >> 32;
    let mut rv = rv;
    loop {
        // project 'rv' into [0..lim]
        // For 64-bit: when lim == u64::MAX, we can't shift by 64
        let sh = lim.leading_zeros(); // number of leading zeros
        let masked = if sh >= 64 { rv } else { (rv >> sh) & lim };
        if masked <= n {
            return masked;
        }
        // rejected; try again with a new random value
        rv = nextrand(state);
    }
}

/// Safely convert float to integer, returning None if out of range or not whole
fn float_to_integer(f: f64) -> Option<i64> {
    if f.fract() != 0.0 || f.is_nan() || f.is_infinite() {
        return None;
    }
    // i64::MIN as f64 is exactly representable (-2^63)
    // i64::MAX as f64 rounds up to 2^63, so we check < 2^63
    // which is the same as < (i64::MIN as f64).abs() or equivalently
    // we check that f >= i64::MIN as f64 and f < 2^63
    const MAX_FLOAT: f64 = 9223372036854775808.0; // 2^63
    if f >= i64::MIN as f64 && f < MAX_FLOAT {
        Some(f as i64)
    } else {
        None
    }
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
    register_fn(gc, math_table, strings, "ult", native_math_ult);

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
    let tname = selune_core::object::obj_type_name(val, ctx.gc, ctx.strings);
    Err(NativeError::String(format!(
        "bad argument #{} to '{}' (number expected, got {})",
        idx + 1,
        fname,
        tname
    )))
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
    if let Some(i) = float_to_integer(c) {
        Ok(vec![TValue::from_full_integer(i, ctx.gc)])
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
    if let Some(i) = float_to_integer(c) {
        Ok(vec![TValue::from_full_integer(i, ctx.gc)])
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
    let a = ctx.args.first().copied().unwrap_or(TValue::nil());
    let b = ctx.args.get(1).copied().unwrap_or(TValue::nil());
    // If both are integers, return integer result
    if let (Some(ai), Some(bi)) = (a.as_full_integer(ctx.gc), b.as_full_integer(ctx.gc)) {
        if bi == 0 {
            return Err(NativeError::String(
                "bad argument #2 to 'fmod' (zero)".to_string(),
            ));
        }
        // Use wrapping_rem to handle minint % -1 (which would panic with normal %)
        let r = ai.wrapping_rem(bi);
        return Ok(vec![TValue::from_full_integer(r, ctx.gc)]);
    }
    let x = get_number_arg(ctx, 0, "fmod")?;
    let y = get_number_arg(ctx, 1, "fmod")?;
    if y == 0.0 {
        return Err(NativeError::String(
            "bad argument #2 to 'fmod' (zero)".to_string(),
        ));
    }
    // Lua fmod: result has same sign as x (C fmod semantics)
    let r = x % y;
    Ok(vec![TValue::from_float(r)])
}

fn native_math_modf(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let f = get_number_arg(ctx, 0, "modf")?;
    let trunc = f.trunc();
    let frac = if f.is_infinite() {
        0.0_f64.copysign(f)
    } else {
        f - trunc
    };
    // Integer part returned as integer if it fits
    let int_part = if let Some(i) = float_to_integer(trunc) {
        TValue::from_full_integer(i, ctx.gc)
    } else {
        TValue::from_float(trunc)
    };
    Ok(vec![int_part, TValue::from_float(frac)])
}

/// Compare two numeric TValues using Lua ordering:
/// int vs int → i64 compare; float vs float → f64 compare;
/// mixed → convert int to float then compare.
fn lua_num_lt(a: TValue, b: TValue, gc: &GcHeap) -> bool {
    match (a.as_full_integer(gc), b.as_full_integer(gc)) {
        (Some(ai), Some(bi)) => ai < bi,
        (Some(ai), None) => (ai as f64) < b.as_float().unwrap_or(f64::NAN),
        (None, Some(bi)) => a.as_float().unwrap_or(f64::NAN) < (bi as f64),
        (None, None) => {
            a.as_float().unwrap_or(f64::NAN) < b.as_float().unwrap_or(f64::NAN)
        }
    }
}

fn native_math_max(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    if ctx.args.is_empty() {
        return Err(NativeError::String(
            "bad argument #1 to 'max' (value expected)".to_string(),
        ));
    }
    // Validate first arg is a number
    let _ = get_number_arg(ctx, 0, "max")?;
    let mut best = ctx.args[0];
    for i in 1..ctx.args.len() {
        let _ = get_number_arg(ctx, i, "max")?;
        if lua_num_lt(best, ctx.args[i], ctx.gc) {
            best = ctx.args[i];
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
    let _ = get_number_arg(ctx, 0, "min")?;
    let mut best = ctx.args[0];
    for i in 1..ctx.args.len() {
        let _ = get_number_arg(ctx, i, "min")?;
        if lua_num_lt(ctx.args[i], best, ctx.gc) {
            best = ctx.args[i];
        }
    }
    Ok(vec![best])
}

fn native_math_random(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let nargs = ctx.args.len();
    if nargs > 2 {
        return Err(NativeError::String(
            "wrong number of arguments".to_string(),
        ));
    }
    RNG_STATE.with(|state_cell| {
        let mut state = state_cell.borrow_mut();
        if nargs == 0 {
            // Return float in [0, 1)
            let rv = nextrand(&mut state);
            Ok(vec![TValue::from_float(i2d(rv))])
        } else if nargs == 1 {
            let low_val = ctx.args[0].as_full_integer(ctx.gc).ok_or_else(|| {
                NativeError::String("bad argument #1 to 'random' (number has no integer representation)".to_string())
            })?;
            let rv = nextrand(&mut state);
            if low_val == 0 {
                // random(0): return raw random bits as integer
                Ok(vec![TValue::from_full_integer(rv as i64, ctx.gc)])
            } else if low_val >= 1 {
                // random(n): return integer in [1, n]
                let r = project(rv, (low_val as u64).wrapping_sub(1), &mut state);
                let result = (r as i64).wrapping_add(1);
                Ok(vec![TValue::from_full_integer(result, ctx.gc)])
            } else {
                Err(NativeError::String(
                    "bad argument #1 to 'random' (interval is empty)".to_string(),
                ))
            }
        } else {
            // random(m, n): return integer in [m, n]
            let low = ctx.args[0].as_full_integer(ctx.gc).ok_or_else(|| {
                NativeError::String("bad argument #1 to 'random' (number has no integer representation)".to_string())
            })?;
            let up = ctx.args[1].as_full_integer(ctx.gc).ok_or_else(|| {
                NativeError::String("bad argument #2 to 'random' (number has no integer representation)".to_string())
            })?;
            // Range as unsigned: (up - low) using wrapping subtraction
            let range = (up as u64).wrapping_sub(low as u64);
            if (up as u64) < (low as u64).wrapping_add(range) {
                // This means low > up (empty interval) — but check simpler:
            }
            if low > up {
                return Err(NativeError::String(
                    "bad argument #2 to 'random' (interval is empty)".to_string(),
                ));
            }
            let rv = nextrand(&mut state);
            let r = project(rv, range, &mut state);
            let result = (low as u64).wrapping_add(r) as i64;
            Ok(vec![TValue::from_full_integer(result, ctx.gc)])
        }
    })
}

fn native_math_randomseed(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let nargs = ctx.args.len();
    RNG_STATE.with(|state_cell| {
        let mut state = state_cell.borrow_mut();
        let (n1, n2) = if nargs == 0 {
            // Time-based seed
            let t = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_nanos() as u64)
                .unwrap_or(42);
            let n2 = nextrand(&mut state);
            (t, n2)
        } else if nargs == 1 {
            let val = ctx.args[0];
            let n1 = if let Some(i) = val.as_full_integer(ctx.gc) {
                i as u64
            } else if let Some(f) = val.as_float() {
                f as i64 as u64
            } else {
                0
            };
            (n1, 0u64)
        } else {
            let val1 = ctx.args[0];
            let val2 = ctx.args[1];
            let n1 = if let Some(i) = val1.as_full_integer(ctx.gc) {
                i as u64
            } else if let Some(f) = val1.as_float() {
                f as i64 as u64
            } else {
                0
            };
            let n2 = if let Some(i) = val2.as_full_integer(ctx.gc) {
                i as u64
            } else if let Some(f) = val2.as_float() {
                f as i64 as u64
            } else {
                0
            };
            (n1, n2)
        };
        setseed(&mut state, n1, n2);
        Ok(vec![
            TValue::from_full_integer(n1 as i64, ctx.gc),
            TValue::from_full_integer(n2 as i64, ctx.gc),
        ])
    })
}

fn native_math_tointeger(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let val = ctx.args.first().copied().unwrap_or(TValue::nil());
    if val.as_full_integer(ctx.gc).is_some() {
        return Ok(vec![val]);
    }
    if let Some(f) = val.as_float() {
        if float_to_integer(f).is_some() {
            return Ok(vec![TValue::from_full_integer(f as i64, ctx.gc)]);
        }
        return Ok(vec![TValue::nil()]);
    }
    // Handle string arguments: try to parse as number then convert to integer
    if let Some(sid) = val.as_string_id() {
        let bytes = ctx.strings.get_bytes(sid);
        let s = std::str::from_utf8(bytes).unwrap_or("").trim();
        // Try parsing as integer directly
        if let Ok(i) = s.parse::<i64>() {
            return Ok(vec![TValue::from_full_integer(i, ctx.gc)]);
        }
        // Try hex integer
        if let Some(hex) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
            if let Ok(i) = i64::from_str_radix(hex, 16) {
                return Ok(vec![TValue::from_full_integer(i, ctx.gc)]);
            }
        }
        if let Some(hex) = s.strip_prefix("-0x").or_else(|| s.strip_prefix("-0X")) {
            if let Ok(i) = i64::from_str_radix(hex, 16) {
                return Ok(vec![TValue::from_full_integer(-i, ctx.gc)]);
            }
        }
        // Try parsing as float and check if it's an integer value
        if let Ok(f) = s.parse::<f64>() {
            if let Some(i) = float_to_integer(f) {
                return Ok(vec![TValue::from_full_integer(i, ctx.gc)]);
            }
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

fn native_math_ult(ctx: &mut NativeContext) -> Result<Vec<TValue>, NativeError> {
    let a = ctx.args.first().copied().unwrap_or(TValue::nil());
    let b = ctx.args.get(1).copied().unwrap_or(TValue::nil());
    let ai = a.as_full_integer(ctx.gc).ok_or_else(|| {
        NativeError::String("bad argument #1 to 'ult' (number has no integer representation)".to_string())
    })?;
    let bi = b.as_full_integer(ctx.gc).ok_or_else(|| {
        NativeError::String("bad argument #2 to 'ult' (number has no integer representation)".to_string())
    })?;
    Ok(vec![TValue::from_bool((ai as u64) < (bi as u64))])
}
