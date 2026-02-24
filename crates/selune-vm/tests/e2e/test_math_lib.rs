use super::helpers::*;

// ---- math.abs ----

#[test]
fn test_math_abs_positive() {
    run_check_ints("return math.abs(42)", &[42]);
}

#[test]
fn test_math_abs_negative() {
    run_check_ints("return math.abs(-42)", &[42]);
}

#[test]
fn test_math_abs_zero() {
    run_check_ints("return math.abs(0)", &[0]);
}

#[test]
fn test_math_abs_float() {
    run_check_floats("return math.abs(-3.5)", &[3.5]);
}

// ---- math.ceil / math.floor ----

#[test]
fn test_math_ceil_float() {
    run_check_ints("return math.ceil(2.3)", &[3]);
}

#[test]
fn test_math_ceil_negative() {
    run_check_ints("return math.ceil(-2.3)", &[-2]);
}

#[test]
fn test_math_ceil_integer() {
    run_check_ints("return math.ceil(5)", &[5]);
}

#[test]
fn test_math_floor_float() {
    run_check_ints("return math.floor(2.7)", &[2]);
}

#[test]
fn test_math_floor_negative() {
    run_check_ints("return math.floor(-2.3)", &[-3]);
}

#[test]
fn test_math_floor_integer() {
    run_check_ints("return math.floor(5)", &[5]);
}

// ---- math.sqrt ----

#[test]
fn test_math_sqrt() {
    run_check_floats("return math.sqrt(4.0)", &[2.0]);
}

#[test]
fn test_math_sqrt_integer() {
    run_check_floats("return math.sqrt(9)", &[3.0]);
}

// ---- math.sin / cos / tan ----

#[test]
fn test_math_sin_zero() {
    run_check_floats("return math.sin(0)", &[0.0]);
}

#[test]
fn test_math_cos_zero() {
    run_check_floats("return math.cos(0)", &[1.0]);
}

#[test]
fn test_math_tan_zero() {
    run_check_floats("return math.tan(0)", &[0.0]);
}

// ---- math.asin / acos ----

#[test]
fn test_math_asin_zero() {
    run_check_floats("return math.asin(0)", &[0.0]);
}

#[test]
fn test_math_acos_one() {
    run_check_floats("return math.acos(1)", &[0.0]);
}

// ---- math.atan ----

#[test]
fn test_math_atan_one_arg() {
    run_check_floats("return math.atan(1)", &[std::f64::consts::FRAC_PI_4]);
}

#[test]
fn test_math_atan_two_args() {
    run_check_floats("return math.atan(1, 1)", &[std::f64::consts::FRAC_PI_4]);
}

// ---- math.exp / log ----

#[test]
fn test_math_exp_zero() {
    run_check_floats("return math.exp(0)", &[1.0]);
}

#[test]
fn test_math_exp_one() {
    run_check_floats("return math.exp(1)", &[std::f64::consts::E]);
}

#[test]
fn test_math_log_e() {
    run_check_floats("return math.log(math.exp(1))", &[1.0]);
}

#[test]
fn test_math_log_base() {
    run_check_floats("return math.log(100, 10)", &[2.0]);
}

// ---- math.deg / rad ----

#[test]
fn test_math_deg() {
    run_check_floats("return math.deg(math.pi)", &[180.0]);
}

#[test]
fn test_math_rad() {
    run_check_floats("return math.rad(180)", &[std::f64::consts::PI]);
}

// ---- math.fmod ----

#[test]
fn test_math_fmod_basic() {
    // When both args are integers, fmod returns integer (Lua 5.4 spec)
    let results = run_lua("return math.fmod(7, 3)");
    assert_int(&results, 0, 1);
}

#[test]
fn test_math_fmod_negative() {
    let results = run_lua("return math.fmod(-7, 3)");
    assert_int(&results, 0, -1);
}

// ---- math.modf ----

#[test]
fn test_math_modf_positive() {
    let results = run_lua("return math.modf(3.75)");
    assert_eq!(results.len(), 2);
    assert_int(&results, 0, 3);
    assert_float(&results, 1, 0.75);
}

#[test]
fn test_math_modf_negative() {
    let results = run_lua("return math.modf(-3.75)");
    assert_eq!(results.len(), 2);
    assert_int(&results, 0, -3);
    assert_float(&results, 1, -0.75);
}

#[test]
fn test_math_modf_integer() {
    let results = run_lua("return math.modf(5)");
    assert_eq!(results.len(), 2);
    assert_int(&results, 0, 5);
    assert_float(&results, 1, 0.0);
}

// ---- math.max / math.min ----

#[test]
fn test_math_max() {
    run_check_ints("return math.max(1, 5, 3)", &[5]);
}

#[test]
fn test_math_max_single() {
    run_check_ints("return math.max(42)", &[42]);
}

#[test]
fn test_math_max_negative() {
    run_check_ints("return math.max(-5, -1, -10)", &[-1]);
}

#[test]
fn test_math_min() {
    run_check_ints("return math.min(1, 5, 3)", &[1]);
}

#[test]
fn test_math_min_single() {
    run_check_ints("return math.min(42)", &[42]);
}

#[test]
fn test_math_min_negative() {
    run_check_ints("return math.min(-5, -1, -10)", &[-10]);
}

// ---- math.random ----

#[test]
fn test_math_random_no_args() {
    // Should return float in [0, 1)
    let results = run_lua("math.randomseed(42)\nreturn math.random()");
    let f = results[0].as_float().expect("expected float");
    assert!((0.0..1.0).contains(&f), "random() = {f}, expected [0,1)");
}

#[test]
fn test_math_random_one_arg() {
    let results = run_lua(
        r#"
        math.randomseed(42)
        local r = math.random(10)
        return r
        "#,
    );
    let i = results[0].as_integer().expect("expected integer");
    assert!((1..=10).contains(&i), "random(10) = {i}, expected [1,10]");
}

#[test]
fn test_math_random_two_args() {
    let results = run_lua(
        r#"
        math.randomseed(42)
        local r = math.random(5, 15)
        return r
        "#,
    );
    let i = results[0].as_integer().expect("expected integer");
    assert!((5..=15).contains(&i), "random(5,15) = {i}, expected [5,15]");
}

// ---- math.tointeger ----

#[test]
fn test_math_tointeger_int() {
    run_check_ints("return math.tointeger(42)", &[42]);
}

#[test]
fn test_math_tointeger_float_exact() {
    run_check_ints("return math.tointeger(42.0)", &[42]);
}

#[test]
fn test_math_tointeger_float_frac() {
    let results = run_lua("return math.tointeger(42.5)");
    assert_nil(&results, 0);
}

#[test]
fn test_math_tointeger_string() {
    let results = run_lua(r#"return math.tointeger("hello")"#);
    assert_nil(&results, 0);
}

// ---- math.type ----

#[test]
fn test_math_type_integer() {
    run_check_strings("return math.type(42)", &["integer"]);
}

#[test]
fn test_math_type_float() {
    run_check_strings("return math.type(42.0)", &["float"]);
}

#[test]
fn test_math_type_non_number() {
    let results = run_lua(r#"return math.type("hello")"#);
    assert_bool(&results, 0, false);
}

// ---- math constants ----

#[test]
fn test_math_pi() {
    run_check_floats("return math.pi", &[std::f64::consts::PI]);
}

#[test]
fn test_math_huge() {
    let results = run_lua("return math.huge");
    let f = results[0].as_float().expect("expected float");
    assert!(f.is_infinite() && f > 0.0, "expected +inf, got {f}");
}

#[test]
fn test_math_maxinteger() {
    // math.maxinteger == 2^63 - 1, verify via comparison
    let results = run_lua("return math.maxinteger > 0");
    assert_bool(&results, 0, true);
}

#[test]
fn test_math_mininteger() {
    // math.mininteger < 0
    let results = run_lua("return math.mininteger < 0");
    assert_bool(&results, 0, true);
}

#[test]
fn test_math_maxinteger_is_positive() {
    // math.maxinteger should be a very large positive number
    let results = run_lua("return math.maxinteger > 1000000");
    assert_bool(&results, 0, true);
}

// ---- edge cases ----

#[test]
fn test_math_sqrt_nan() {
    let results = run_lua("return math.sqrt(-1)");
    let f = results[0].as_float().expect("expected float");
    assert!(f.is_nan(), "expected NaN, got {f}");
}

#[test]
fn test_math_log_zero() {
    let results = run_lua("return math.log(0)");
    let f = results[0].as_float().expect("expected float");
    assert!(f.is_infinite() && f < 0.0, "expected -inf, got {f}");
}

#[test]
fn test_math_huge_arithmetic() {
    let results = run_lua("return math.huge + 1");
    let f = results[0].as_float().expect("expected float");
    assert!(f.is_infinite(), "expected inf, got {f}");
}
