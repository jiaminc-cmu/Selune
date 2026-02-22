use super::helpers::*;

// ==========================================================================
// 2A. Number Semantics — Integer/Float duality tests
// ==========================================================================

#[test]
fn number_type_returns_number_for_both() {
    run_lua(
        r#"
        assert(type(3) == "number")
        assert(type(3.0) == "number")
        "#,
    );
}

#[test]
fn number_math_type_distinguishes() {
    run_lua(
        r#"
        assert(math.type(3) == "integer")
        assert(math.type(3.0) == "float")
        "#,
    );
}

#[test]
fn number_integer_arithmetic_preserves_type() {
    run_lua(
        r#"
        assert(math.type(3 + 4) == "integer")
        assert(math.type(10 - 3) == "integer")
        assert(math.type(3 * 4) == "integer")
        assert(math.type(10 % 3) == "integer")
        "#,
    );
}

#[test]
fn number_float_arithmetic_preserves_type() {
    run_lua(
        r#"
        assert(math.type(3.0 + 4.0) == "float")
        assert(math.type(10.0 - 3.0) == "float")
        assert(math.type(3.0 * 4.0) == "float")
        "#,
    );
}

#[test]
fn number_mixed_promotes_to_float() {
    run_lua(
        r#"
        assert(math.type(3 + 4.0) == "float")
        assert(math.type(3.0 + 4) == "float")
        assert(math.type(3 * 4.0) == "float")
        "#,
    );
}

#[test]
fn number_division_always_float() {
    run_lua(
        r#"
        assert(math.type(6 / 2) == "float")
        assert(6 / 2 == 3.0)
        assert(math.type(7 / 2) == "float")
        assert(7 / 2 == 3.5)
        "#,
    );
}

#[test]
fn number_floor_div_integer_stays_integer() {
    run_lua(
        r#"
        assert(math.type(7 // 2) == "integer")
        assert(7 // 2 == 3)
        "#,
    );
}

#[test]
fn number_floor_div_with_float_gives_float() {
    run_lua(
        r#"
        assert(math.type(7 // 2.0) == "float")
        assert(7 // 2.0 == 3.0)
        assert(math.type(7.0 // 2) == "float")
        assert(7.0 // 2 == 3.0)
        "#,
    );
}

#[test]
fn number_modulo_same_rules() {
    run_lua(
        r#"
        assert(math.type(7 % 2) == "integer")
        assert(7 % 2 == 1)
        assert(math.type(7.0 % 2) == "float")
        "#,
    );
}

#[test]
fn number_power_always_float() {
    run_lua(
        r#"
        assert(math.type(2 ^ 3) == "float")
        assert(2 ^ 3 == 8.0)
        assert(math.type(2 ^ 0) == "float")
        "#,
    );
}

#[test]
fn number_unary_minus_preserves_type() {
    run_lua(
        r#"
        assert(math.type(-3) == "integer")
        assert(math.type(-3.0) == "float")
        assert(-3 == -3)
        "#,
    );
}

#[test]
fn number_string_coercion_integer() {
    run_lua(
        r#"
        assert(math.type("10" + 5) == "integer")
        assert("10" + 5 == 15)
        "#,
    );
}

#[test]
fn number_string_coercion_float() {
    run_lua(
        r#"
        assert(math.type("10.5" + 5) == "float")
        assert("10.5" + 5 == 15.5)
        "#,
    );
}

#[test]
fn number_integer_overflow_wraps() {
    run_lua(
        r#"
        assert(math.maxinteger + 1 == math.mininteger)
        assert(math.mininteger - 1 == math.maxinteger)
        "#,
    );
}

#[test]
fn number_tonumber_integer_vs_float() {
    run_lua(
        r#"
        assert(math.type(tonumber("10")) == "integer")
        assert(math.type(tonumber("10.0")) == "float")
        "#,
    );
}

#[test]
fn number_tonumber_hex() {
    run_lua(
        r#"
        assert(tonumber("0xff") == 255)
        assert(tonumber("0xFF") == 255)
        "#,
    );
}

#[test]
fn number_tonumber_whitespace() {
    run_lua(
        r#"
        assert(tonumber("  42  ") == 42)
        assert(tonumber("  3.14  ") == 3.14)
        "#,
    );
}

#[test]
fn number_tonumber_invalid() {
    run_lua(
        r#"
        assert(tonumber("hello") == nil)
        assert(tonumber("") == nil)
        assert(tonumber("12abc") == nil)
        "#,
    );
}

#[test]
fn number_tostring_integer() {
    run_lua(
        r#"
        assert(tostring(10) == "10")
        assert(tostring(-5) == "-5")
        assert(tostring(0) == "0")
        "#,
    );
}

#[test]
fn number_tostring_float() {
    run_lua(
        r#"
        assert(tostring(10.0) == "10.0")
        assert(tostring(3.14) == "3.14")
        assert(tostring(-0.5) == "-0.5")
        "#,
    );
}

#[test]
fn number_equality_cross_type() {
    run_lua(
        r#"
        assert(1 == 1.0)
        assert(0 == 0.0)
        assert(-1 == -1.0)
        assert(not (1 == 2.0))
        "#,
    );
}

#[test]
fn number_comparison_cross_type() {
    run_lua(
        r#"
        assert(1 < 2.0)
        assert(1.0 < 2)
        assert(1 <= 1.0)
        assert(2.0 > 1)
        "#,
    );
}

#[test]
fn number_bitwise_requires_integer() {
    run_lua(
        r#"
        assert(0xFF & 0x0F == 0x0F)
        assert(0x0F | 0xF0 == 0xFF)
        assert(1 << 4 == 16)
        assert(16 >> 4 == 1)
        assert(~0 == -1)
        "#,
    );
}

#[test]
fn number_float_to_integer_coercion_bitwise() {
    run_lua(
        r#"
        -- Float with exact integer value can be used in bitwise
        assert(3.0 & 1 == 1)
        assert(3.0 | 4 == 7)
        "#,
    );
}

#[test]
fn number_nan_properties() {
    let results = run_lua("return 0/0");
    assert_float_nan(&results, 0);
}

#[test]
fn number_infinity() {
    let results = run_lua("return 1/0, -1/0");
    assert_float_inf(&results, 0, true);
    assert_float_inf(&results, 1, false);
}

#[test]
fn number_math_maxinteger_value() {
    run_check_ints("return math.maxinteger", &[i64::MAX]);
}

#[test]
fn number_math_mininteger_value() {
    run_check_ints("return math.mininteger", &[i64::MIN]);
}

#[test]
fn number_integer_division_negative() {
    run_lua(
        r#"
        assert(-7 // 2 == -4)   -- floor division rounds toward -inf
        assert(7 // -2 == -4)
        assert(-7 // -2 == 3)
        "#,
    );
}

#[test]
fn number_modulo_negative() {
    run_lua(
        r#"
        assert(-7 % 2 == 1)    -- Lua modulo: result has sign of divisor
        assert(7 % -2 == -1)
        assert(-7 % -2 == -1)
        "#,
    );
}

#[test]
fn number_float_equality_precision() {
    run_lua(
        r#"
        -- Exact powers of 2 should be exact
        assert(2^53 == 9007199254740992)
        "#,
    );
}
