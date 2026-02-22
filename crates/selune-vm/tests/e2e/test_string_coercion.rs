use super::helpers::*;

// ==========================================================================
// 2B. String/Number Coercion Tests
// ==========================================================================

#[test]
fn coerce_string_integer_add() {
    run_lua(r#"assert("10" + 5 == 15)"#);
}

#[test]
fn coerce_string_float_add() {
    run_lua(r#"assert("10.5" + 5 == 15.5)"#);
}

#[test]
fn coerce_string_hex_add() {
    run_lua(r#"assert("0xff" + 0 == 255)"#);
}

#[test]
fn coerce_number_to_string_concat() {
    run_lua(r#"assert(10 .. "" == "10")"#);
}

#[test]
fn coerce_float_to_string_concat() {
    run_lua(r#"assert(10.0 .. "" == "10.0")"#);
}

#[test]
fn coerce_tostring_integer() {
    run_lua(r#"assert(tostring(10) == "10")"#);
}

#[test]
fn coerce_tostring_float() {
    run_lua(r#"assert(tostring(10.0) == "10.0")"#);
}

#[test]
fn coerce_tostring_nil() {
    run_lua(r#"assert(tostring(nil) == "nil")"#);
}

#[test]
fn coerce_tostring_bool() {
    run_lua(
        r#"
        assert(tostring(true) == "true")
        assert(tostring(false) == "false")
        "#,
    );
}

#[test]
fn coerce_string_to_number_sub() {
    run_lua(r#"assert("20" - 5 == 15)"#);
}

#[test]
fn coerce_string_to_number_mul() {
    run_lua(r#"assert("3" * 4 == 12)"#);
}

#[test]
fn coerce_string_to_number_div() {
    run_lua(r#"assert("10" / 2 == 5.0)"#);
}

#[test]
fn coerce_string_to_number_mod() {
    run_lua(r#"assert("10" % 3 == 1)"#);
}

#[test]
fn coerce_string_to_number_unm() {
    run_lua(r#"assert(-"5" == -5)"#);
}

#[test]
fn coerce_string_add_error() {
    let err = run_lua_err(r#"return "hello" + 1"#);
    assert!(
        err.contains("attempt to perform arithmetic"),
        "got: {err}"
    );
}

#[test]
fn coerce_concat_mixed() {
    run_lua(
        r#"
        assert("val=" .. 42 == "val=42")
        assert(42 .. "!" == "42!")
        assert(3.14 .. "x" == "3.14x")
        "#,
    );
}

#[test]
fn coerce_string_comparison_lexicographic() {
    run_lua(
        r#"
        assert("abc" < "abd")
        assert("abc" < "b")
        assert("abc" <= "abc")
        assert(not ("abc" < "abc"))
        "#,
    );
}

#[test]
fn coerce_string_number_no_compare() {
    // Comparing string with number should error (Lua 5.4)
    let err = run_lua_err(r#"return "10" < 10"#);
    assert!(err.contains("attempt to compare"), "got: {err}");
}

#[test]
fn coerce_string_whitespace_arithmetic() {
    run_lua(r#"assert("  42  " + 0 == 42)"#);
}

#[test]
fn coerce_string_scientific_notation() {
    run_lua(r#"assert("1e2" + 0 == 100.0)"#);
}
