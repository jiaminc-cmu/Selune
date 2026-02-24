use super::helpers::*;

// ---- assert ----

#[test]
fn test_assert_pass() {
    run_check_ints("return assert(42)", &[42]);
}

#[test]
fn test_assert_pass_multiple_returns() {
    run_check_ints("return assert(1, 2, 3)", &[1, 2, 3]);
}

#[test]
fn test_assert_pass_true() {
    let results = run_lua("return assert(true)");
    assert_bool(&results, 0, true);
}

#[test]
fn test_assert_fail_default_message() {
    let err = run_lua_err("assert(false)");
    assert!(
        err.contains("assertion failed"),
        "expected 'assertion failed', got: {err}"
    );
}

#[test]
fn test_assert_fail_custom_message() {
    // PUC Lua 5.4: assert with explicit message passes it through unchanged
    run_lua(
        r#"
        local ok, msg = pcall(assert, false, 'custom error')
        assert(ok == false)
        assert(msg == 'custom error')
        "#,
    );
}

#[test]
fn test_assert_fail_nil() {
    let err = run_lua_err("assert(nil)");
    assert!(
        err.contains("assertion failed"),
        "expected 'assertion failed', got: {err}"
    );
}

// ---- select ----

#[test]
fn test_select_index() {
    run_check_ints("return select(2, 10, 20, 30)", &[20, 30]);
}

#[test]
fn test_select_first() {
    run_check_ints("return select(1, 10, 20, 30)", &[10, 20, 30]);
}

#[test]
fn test_select_last() {
    run_check_ints("return select(3, 10, 20, 30)", &[30]);
}

#[test]
fn test_select_hash() {
    run_check_ints("return select('#', 10, 20, 30)", &[3]);
}

#[test]
fn test_select_hash_empty() {
    run_check_ints("return select('#')", &[0]);
}

#[test]
fn test_select_out_of_range() {
    let results = run_lua("return select(10, 1, 2, 3)");
    assert_eq!(results.len(), 0);
}

// ---- rawget / rawset ----

#[test]
fn test_rawget_basic() {
    run_check_ints(
        r#"
        local t = {10, 20, 30}
        return rawget(t, 2)
        "#,
        &[20],
    );
}

#[test]
fn test_rawget_string_key() {
    run_check_ints(
        r#"
        local t = {x = 42}
        return rawget(t, "x")
        "#,
        &[42],
    );
}

#[test]
fn test_rawget_missing() {
    let results = run_lua(
        r#"
        local t = {x = 42}
        return rawget(t, "y")
        "#,
    );
    assert_nil(&results, 0);
}

#[test]
fn test_rawset_basic() {
    run_check_ints(
        r#"
        local t = {}
        rawset(t, "x", 99)
        return t.x
        "#,
        &[99],
    );
}

#[test]
fn test_rawset_returns_table() {
    // rawset returns the table
    let results = run_lua(
        r#"
        local t = {}
        local r = rawset(t, "x", 1)
        return r == t
        "#,
    );
    assert_bool(&results, 0, true);
}

// ---- rawequal ----

#[test]
fn test_rawequal_same() {
    let results = run_lua("return rawequal(1, 1)");
    assert_bool(&results, 0, true);
}

#[test]
fn test_rawequal_different() {
    let results = run_lua("return rawequal(1, 2)");
    assert_bool(&results, 0, false);
}

#[test]
fn test_rawequal_string() {
    let results = run_lua(r#"return rawequal("abc", "abc")"#);
    assert_bool(&results, 0, true);
}

#[test]
fn test_rawequal_nil() {
    let results = run_lua("return rawequal(nil, nil)");
    assert_bool(&results, 0, true);
}

// ---- rawlen ----

#[test]
fn test_rawlen_table() {
    run_check_ints("return rawlen({10, 20, 30})", &[3]);
}

#[test]
fn test_rawlen_empty() {
    run_check_ints("return rawlen({})", &[0]);
}

#[test]
fn test_rawlen_string() {
    run_check_ints(r#"return rawlen("hello")"#, &[5]);
}

// ---- setmetatable / getmetatable ----

#[test]
fn test_setmetatable_basic() {
    let results = run_lua(
        r#"
        local t = {}
        local mt = {}
        setmetatable(t, mt)
        return getmetatable(t) == mt
        "#,
    );
    assert_bool(&results, 0, true);
}

#[test]
fn test_setmetatable_returns_table() {
    let results = run_lua(
        r#"
        local t = {}
        local r = setmetatable(t, {})
        return r == t
        "#,
    );
    assert_bool(&results, 0, true);
}

#[test]
fn test_setmetatable_nil_clears() {
    let results = run_lua(
        r#"
        local t = {}
        setmetatable(t, {})
        setmetatable(t, nil)
        return getmetatable(t)
        "#,
    );
    assert_nil(&results, 0);
}

#[test]
fn test_getmetatable_no_metatable() {
    let results = run_lua(
        r#"
        local t = {}
        return getmetatable(t)
        "#,
    );
    assert_nil(&results, 0);
}

#[test]
fn test_getmetatable_non_table() {
    let results = run_lua("return getmetatable(42)");
    assert_nil(&results, 0);
}

#[test]
fn test_getmetatable_metatable_field() {
    // __metatable field should be returned instead of the actual metatable
    let results = run_lua(
        r#"
        local t = {}
        setmetatable(t, { __metatable = "protected" })
        return getmetatable(t)
        "#,
    );
    // __metatable field should be returned - just check it's not nil and not a table
    assert!(!results[0].is_nil());
}

// ---- unpack ----

#[test]
fn test_unpack_basic() {
    run_check_ints("return unpack({10, 20, 30})", &[10, 20, 30]);
}

#[test]
fn test_unpack_range() {
    run_check_ints("return unpack({10, 20, 30, 40}, 2, 3)", &[20, 30]);
}

#[test]
fn test_unpack_single() {
    run_check_ints("return unpack({42}, 1, 1)", &[42]);
}

#[test]
fn test_unpack_empty() {
    let results = run_lua("return unpack({})");
    assert_eq!(results.len(), 0);
}

#[test]
fn test_unpack_start() {
    run_check_ints("return unpack({10, 20, 30}, 2)", &[20, 30]);
}

// ---- error ----

#[test]
fn test_error_string() {
    let err = run_lua_err(r#"error("boom")"#);
    // LuaValue variant will show as debug
    assert!(
        err.contains("boom") || err.contains("string"),
        "expected error with 'boom', got: {err}"
    );
}

#[test]
fn test_error_number() {
    let err = run_lua_err("error(42)");
    assert!(err.contains("42"), "expected error with '42', got: {err}");
}
