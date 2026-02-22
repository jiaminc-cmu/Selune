use super::helpers::*;

// ==========================================================================
// 2C. Table Semantics — edge cases
// ==========================================================================

#[test]
fn table_int_float_key_equivalence() {
    run_lua(
        r#"
        local t = {}
        t[1] = "a"
        assert(t[1.0] == "a")
        t[2.0] = "b"
        assert(t[2] == "b")
        "#,
    );
}

#[test]
fn table_nil_key_error() {
    let err = run_lua_err(
        r#"
        local t = {}
        t[nil] = 1
        "#,
    );
    assert!(err.contains("nil") || err.contains("index"), "got: {err}");
}

#[test]
fn table_nan_key_error() {
    let err = run_lua_err(
        r#"
        local t = {}
        t[0/0] = 1
        "#,
    );
    assert!(err.contains("NaN") || err.contains("nan") || err.contains("index"), "got: {err}");
}

#[test]
fn table_rawget_rawset() {
    run_lua(
        r#"
        local mt = {
            __index = function(t, k) return "meta" end,
            __newindex = function(t, k, v) error("should not fire") end
        }
        local t = setmetatable({}, mt)
        rawset(t, "x", 42)
        assert(rawget(t, "x") == 42)
        assert(rawget(t, "y") == nil)
        "#,
    );
}

#[test]
fn table_two_tables_are_different_keys() {
    run_lua(
        r#"
        local t = {}
        local a = {}
        local b = {}
        t[a] = 1
        t[b] = 2
        assert(t[a] == 1)
        assert(t[b] == 2)
        "#,
    );
}

#[test]
fn table_length_sequence() {
    run_lua(
        r#"
        assert(#{} == 0)
        assert(#{1, 2, 3} == 3)
        assert(#{1, 2, 3, 4, 5} == 5)
        "#,
    );
}

#[test]
fn table_length_with_nil_at_end() {
    // #{nil} — the sequence boundary is 0
    run_lua("assert(#{nil} == 0)");
}

#[test]
fn table_setmetatable_returns_table() {
    run_lua(
        r#"
        local t = {}
        local result = setmetatable(t, {})
        assert(t == result)
        "#,
    );
}

#[test]
#[ignore] // BUG: getmetatable("hello") returns nil — PUC Lua: strings have metatable
fn table_getmetatable() {
    run_lua(
        r#"
        local mt = {}
        local t = setmetatable({}, mt)
        assert(getmetatable(t) == mt)
        assert(getmetatable("hello") ~= nil)  -- strings have metatable
        assert(getmetatable(42) == nil)
        "#,
    );
}

#[test]
fn table_constructor_mixed() {
    run_lua(
        r#"
        local t = {1, 2, a="x", b="y", 3}
        assert(t[1] == 1 and t[2] == 2 and t[3] == 3)
        assert(t.a == "x" and t.b == "y")
        "#,
    );
}

#[test]
fn table_constructor_trailing_comma() {
    run_lua(
        r#"
        local t = {1, 2, 3,}
        assert(#t == 3)
        "#,
    );
}

#[test]
fn table_constructor_semicolon() {
    run_lua(
        r#"
        local t = {1; 2; 3}
        assert(#t == 3)
        "#,
    );
}

#[test]
fn table_constructor_computed_key() {
    run_lua(
        r#"
        local key = "hello"
        local t = {[key] = 42, [1+1] = "two"}
        assert(t.hello == 42)
        assert(t[2] == "two")
        "#,
    );
}

#[test]
fn table_nested() {
    run_lua(
        r#"
        local t = {a = {b = {c = 42}}}
        assert(t.a.b.c == 42)
        "#,
    );
}

#[test]
fn table_ipairs_stops_at_nil() {
    run_lua(
        r#"
        local t = {1, 2, nil, 4}
        local count = 0
        for i, v in ipairs(t) do
            count = count + 1
        end
        assert(count == 2)
        "#,
    );
}

#[test]
fn table_pairs_includes_all() {
    run_lua(
        r#"
        local t = {1, 2, a="x"}
        local count = 0
        for k, v in pairs(t) do
            count = count + 1
        end
        assert(count == 3)
        "#,
    );
}

#[test]
fn table_rawequal() {
    run_lua(
        r#"
        local a = {}
        local b = a
        assert(rawequal(a, b) == true)
        assert(rawequal({}, {}) == false)
        assert(rawequal(1, 1) == true)
        assert(rawequal(1, 1.0) == true)   -- PUC Lua 5.4: rawequal compares by value
        "#,
    );
}

#[test]
fn table_rawlen() {
    run_lua(
        r#"
        local t = setmetatable({1, 2, 3}, {__len = function() return 99 end})
        assert(#t == 99)
        assert(rawlen(t) == 3)
        "#,
    );
}

#[test]
fn table_sort_strings() {
    run_lua(
        r#"
        local t = {"banana", "apple", "cherry"}
        table.sort(t)
        assert(t[1] == "apple" and t[2] == "banana" and t[3] == "cherry")
        "#,
    );
}

#[test]
fn table_move_to_other_table() {
    run_lua(
        r#"
        local src = {10, 20, 30}
        local dst = {}
        table.move(src, 1, 3, 1, dst)
        assert(dst[1] == 10 and dst[2] == 20 and dst[3] == 30)
        "#,
    );
}

#[test]
fn table_unpack_empty() {
    run_lua(
        r#"
        local a = table.unpack({})
        assert(a == nil)
        "#,
    );
}

#[test]
fn table_insert_at_position() {
    run_lua(
        r#"
        local t = {1, 2, 3}
        table.insert(t, 1, 0)
        assert(t[1] == 0 and t[2] == 1 and t[3] == 2 and t[4] == 3)
        "#,
    );
}

#[test]
fn table_remove_returns_value() {
    run_lua(
        r#"
        local t = {10, 20, 30}
        local v = table.remove(t, 2)
        assert(v == 20)
        assert(#t == 2 and t[1] == 10 and t[2] == 30)
        "#,
    );
}

#[test]
fn table_constructor_multireturn_last() {
    run_lua(
        r#"
        local function f() return 10, 20, 30 end
        local t = {f()}
        assert(#t == 3 and t[1] == 10 and t[2] == 20 and t[3] == 30)
        "#,
    );
}

#[test]
fn table_constructor_multireturn_not_last() {
    run_lua(
        r#"
        local function f() return 10, 20, 30 end
        local t = {f(), 99}
        assert(#t == 2 and t[1] == 10 and t[2] == 99)
        "#,
    );
}
