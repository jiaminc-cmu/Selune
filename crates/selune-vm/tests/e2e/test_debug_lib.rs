/// Tests for the debug library.
use super::helpers::*;

// ---- debug.getmetatable / debug.setmetatable ----

#[test]
fn test_debug_getmetatable_table() {
    let (results, _) = run_with_vm(
        r#"
        local t = {}
        local mt = {}
        setmetatable(t, mt)
        return debug.getmetatable(t) == mt
        "#,
    );
    assert_bool(&results, 0, true);
}

#[test]
fn test_debug_getmetatable_no_mt() {
    let (results, _) = run_with_vm(
        r#"
        local t = {}
        return debug.getmetatable(t) == nil
        "#,
    );
    assert_bool(&results, 0, true);
}

#[test]
fn test_debug_getmetatable_bypasses_metatable_field() {
    let (results, _) = run_with_vm(
        r#"
        local t = {}
        local mt = { __metatable = "hidden" }
        setmetatable(t, mt)
        -- getmetatable(t) would return "hidden", but debug.getmetatable returns the real mt
        return debug.getmetatable(t) == mt
        "#,
    );
    assert_bool(&results, 0, true);
}

#[test]
fn test_debug_setmetatable() {
    let (results, _) = run_with_vm(
        r#"
        local t = {}
        local mt = { __index = function() return 42 end }
        debug.setmetatable(t, mt)
        return t.anything
        "#,
    );
    assert_int(&results, 0, 42);
}

#[test]
fn test_debug_setmetatable_nil() {
    let (results, _) = run_with_vm(
        r#"
        local t = {}
        local mt = {}
        setmetatable(t, mt)
        debug.setmetatable(t, nil)
        return debug.getmetatable(t) == nil
        "#,
    );
    assert_bool(&results, 0, true);
}

// ---- debug.getupvalue / debug.setupvalue ----

#[test]
fn test_debug_getupvalue_closed() {
    // After the closure escapes and the local scope ends, the upvalue is closed
    let (results, _vm) = run_with_vm(
        r#"
        local function make()
            local x = 99
            return function() return x end
        end
        local f = make()
        local name, val = debug.getupvalue(f, 1)
        return name ~= nil, val
        "#,
    );
    assert_bool(&results, 0, true);
    assert_int(&results, 1, 99);
}

#[test]
fn test_debug_getupvalue_out_of_range() {
    let (results, _) = run_with_vm(
        r#"
        local function make()
            local x = 1
            return function() return x end
        end
        local f = make()
        return debug.getupvalue(f, 99)
        "#,
    );
    assert_nil(&results, 0);
}

#[test]
fn test_debug_setupvalue_closed() {
    run_check_ints(
        r#"
        local function make()
            local x = 10
            return function() return x end
        end
        local f = make()
        debug.setupvalue(f, 1, 42)
        return f()
        "#,
        &[42],
    );
}

// ---- debug.upvalueid / debug.upvaluejoin ----

#[test]
fn test_debug_upvalueid_same() {
    // Two closures created in same scope share the same upvalue
    let (results, _) = run_with_vm(
        r#"
        local function make()
            local x = 1
            local f = function() return x end
            local g = function() return x end
            return f, g
        end
        local f, g = make()
        return debug.upvalueid(f, 1) == debug.upvalueid(g, 1)
        "#,
    );
    assert_bool(&results, 0, true);
}

#[test]
fn test_debug_upvalueid_different() {
    // Two independent closures have different upvalues
    let (results, _) = run_with_vm(
        r#"
        local function make1()
            local x = 1
            return function() return x end
        end
        local function make2()
            local x = 2
            return function() return x end
        end
        local f = make1()
        local g = make2()
        return debug.upvalueid(f, 1) ~= debug.upvalueid(g, 1)
        "#,
    );
    assert_bool(&results, 0, true);
}

#[test]
fn test_debug_upvaluejoin() {
    // After joining, f1's upvalue should point to f2's upvalue
    run_check_ints(
        r#"
        local function make1()
            local x = 10
            return function() return x end
        end
        local function make2()
            local y = 99
            return function() return y end
        end
        local f = make1()
        local g = make2()
        debug.upvaluejoin(f, 1, g, 1)
        return f()
        "#,
        &[99],
    );
}

// ---- debug.getinfo (stub) ----

#[test]
fn test_debug_getinfo_returns_table() {
    run_check_strings(
        r#"
        local info = debug.getinfo(print)
        return type(info)
        "#,
        &["table"],
    );
}

// ---- debug.traceback ----

#[test]
fn test_debug_traceback_returns_message() {
    let (results, vm) = run_with_vm(
        r#"
        return debug.traceback("hello")
        "#,
    );
    let sid = results[0].as_string_id().expect("expected string");
    let s = std::str::from_utf8(vm.strings.get_bytes(sid)).unwrap();
    assert!(s.starts_with("hello"), "traceback should start with message, got: {s}");
    assert!(s.contains("stack traceback:"), "traceback should contain stack info, got: {s}");
}

#[test]
fn test_debug_traceback_nil_returns_empty() {
    let (results, vm) = run_with_vm(
        r#"
        return debug.traceback()
        "#,
    );
    let sid = results[0].as_string_id().expect("expected string");
    let s = std::str::from_utf8(vm.strings.get_bytes(sid)).unwrap();
    assert!(s.contains("stack traceback:"), "traceback should contain stack info, got: {s}");
}

// ---- debug.sethook (stub, no-op) ----

#[test]
fn test_debug_sethook_noop() {
    let results = run_lua(
        r#"
        debug.sethook(function() end, "c")
        return 1
        "#,
    );
    assert_int(&results, 0, 1);
}

// ---- debug type check ----

#[test]
fn test_debug_is_table() {
    run_check_strings("return type(debug)", &["table"]);
}

