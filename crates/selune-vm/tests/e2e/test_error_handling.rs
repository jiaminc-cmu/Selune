use super::helpers::*;

// ── error() basics ──────────────────────────────────────────────

#[test]
fn test_error_string() {
    // error() throws the value — pcall catches it and we check the string content
    run_check_strings(
        r#"
        local ok, msg = pcall(function() error("something went wrong") end)
        return msg
        "#,
        &["test:2: something went wrong"],
    );
}

#[test]
fn test_error_number() {
    let err = run_lua_err("error(42)");
    // error(42) throws the integer 42
    assert!(err.contains("42"), "got: {err}");
}

#[test]
fn test_error_nil() {
    let err = run_lua_err("error()");
    assert!(err.contains("nil") || err.contains("Nil"), "got: {err}");
}

// ── pcall basics ────────────────────────────────────────────────

#[test]
fn test_pcall_success() {
    run_check_ints(
        r#"
        local ok, val = pcall(function() return 42 end)
        if ok then return val else return -1 end
        "#,
        &[42],
    );
}

#[test]
fn test_pcall_success_multiple_results() {
    run_check_ints(
        r#"
        local ok, a, b = pcall(function() return 10, 20 end)
        if ok then return a, b else return -1 end
        "#,
        &[10, 20],
    );
}

#[test]
fn test_pcall_success_with_args() {
    run_check_ints(
        r#"
        local ok, val = pcall(function(x, y) return x + y end, 10, 20)
        if ok then return val else return -1 end
        "#,
        &[30],
    );
}

#[test]
fn test_pcall_catches_error_string() {
    run_check_strings(
        r#"
        local ok, msg = pcall(function() error("boom") end)
        if ok then return "bad" else return msg end
        "#,
        &["test:2: boom"],
    );
}

#[test]
fn test_pcall_returns_false_on_error() {
    run_check_ints(
        r#"
        local ok, msg = pcall(function() error("boom") end)
        if ok then return 1 else return 0 end
        "#,
        &[0],
    );
}

#[test]
fn test_pcall_catches_error_number() {
    run_check_ints(
        r#"
        local ok, val = pcall(function() error(42) end)
        if ok then return -1 else return val end
        "#,
        &[42],
    );
}

#[test]
fn test_pcall_catches_runtime_error() {
    // Calling nil should error
    run_check_ints(
        r#"
        local ok, msg = pcall(function()
            local x = nil
            x()
        end)
        if ok then return 1 else return 0 end
        "#,
        &[0],
    );
}

#[test]
fn test_pcall_catches_arithmetic_error() {
    run_check_ints(
        r#"
        local ok, msg = pcall(function()
            local x = "hello"
            return x + 1
        end)
        if ok then return 1 else return 0 end
        "#,
        &[0],
    );
}

#[test]
fn test_pcall_no_args_function() {
    run_check_ints(
        r#"
        local ok = pcall(function() end)
        if ok then return 1 else return 0 end
        "#,
        &[1],
    );
}

#[test]
fn test_pcall_catches_stack_overflow() {
    run_check_ints(
        r#"
        local function f(n) return f(n + 1) + n end
        local ok, msg = pcall(f, 0)
        if ok then return 1 else return 0 end
        "#,
        &[0],
    );
}

// ── pcall nested ────────────────────────────────────────────────

#[test]
fn test_pcall_nested() {
    run_check_ints(
        r#"
        local ok1, result = pcall(function()
            local ok2, val = pcall(function()
                error("inner")
            end)
            if ok2 then return -1 end
            return 42
        end)
        if ok1 then return result else return -1 end
        "#,
        &[42],
    );
}

#[test]
fn test_pcall_nested_inner_succeeds() {
    run_check_ints(
        r#"
        local ok1, result = pcall(function()
            local ok2, val = pcall(function() return 10 end)
            if ok2 then return val + 5 else return -1 end
        end)
        if ok1 then return result else return -1 end
        "#,
        &[15],
    );
}

#[test]
fn test_pcall_nested_outer_catches() {
    run_check_ints(
        r#"
        local ok, msg = pcall(function()
            pcall(function() end)  -- inner succeeds
            error("outer error")
        end)
        if ok then return 1 else return 0 end
        "#,
        &[0],
    );
}

// ── xpcall basics ───────────────────────────────────────────────

#[test]
fn test_xpcall_success() {
    run_check_ints(
        r#"
        local ok, val = xpcall(function() return 42 end, function(e) return e end)
        if ok then return val else return -1 end
        "#,
        &[42],
    );
}

#[test]
fn test_xpcall_error_with_handler() {
    run_check_strings(
        r#"
        local ok, val = xpcall(
            function() error("oops") end,
            function(e) return "handled: " .. e end
        )
        if ok then return "bad" else return val end
        "#,
        &["handled: test:3: oops"],
    );
}

#[test]
fn test_xpcall_handler_receives_error() {
    run_check_ints(
        r#"
        local ok, val = xpcall(
            function() error(99) end,
            function(e) return e + 1 end
        )
        if ok then return -1 else return val end
        "#,
        &[100],
    );
}

#[test]
fn test_xpcall_handler_error() {
    // Handler itself errors — returns false + handler's error
    run_check_ints(
        r#"
        local ok, val = xpcall(
            function() error("first") end,
            function(e) error("handler_error") end
        )
        if ok then return 1 else return 0 end
        "#,
        &[0],
    );
}

#[test]
fn test_xpcall_success_with_args() {
    run_check_ints(
        r#"
        local ok, val = xpcall(
            function(x, y) return x * y end,
            function(e) return e end,
            6, 7
        )
        if ok then return val else return -1 end
        "#,
        &[42],
    );
}

#[test]
fn test_xpcall_multiple_results() {
    run_check_ints(
        r#"
        local ok, a, b = xpcall(
            function() return 10, 20 end,
            function(e) return e end
        )
        if ok then return a, b else return -1 end
        "#,
        &[10, 20],
    );
}

// ── error + pcall with metamethods ──────────────────────────────

#[test]
fn test_pcall_catches_metamethod_error() {
    run_check_ints(
        r#"
        local t = setmetatable({}, {
            __add = function(a, b) error("cannot add") end
        })
        local ok = pcall(function() return t + 1 end)
        if ok then return 1 else return 0 end
        "#,
        &[0],
    );
}

#[test]
fn test_pcall_with_error_table() {
    // error() can throw a table
    run_check_ints(
        r#"
        local ok, err = pcall(function()
            error({code=404, msg="not found"})
        end)
        if ok then return -1 end
        return err.code
        "#,
        &[404],
    );
}

// ── error in various contexts caught by pcall ───────────────────

#[test]
fn test_pcall_catches_index_error() {
    run_check_ints(
        r#"
        local ok = pcall(function()
            local x = 42
            return x.foo
        end)
        if ok then return 1 else return 0 end
        "#,
        &[0],
    );
}

#[test]
fn test_pcall_catches_division_by_zero() {
    run_check_ints(
        r#"
        local ok = pcall(function()
            return 1 // 0
        end)
        if ok then return 1 else return 0 end
        "#,
        &[0],
    );
}

#[test]
fn test_pcall_preserves_state() {
    // After pcall catches an error, outer state is preserved
    run_check_ints(
        r#"
        local x = 10
        local ok = pcall(function()
            x = 20
            error("boom")
        end)
        return x
        "#,
        &[20],
    );
}

#[test]
fn test_pcall_error_boolean() {
    // error(false) throws false
    run_check_ints(
        r#"
        local ok, val = pcall(function() error(false) end)
        if ok then return -1 end
        if val == false then return 1 else return 0 end
        "#,
        &[1],
    );
}

// ── assert interacting with pcall ───────────────────────────────

#[test]
fn test_pcall_catches_assert_failure() {
    run_check_ints(
        r#"
        local ok = pcall(function()
            assert(false, "assertion failed")
        end)
        if ok then return 1 else return 0 end
        "#,
        &[0],
    );
}

#[test]
fn test_pcall_assert_success() {
    run_check_ints(
        r#"
        local ok, val = pcall(function()
            return assert(42)
        end)
        if ok then return val else return -1 end
        "#,
        &[42],
    );
}

// ── Additional gap-fill tests (Tier 2D) ────────────────────────

#[test]
fn test_error_with_no_args() {
    let err = run_lua_err("error()");
    // error() with no args should throw nil
    assert!(err.contains("nil") || err.contains("Nil"), "got: {err}");
}

#[test]
fn test_error_with_level_0() {
    // level 0 means no position info
    run_check_strings(
        r#"
        local ok, msg = pcall(error, "raw message", 0)
        return msg
        "#,
        &["raw message"],
    );
}

#[test]
fn test_pcall_nested_both_error() {
    run_check_ints(
        r#"
        local ok1, result = pcall(function()
            local ok2, msg = pcall(function()
                error("inner error")
            end)
            if ok2 then return -1 end
            error("outer error")
        end)
        if ok1 then return 1 else return 0 end
        "#,
        &[0],
    );
}

#[test]
fn test_xpcall_handler_receives_original() {
    run_check_ints(
        r#"
        local handler_called = false
        local ok, val = xpcall(
            function() error(42) end,
            function(e)
                handler_called = true
                return e * 2
            end
        )
        if ok then return -1 end
        if handler_called then return val else return -1 end
        "#,
        &[84],
    );
}

#[test]
fn test_pcall_error_nil_value() {
    run_check_ints(
        r#"
        local ok, msg = pcall(error, nil)
        if ok then return 1 end
        if msg == nil then return 0 else return -1 end
        "#,
        &[0],
    );
}

#[test]
fn test_assert_nil_errors() {
    run_check_ints(
        r#"
        local ok = pcall(assert, nil)
        if ok then return 1 else return 0 end
        "#,
        &[0],
    );
}

#[test]
fn test_assert_false_with_message() {
    run_check_strings(
        r#"
        local ok, msg = pcall(assert, false, "custom error")
        return msg
        "#,
        &["custom error"],
    );
}

#[test]
fn test_assert_false_default_message() {
    run_check_strings(
        r#"
        local ok, msg = pcall(assert, false)
        return msg
        "#,
        &["assertion failed!"],
    );
}

#[test]
fn test_assert_truthy_returns_value() {
    run_check_ints(
        r#"
        local v = assert(42)
        return v
        "#,
        &[42],
    );
}

#[test]
fn test_pcall_catches_concat_error() {
    run_check_ints(
        r#"
        local ok = pcall(function()
            return {} .. "hello"
        end)
        if ok then return 1 else return 0 end
        "#,
        &[0],
    );
}

#[test]
fn test_pcall_catches_comparison_error() {
    run_check_ints(
        r#"
        local ok = pcall(function()
            return {} < {}
        end)
        if ok then return 1 else return 0 end
        "#,
        &[0],
    );
}

#[test]
fn test_pcall_with_varargs() {
    run_check_ints(
        r#"
        local function sum(...)
            local s = 0
            for i = 1, select('#', ...) do
                s = s + select(i, ...)
            end
            return s
        end
        local ok, val = pcall(sum, 1, 2, 3, 4, 5)
        if ok then return val else return -1 end
        "#,
        &[15],
    );
}

#[test]
fn test_error_in_metamethod_caught_by_pcall() {
    run_check_ints(
        r#"
        local t = setmetatable({}, {
            __index = function(t, k)
                error("no such key: " .. k)
            end
        })
        local ok, msg = pcall(function() return t.foo end)
        if ok then return 1 else return 0 end
        "#,
        &[0],
    );
}

#[test]
fn test_deeply_nested_pcall_error() {
    run_check_ints(
        r#"
        local result = 0
        local ok = pcall(function()
            pcall(function()
                pcall(function()
                    error("deep error")
                end)
                result = 1
            end)
            result = result + 10
        end)
        return result
        "#,
        &[11],
    );
}

#[test]
fn test_xpcall_success_returns_all_values() {
    run_check_ints(
        r#"
        local ok, a, b, c = xpcall(
            function() return 1, 2, 3 end,
            function(e) return e end
        )
        if ok then return a, b, c else return -1 end
        "#,
        &[1, 2, 3],
    );
}
