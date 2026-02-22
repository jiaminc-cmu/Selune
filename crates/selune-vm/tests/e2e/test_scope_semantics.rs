use super::helpers::*;

// ==========================================================================
// 2F. Scope Semantics
// ==========================================================================

#[test]
fn scope_repeat_until_local_visible() {
    run_lua(
        r#"
        repeat
            local x = 1
        until x == 1
        "#,
    );
}

#[test]
fn scope_for_variable_is_local_per_iteration() {
    run_lua(
        r#"
        local fns = {}
        for i = 1, 5 do
            fns[i] = function() return i end
        end
        assert(fns[1]() == 1)
        assert(fns[2]() == 2)
        assert(fns[5]() == 5)
        "#,
    );
}

#[test]
fn scope_do_end_block() {
    run_lua(
        r#"
        local x = 1
        do
            local x = 2
            assert(x == 2)
        end
        assert(x == 1)
        "#,
    );
}

#[test]
fn scope_local_function_recursion() {
    run_lua(
        r#"
        local function fact(n)
            if n <= 1 then return 1 end
            return n * fact(n - 1)
        end
        assert(fact(5) == 120)
        "#,
    );
}

#[test]
fn scope_forward_reference_via_upvalue() {
    run_lua(
        r#"
        local f
        local g = function() return f() end
        f = function() return 42 end
        assert(g() == 42)
        "#,
    );
}

#[test]
fn scope_shadow_same_scope() {
    run_lua(
        r#"
        local x = 1
        local x = 2
        assert(x == 2)
        "#,
    );
}

#[test]
fn scope_nested_functions() {
    run_lua(
        r#"
        local function outer()
            local x = 10
            local function inner()
                local y = 20
                return x + y
            end
            return inner()
        end
        assert(outer() == 30)
        "#,
    );
}

#[test]
fn scope_for_in_variable_local() {
    run_lua(
        r#"
        local captured = {}
        for i, v in ipairs({10, 20, 30}) do
            captured[i] = function() return v end
        end
        assert(captured[1]() == 10)
        assert(captured[2]() == 20)
        assert(captured[3]() == 30)
        "#,
    );
}

#[test]
fn scope_while_body_is_scoped() {
    run_lua(
        r#"
        local n = 3
        while n > 0 do
            local x = n
            n = n - 1
        end
        -- x is not accessible here
        local ok = pcall(function() return x end)
        -- x is nil (global), so this won't error but will be nil
        assert(x == nil)
        "#,
    );
}

#[test]
fn scope_multiple_return_assignment() {
    run_lua(
        r#"
        local function f() return 1, 2 end
        local a, b = f()
        assert(a == 1 and b == 2)
        -- Ensure they are actually separate variables
        a = 10
        assert(b == 2)
        "#,
    );
}

#[test]
fn scope_nested_for_loops() {
    run_lua(
        r#"
        local result = 0
        for i = 1, 3 do
            for j = 1, 3 do
                result = result + i * j
            end
        end
        assert(result == 36)  -- (1+2+3)*(1+2+3)
        "#,
    );
}

#[test]
fn scope_local_in_if_branch() {
    run_lua(
        r#"
        if true then
            local x = 42
            assert(x == 42)
        end
        assert(x == nil)  -- x not visible outside
        "#,
    );
}

#[test]
fn scope_upvalue_from_enclosing_scope() {
    run_lua(
        r#"
        local x = 100
        local function f()
            local function g()
                return x
            end
            return g()
        end
        assert(f() == 100)
        x = 200
        assert(f() == 200)
        "#,
    );
}

#[test]
fn scope_for_loop_var_not_visible_outside() {
    run_lua(
        r#"
        for i = 1, 3 do end
        assert(i == nil)
        "#,
    );
}

#[test]
fn scope_generic_for_vars_not_visible_outside() {
    run_lua(
        r#"
        for k, v in pairs({a=1}) do end
        assert(k == nil and v == nil)
        "#,
    );
}

#[test]
fn scope_do_end_sequential() {
    run_lua(
        r#"
        local result = 0
        do
            local x = 10
            result = result + x
        end
        do
            local x = 20
            result = result + x
        end
        assert(result == 30)
        "#,
    );
}

#[test]
fn scope_closure_captures_latest_value() {
    run_lua(
        r#"
        local x = 1
        local function f() return x end
        x = 2
        assert(f() == 2)
        x = 3
        assert(f() == 3)
        "#,
    );
}

#[test]
fn scope_parameter_shadows_outer() {
    run_lua(
        r#"
        local x = 10
        local function f(x)
            return x
        end
        assert(f(20) == 20)
        assert(x == 10)
        "#,
    );
}

#[test]
fn scope_deeply_nested_upvalues() {
    run_lua(
        r#"
        local function level1()
            local a = 1
            return function()
                local b = 2
                return function()
                    local c = 3
                    return function()
                        return a + b + c
                    end
                end
            end
        end
        assert(level1()()()() == 6)
        "#,
    );
}
