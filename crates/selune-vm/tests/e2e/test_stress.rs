use super::helpers::*;

// ==========================================================================
// 3B. Stress Tests — boundary conditions and resource limits
// ==========================================================================

#[test]
fn stress_tail_call_deep_recursion() {
    run_lua(
        r#"
        local function f(n) if n > 0 then return f(n-1) end return 0 end
        assert(f(1000000) == 0)
        "#,
    );
}

#[test]
fn stress_non_tail_recursion_overflow_caught() {
    run_lua(
        r#"
        local function f(n) return f(n + 1) + n end
        local ok, msg = pcall(f, 0)
        assert(not ok)
        "#,
    );
}

#[test]
fn stress_large_table() {
    run_lua(
        r#"
        local t = {}
        for i = 1, 100000 do
            t[i] = i
        end
        assert(#t == 100000)
        assert(t[1] == 1)
        assert(t[50000] == 50000)
        assert(t[100000] == 100000)
        "#,
    );
}

#[test]
fn stress_string_concatenation() {
    run_lua(
        r#"
        local parts = {}
        for i = 1, 1000 do
            parts[i] = "x"
        end
        local s = table.concat(parts)
        assert(#s == 1000)
        "#,
    );
}

#[test]
fn stress_many_closures() {
    run_lua(
        r#"
        local closures = {}
        for i = 1, 1000 do
            closures[i] = function() return i end
        end
        assert(closures[1]() == 1)
        assert(closures[500]() == 500)
        assert(closures[1000]() == 1000)
        "#,
    );
}

#[test]
fn stress_deep_index_chain() {
    run_lua(
        r#"
        local base = {val = 42}
        local current = base
        for i = 1, 100 do
            current = setmetatable({}, {__index = current})
        end
        assert(current.val == 42)
        "#,
    );
}

#[test]
fn stress_many_coroutines() {
    run_lua(
        r#"
        local coroutines = {}
        for i = 1, 100 do
            coroutines[i] = coroutine.create(function()
                coroutine.yield(i)
                return i * 2
            end)
        end
        for i = 1, 100 do
            local ok, v = coroutine.resume(coroutines[i])
            assert(ok and v == i)
        end
        for i = 1, 100 do
            local ok, v = coroutine.resume(coroutines[i])
            assert(ok and v == i * 2)
        end
        "#,
    );
}

#[test]
fn stress_long_pattern_match() {
    run_lua(
        r#"
        local parts = {}
        for i = 1, 10000 do
            parts[i] = "a"
        end
        local s = table.concat(parts)
        assert(string.find(s, "aaa") == 1)
        assert(string.find(s, "b") == nil)
        assert(#s == 10000)
        "#,
    );
}

#[test]
fn stress_deeply_nested_tables() {
    run_lua(
        r#"
        local t = {val = 42}
        for i = 1, 100 do
            t = {inner = t}
        end
        -- Navigate back down
        local current = t
        for i = 1, 100 do
            current = current.inner
        end
        assert(current.val == 42)
        "#,
    );
}

#[test]
fn stress_gc_under_pressure() {
    run_lua(
        r#"
        collectgarbage("collect")
        local before = collectgarbage("count")
        for i = 1, 10000 do
            local t = {i, i*2, i*3, i*4}
        end
        collectgarbage("collect")
        local after = collectgarbage("count")
        -- Memory should not have grown unboundedly
        assert(after < before + 1000)
        "#,
    );
}

#[test]
fn stress_many_string_operations() {
    run_lua(
        r#"
        local t = {}
        for i = 1, 100 do
            t[i] = string.format("item_%04d", i)
        end
        assert(t[1] == "item_0001")
        assert(t[100] == "item_0100")
        assert(#t == 100)
        "#,
    );
}

#[test]
fn stress_nested_pcall() {
    run_lua(
        r#"
        local function nested_pcall(n)
            if n <= 0 then return 42 end
            local ok, val = pcall(nested_pcall, n - 1)
            assert(ok)
            return val
        end
        assert(nested_pcall(20) == 42)
        "#,
    );
}

#[test]
fn stress_many_table_sorts() {
    run_lua(
        r#"
        for i = 1, 100 do
            local t = {}
            for j = 1, 50 do
                t[j] = 51 - j
            end
            table.sort(t)
            assert(t[1] == 1 and t[50] == 50)
        end
        "#,
    );
}

#[test]
fn stress_large_table_with_hash() {
    run_lua(
        r#"
        local t = {}
        for i = 1, 10000 do
            t["key_" .. i] = i
        end
        assert(t["key_1"] == 1)
        assert(t["key_5000"] == 5000)
        assert(t["key_10000"] == 10000)
        "#,
    );
}

#[test]
fn stress_coroutine_ping_pong() {
    run_lua(
        r#"
        local co1, co2
        local result = {}
        co1 = coroutine.create(function()
            for i = 1, 50 do
                result[#result + 1] = "a" .. i
                coroutine.yield()
            end
        end)
        co2 = coroutine.create(function()
            for i = 1, 50 do
                result[#result + 1] = "b" .. i
                coroutine.yield()
            end
        end)
        for i = 1, 50 do
            coroutine.resume(co1)
            coroutine.resume(co2)
        end
        assert(#result == 100)
        assert(result[1] == "a1")
        assert(result[2] == "b1")
        "#,
    );
}

#[test]
fn stress_closure_chain() {
    run_lua(
        r#"
        local function make_adder(x)
            return function(y) return x + y end
        end
        local adders = {}
        for i = 1, 1000 do
            adders[i] = make_adder(i)
        end
        local sum = 0
        for i = 1, 1000 do
            sum = sum + adders[i](0)
        end
        assert(sum == 500500)  -- 1+2+...+1000
        "#,
    );
}

#[test]
fn stress_fibonacci_large() {
    run_lua(
        r#"
        local function fib(n)
            if n <= 1 then return n end
            local a, b = 0, 1
            for i = 2, n do
                a, b = b, a + b
            end
            return b
        end
        assert(fib(50) == 12586269025)
        assert(fib(0) == 0)
        assert(fib(1) == 1)
        "#,
    );
}

#[test]
fn stress_gsub_many_replacements() {
    run_lua(
        r#"
        local parts = {}
        for i = 1, 500 do
            parts[i] = "abc"
        end
        local s = table.concat(parts, " ")
        local result, count = string.gsub(s, "abc", "xyz")
        assert(count == 500)
        "#,
    );
}

#[test]
fn stress_table_insert_remove_many() {
    run_lua(
        r#"
        local t = {}
        for i = 1, 1000 do
            table.insert(t, i)
        end
        assert(#t == 1000)
        for i = 1, 500 do
            table.remove(t)
        end
        assert(#t == 500)
        assert(t[1] == 1 and t[500] == 500)
        "#,
    );
}
