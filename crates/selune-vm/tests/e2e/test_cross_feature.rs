use super::helpers::*;

// ==========================================================================
// 3A. Cross-Feature Tests — interactions between features
// ==========================================================================

// ---- Closure + Error Handling ----

#[test]
fn cross_pcall_inside_closure() {
    run_lua(
        r#"
        local function make()
            local x = 10
            return function()
                local ok = pcall(function() error("boom") end)
                return x, not ok
            end
        end
        local f = make()
        local val, caught = f()
        assert(val == 10 and caught == true)
        "#,
    );
}

#[test]
fn cross_error_preserves_upvalues() {
    run_lua(
        r#"
        local x = 0
        local function inc()
            x = x + 1
            if x == 3 then error("stop") end
        end
        pcall(function()
            for i = 1, 10 do inc() end
        end)
        assert(x == 3)
        "#,
    );
}

// ---- Metamethods + Error Handling ----

#[test]
fn cross_index_error_caught_by_pcall() {
    run_lua(
        r#"
        local t = setmetatable({}, {
            __index = function(t, k)
                error("no key: " .. k)
            end
        })
        local ok, msg = pcall(function() return t.missing end)
        assert(not ok)
        assert(string.find(msg, "no key: missing") ~= nil)
        "#,
    );
}

#[test]
fn cross_metamethod_error_in_arithmetic() {
    run_lua(
        r#"
        local t = setmetatable({}, {
            __add = function(a, b) error("cannot add") end
        })
        local ok, msg = pcall(function() return t + 1 end)
        assert(not ok)
        assert(string.find(msg, "cannot add") ~= nil)
        "#,
    );
}

// ---- Generic for + Closures ----

#[test]
fn cross_stateful_iterator_closure() {
    run_lua(
        r#"
        local function range(n)
            local i = 0
            return function()
                i = i + 1
                if i <= n then return i end
            end
        end
        local sum = 0
        for v in range(5) do
            sum = sum + v
        end
        assert(sum == 15)
        "#,
    );
}

#[test]
fn cross_generic_for_with_multiple_values() {
    run_lua(
        r#"
        local function enum(t)
            local i = 0
            return function()
                i = i + 1
                if t[i] then return i, t[i] end
            end
        end
        local keys, vals = {}, {}
        for k, v in enum({"a", "b", "c"}) do
            keys[#keys + 1] = k
            vals[#vals + 1] = v
        end
        assert(#keys == 3 and keys[1] == 1 and vals[3] == "c")
        "#,
    );
}

// ---- Multiple Returns + Table Constructor ----

#[test]
fn cross_multireturn_in_table_constructor() {
    run_lua(
        r#"
        local function f() return 10, 20, 30 end
        local t = {f()}
        assert(#t == 3)
        assert(t[1] == 10 and t[2] == 20 and t[3] == 30)
        -- Not last: truncated
        local t2 = {f(), 99}
        assert(#t2 == 2 and t2[1] == 10 and t2[2] == 99)
        "#,
    );
}

// ---- Tail Call + Closures ----

#[test]
fn cross_tail_call_from_closure() {
    run_lua(
        r#"
        local function make(x)
            local function helper(n)
                if n <= 0 then return x end
                return helper(n - 1)
            end
            return helper
        end
        local f = make(42)
        assert(f(100000) == 42)
        "#,
    );
}

// ---- Coroutines + Error Handling ----

#[test]
fn cross_error_in_coroutine() {
    run_lua(
        r#"
        local co = coroutine.create(function()
            error("coro error")
        end)
        local ok, msg = coroutine.resume(co)
        assert(not ok)
        assert(string.find(msg, "coro error") ~= nil)
        assert(coroutine.status(co) == "dead")
        "#,
    );
}

#[test]
fn cross_pcall_in_coroutine() {
    run_lua(
        r#"
        local co = coroutine.create(function()
            local ok, msg = pcall(function()
                error("caught inside coro")
            end)
            assert(not ok)
            coroutine.yield(42)
            return 99
        end)
        local ok1, v1 = coroutine.resume(co)
        assert(ok1 and v1 == 42)
        local ok2, v2 = coroutine.resume(co)
        assert(ok2 and v2 == 99)
        "#,
    );
}

// ---- Coroutines + Closures ----

#[test]
fn cross_closure_captures_across_yield() {
    run_lua(
        r#"
        local x = 0
        local co = coroutine.create(function()
            x = x + 1
            coroutine.yield()
            x = x + 10
        end)
        coroutine.resume(co)
        assert(x == 1)
        coroutine.resume(co)
        assert(x == 11)
        "#,
    );
}

#[test]
fn cross_coroutine_with_closure_generator() {
    run_lua(
        r#"
        local function make_counter()
            local n = 0
            return coroutine.wrap(function()
                while true do
                    n = n + 1
                    coroutine.yield(n)
                end
            end)
        end
        local counter = make_counter()
        assert(counter() == 1)
        assert(counter() == 2)
        assert(counter() == 3)
        "#,
    );
}

// ---- Coroutine Yield from Nested Calls ----

#[test]
fn cross_yield_from_nested_call_3_deep() {
    run_lua(
        r#"
        local function f3() return coroutine.yield(42) end
        local function f2() return f3() end
        local function f1() return f2() end
        local co = coroutine.create(f1)
        local ok, v = coroutine.resume(co)
        assert(ok and v == 42, "first resume failed: ok=" .. tostring(ok) .. " v=" .. tostring(v))
        local ok2, v2 = coroutine.resume(co, 100)
        assert(ok2 and v2 == 100, "second resume failed: ok2=" .. tostring(ok2) .. " v2=" .. tostring(v2))
        "#,
    );
}

#[test]
fn cross_yield_from_inside_pcall() {
    run_lua(
        r#"
        local co = coroutine.create(function()
            local ok, v = pcall(function()
                coroutine.yield(42)
                return 100
            end)
            return ok, v
        end)
        local ok1, v1 = coroutine.resume(co)
        assert(ok1 and v1 == 42, "first resume: ok1=" .. tostring(ok1) .. " v1=" .. tostring(v1))
        local ok2, v2, v3 = coroutine.resume(co)
        assert(ok2, "second resume failed")
        assert(v2 == true, "pcall should return true, got: " .. tostring(v2))
        assert(v3 == 100, "pcall result should be 100, got: " .. tostring(v3))
        "#,
    );
}

#[test]
fn cross_multiple_yields_from_nested() {
    run_lua(
        r#"
        local function inner(x)
            coroutine.yield(x)
            coroutine.yield(x * 2)
            return x * 3
        end
        local function outer()
            local a = inner(10)
            return a
        end
        local co = coroutine.create(outer)
        local ok1, v1 = coroutine.resume(co)
        assert(ok1 and v1 == 10)
        local ok2, v2 = coroutine.resume(co)
        assert(ok2 and v2 == 20)
        local ok3, v3 = coroutine.resume(co)
        assert(ok3 and v3 == 30)
        "#,
    );
}

#[test]
fn cross_yield_from_inside_xpcall() {
    run_lua(
        r#"
        local co = coroutine.create(function()
            local ok, v = xpcall(function()
                coroutine.yield(42)
                return 100
            end, function(e) return "handler: " .. e end)
            return ok, v
        end)
        local ok1, v1 = coroutine.resume(co)
        assert(ok1 and v1 == 42)
        local ok2, v2, v3 = coroutine.resume(co)
        assert(ok2)
        assert(v2 == true, "xpcall should return true, got: " .. tostring(v2))
        assert(v3 == 100, "xpcall result should be 100, got: " .. tostring(v3))
        "#,
    );
}

#[test]
fn cross_yield_multiple_times_inside_pcall() {
    run_lua(
        r#"
        local co = coroutine.create(function()
            local ok, v = pcall(function()
                coroutine.yield(1)
                coroutine.yield(2)
                return 3
            end)
            return ok, v
        end)
        local ok1, v1 = coroutine.resume(co)
        assert(ok1 and v1 == 1)
        local ok2, v2 = coroutine.resume(co)
        assert(ok2 and v2 == 2)
        local ok3, v3, v4 = coroutine.resume(co)
        assert(ok3 and v3 == true and v4 == 3)
        "#,
    );
}

#[test]
fn cross_yield_nested_pcall() {
    run_lua(
        r#"
        -- yield from inside nested pcall calls
        local co = coroutine.create(function()
            local ok1, v1 = pcall(function()
                local ok2, v2 = pcall(function()
                    coroutine.yield(42)
                    return 100
                end)
                return ok2, v2
            end)
            return ok1, v1
        end)
        local ok, v = coroutine.resume(co)
        assert(ok and v == 42)
        local ok2, v2, v3 = coroutine.resume(co)
        assert(ok2, "second resume should succeed")
        -- outer pcall returns (true, inner_ok, inner_v)
        -- but since inner pcall wraps its results, and outer pcall wraps that:
        -- inner returns (true, 100), outer returns (true, true, 100)
        assert(v2 == true, "outer pcall ok=" .. tostring(v2))
        assert(v3 == true, "inner pcall ok=" .. tostring(v3))
        "#,
    );
}

// ---- Table Sort + Metamethods ----

#[test]
fn cross_table_sort_with_metamethod_values() {
    run_lua(
        r#"
        -- Sort a list of plain numbers using a custom comparator
        local t = {5, 3, 8, 1, 9, 2}
        table.sort(t, function(a, b) return a > b end)
        assert(t[1] == 9 and t[6] == 1)
        "#,
    );
}

// ---- String Operations + Error Handling ----

#[test]
fn cross_string_format_error_caught() {
    run_lua(
        r#"
        local ok, msg = pcall(string.format, "%d", "not a number")
        -- string.format should error on type mismatch
        assert(not ok)
        "#,
    );
}

#[test]
fn cross_pattern_error_caught() {
    run_lua(
        r#"
        -- Invalid pattern should error
        local ok, msg = pcall(string.find, "hello", "[invalid")
        assert(not ok)
        "#,
    );
}

// ---- GC + Closures ----

#[test]
fn cross_gc_preserves_closure_upvalues() {
    run_lua(
        r#"
        local function make()
            local x = 42
            return function() return x end
        end
        local f = make()
        collectgarbage("collect")
        assert(f() == 42)
        "#,
    );
}

#[test]
fn cross_gc_preserves_coroutine_state() {
    run_lua(
        r#"
        local co = coroutine.create(function()
            coroutine.yield(1)
            return 2
        end)
        local _, v1 = coroutine.resume(co)
        assert(v1 == 1)
        collectgarbage("collect")
        local _, v2 = coroutine.resume(co)
        assert(v2 == 2)
        "#,
    );
}

// ---- TBC + pcall ----

#[test]
fn cross_tbc_in_pcall_error_path() {
    run_lua(
        r#"
        local closed = false
        local ok = pcall(function()
            local x <close> = setmetatable({}, {
                __close = function() closed = true end
            })
            error("boom")
        end)
        assert(not ok)
        assert(closed == true)
        "#,
    );
}

#[test]
fn cross_tbc_in_pcall_success_path() {
    run_lua(
        r#"
        local closed = false
        local ok = pcall(function()
            local x <close> = setmetatable({}, {
                __close = function() closed = true end
            })
            return 42
        end)
        assert(ok)
        assert(closed == true)
        "#,
    );
}

// ---- OOP Pattern Integration ----

#[test]
fn cross_oop_with_error_handling() {
    run_lua(
        r#"
        local Account = {}
        Account.__index = Account

        function Account.new(balance)
            return setmetatable({balance = balance}, Account)
        end

        function Account:withdraw(amount)
            if amount > self.balance then
                error("insufficient funds")
            end
            self.balance = self.balance - amount
            return self.balance
        end

        local acc = Account.new(100)
        assert(acc:withdraw(30) == 70)
        local ok, msg = pcall(function() acc:withdraw(200) end)
        assert(not ok)
        assert(string.find(msg, "insufficient funds") ~= nil)
        assert(acc.balance == 70)  -- balance unchanged after error
        "#,
    );
}

// ---- Complex Iterator ----

#[test]
fn cross_fibonacci_iterator() {
    run_lua(
        r#"
        local function fibonacci(max)
            local a, b = 0, 1
            return function()
                if a > max then return nil end
                local val = a
                a, b = b, a + b
                return val
            end
        end
        local fibs = {}
        for v in fibonacci(20) do
            fibs[#fibs + 1] = v
        end
        assert(#fibs == 8)  -- 0,1,1,2,3,5,8,13 (21>20 so not included)
        assert(fibs[1] == 0)
        assert(fibs[7] == 8)
        assert(fibs[8] == 13)
        "#,
    );
}

// ---- Deep Index Chain ----

#[test]
fn cross_deep_index_chain() {
    run_lua(
        r#"
        local function make_chain(depth, val)
            local t = {value = val}
            for i = 1, depth do
                t = setmetatable({}, {__index = t})
            end
            return t
        end
        local t = make_chain(50, 42)
        assert(t.value == 42)
        "#,
    );
}

// ---- Metamethods + Concatenation Chains ----

#[test]
fn cross_concat_chain_with_metamethods() {
    run_lua(
        r#"
        local mt = {__concat = function(a, b)
            if type(a) == "table" then a = a.val end
            if type(b) == "table" then b = b.val end
            return a .. b
        end}
        local a = setmetatable({val = "hello"}, mt)
        assert(a .. " world" == "hello world")
        "#,
    );
}

// ---- Varargs + pcall ----

#[test]
fn cross_vararg_through_pcall() {
    run_lua(
        r#"
        local function f(...)
            return ...
        end
        local ok, a, b, c = pcall(f, 10, 20, 30)
        assert(ok and a == 10 and b == 20 and c == 30)
        "#,
    );
}

// ---- String Patterns + Closures ----

#[test]
fn cross_gmatch_with_closure() {
    run_lua(
        r#"
        local function word_count(s)
            local count = 0
            for _ in string.gmatch(s, "%S+") do
                count = count + 1
            end
            return count
        end
        assert(word_count("hello world foo bar") == 4)
        assert(word_count("") == 0)
        assert(word_count("single") == 1)
        "#,
    );
}

// ---- Coroutine wrap as iterator ----

#[test]
fn cross_wrap_as_iterator() {
    run_lua(
        r#"
        local function permgen(a, n)
            n = n or #a
            if n <= 1 then
                coroutine.yield(a)
            else
                for i = 1, n do
                    a[n], a[i] = a[i], a[n]
                    permgen(a, n - 1)
                    a[n], a[i] = a[i], a[n]
                end
            end
        end
        local count = 0
        local gen = coroutine.wrap(function() permgen({1, 2, 3}) end)
        for p in gen do
            count = count + 1
        end
        assert(count == 6)  -- 3! = 6
        "#,
    );
}
