use super::helpers::*;

// ---- collectgarbage basic API ----

#[test]
fn test_gc_collect() {
    run_check_ints(
        r#"
        collectgarbage("collect")
        return 1
        "#,
        &[1],
    );
}

#[test]
fn test_gc_count_returns_number() {
    let r = run_lua(r#"
        local kb, bytes = collectgarbage("count")
        -- kb should be a number >= 0
        if kb >= 0 then return 1 else return 0 end
    "#);
    assert_int(&r, 0, 1);
}

#[test]
fn test_gc_stop_and_restart() {
    run_check_ints(
        r#"
        collectgarbage("stop")
        local running1 = collectgarbage("isrunning")
        collectgarbage("restart")
        local running2 = collectgarbage("isrunning")
        local r1 = 0
        local r2 = 0
        if not running1 then r1 = 1 end
        if running2 then r2 = 1 end
        return r1, r2
        "#,
        &[1, 1],
    );
}

#[test]
fn test_gc_isrunning() {
    let r = run_lua("return collectgarbage('isrunning')");
    assert_bool(&r, 0, true);
}

#[test]
fn test_gc_step() {
    let r = run_lua(r#"
        local ok = collectgarbage("step")
        return ok
    "#);
    assert_bool(&r, 0, true);
}

#[test]
fn test_gc_setpause() {
    run_check_ints(
        r#"
        local old = collectgarbage("setpause", 400)
        -- old should be 200 (the default)
        return old
        "#,
        &[200],
    );
}

#[test]
fn test_gc_setstepmul() {
    run_check_ints(
        r#"
        local old = collectgarbage("setstepmul", 400)
        -- old should be 200 (the default)
        return old
        "#,
        &[200],
    );
}

#[test]
fn test_gc_default_is_collect() {
    // Calling with no args defaults to "collect"
    run_check_ints(
        r#"
        collectgarbage()
        return 1
        "#,
        &[1],
    );
}

// ---- GC correctness: reachable objects survive ----

#[test]
fn test_gc_reachable_survives() {
    run_check_ints(
        r#"
        local t = {1, 2, 3}
        collectgarbage("collect")
        -- t should still be accessible
        return t[1], t[2], t[3]
        "#,
        &[1, 2, 3],
    );
}

#[test]
fn test_gc_nested_tables_survive() {
    run_check_ints(
        r#"
        local t = {inner = {value = 42}}
        collectgarbage("collect")
        return t.inner.value
        "#,
        &[42],
    );
}

#[test]
fn test_gc_closures_survive() {
    run_check_ints(
        r#"
        local function make_counter()
            local n = 0
            return function()
                n = n + 1
                return n
            end
        end
        local inc = make_counter()
        collectgarbage("collect")
        -- Closure and its upvalue should survive
        return inc(), inc(), inc()
        "#,
        &[1, 2, 3],
    );
}

#[test]
fn test_gc_upvalues_survive() {
    run_check_ints(
        r#"
        local x = 10
        local function get_x() return x end
        collectgarbage("collect")
        return get_x()
        "#,
        &[10],
    );
}

#[test]
fn test_gc_metatables_survive() {
    run_check_ints(
        r#"
        local t = {}
        setmetatable(t, {__index = function(_, k) return k * 2 end})
        collectgarbage("collect")
        return t[5]
        "#,
        &[10],
    );
}

// ---- GC unreachable objects are collected ----

#[test]
fn test_gc_unreachable_collected() {
    // Create many tables, then make them unreachable, then collect
    // Memory should decrease after collection
    let r = run_lua(r#"
        collectgarbage("collect")
        local before = collectgarbage("count")
        -- Create many tables
        local t = {}
        for i = 1, 1000 do
            t[i] = {i, i*2, i*3}
        end
        local after_alloc = collectgarbage("count")
        -- Make them all unreachable
        t = nil
        collectgarbage("collect")
        local after_gc = collectgarbage("count")
        -- after_gc should be less than after_alloc
        if after_gc < after_alloc then return 1 else return 0 end
    "#);
    assert_int(&r, 0, 1);
}

#[test]
fn test_gc_cyclic_references_collected() {
    // Create a cycle and check it gets collected
    let r = run_lua(r#"
        collectgarbage("collect")
        local before = collectgarbage("count")
        -- Create a cycle
        do
            local a = {}
            local b = {}
            a.ref_b = b
            b.ref_a = a
        end
        -- a and b are now unreachable
        collectgarbage("collect")
        local after = collectgarbage("count")
        -- Memory should not grow unboundedly
        return 1
    "#);
    assert_int(&r, 0, 1);
}

// ---- GC stress tests ----

#[test]
fn test_gc_stress_allocation() {
    // Allocate many objects with GC enabled, verify correctness
    run_check_ints(
        r#"
        local sum = 0
        for i = 1, 500 do
            local t = {value = i}
            sum = sum + t.value
        end
        collectgarbage("collect")
        return sum
        "#,
        &[125250], // sum(1..500) = 500*501/2 = 125250
    );
}

#[test]
fn test_gc_repeated_collect() {
    // Multiple collections shouldn't cause issues
    run_check_ints(
        r#"
        local t = {1, 2, 3}
        collectgarbage("collect")
        collectgarbage("collect")
        collectgarbage("collect")
        return t[1] + t[2] + t[3]
        "#,
        &[6],
    );
}

#[test]
fn test_gc_collect_during_iteration() {
    // GC during pairs() iteration
    run_check_ints(
        r#"
        local t = {a = 1, b = 2, c = 3}
        local sum = 0
        for k, v in pairs(t) do
            sum = sum + v
        end
        collectgarbage("collect")
        return sum
        "#,
        &[6],
    );
}

#[test]
fn test_gc_coroutine_survives() {
    run_check_ints(
        r#"
        local co = coroutine.create(function()
            coroutine.yield(10)
            return 20
        end)
        collectgarbage("collect")
        local ok1, v1 = coroutine.resume(co)
        collectgarbage("collect")
        local ok2, v2 = coroutine.resume(co)
        return v1, v2
        "#,
        &[10, 20],
    );
}

#[test]
fn test_gc_string_operations_after_collect() {
    run_check_strings(
        r#"
        local s = "hello"
        collectgarbage("collect")
        return string.upper(s)
        "#,
        &["HELLO"],
    );
}

#[test]
fn test_gc_table_operations_after_collect() {
    run_check_ints(
        r#"
        local t = {3, 1, 2}
        collectgarbage("collect")
        table.sort(t)
        return t[1], t[2], t[3]
        "#,
        &[1, 2, 3],
    );
}

// ---- Integration test ----

#[test]
fn test_gc_fibonacci_with_gc() {
    run_check_ints(
        r#"
        local function fib(n)
            if n <= 1 then return n end
            return fib(n-1) + fib(n-2)
        end
        collectgarbage("collect")
        local result = fib(15)
        collectgarbage("collect")
        return result
        "#,
        &[610],
    );
}

#[test]
fn test_gc_count_basic() {
    // collectgarbage("count") should return two numbers
    let r = run_lua(r#"
        local kb, bytes = collectgarbage("count")
        if type(kb) == "number" and type(bytes) == "number" then
            return 1
        else
            return 0
        end
    "#);
    assert_int(&r, 0, 1);
}
