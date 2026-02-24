use super::helpers::*;

// ---- coroutine.create / resume / yield basic ----

#[test]
fn test_coroutine_basic_resume_return() {
    // Coroutine that returns immediately
    run_check_ints(
        r#"
        local co = coroutine.create(function() return 42 end)
        local ok, val = coroutine.resume(co)
        if ok then return val else return -1 end
        "#,
        &[42],
    );
}

#[test]
fn test_coroutine_resume_returns_true() {
    let r = run_lua(
        r#"
        local co = coroutine.create(function() return 1 end)
        local ok = coroutine.resume(co)
        return ok
    "#,
    );
    assert_bool(&r, 0, true);
}

#[test]
fn test_coroutine_single_yield() {
    run_check_ints(
        r#"
        local co = coroutine.create(function()
            coroutine.yield(10)
            return 20
        end)
        local ok1, v1 = coroutine.resume(co)
        local ok2, v2 = coroutine.resume(co)
        return v1, v2
        "#,
        &[10, 20],
    );
}

#[test]
fn test_coroutine_multiple_yields() {
    run_check_ints(
        r#"
        local co = coroutine.create(function()
            coroutine.yield(1)
            coroutine.yield(2)
            coroutine.yield(3)
            return 4
        end)
        local _, a = coroutine.resume(co)
        local _, b = coroutine.resume(co)
        local _, c = coroutine.resume(co)
        local _, d = coroutine.resume(co)
        return a, b, c, d
        "#,
        &[1, 2, 3, 4],
    );
}

#[test]
fn test_coroutine_pass_values_to_resume() {
    run_check_ints(
        r#"
        local co = coroutine.create(function(a, b)
            return a + b
        end)
        local ok, val = coroutine.resume(co, 10, 20)
        return val
        "#,
        &[30],
    );
}

#[test]
fn test_coroutine_resume_args_become_yield_return() {
    run_check_ints(
        r#"
        local co = coroutine.create(function()
            local x = coroutine.yield()
            return x * 2
        end)
        coroutine.resume(co)       -- start, hits yield
        local ok, val = coroutine.resume(co, 21) -- resume with 21
        return val
        "#,
        &[42],
    );
}

#[test]
fn test_coroutine_yield_multiple_values() {
    run_check_ints(
        r#"
        local co = coroutine.create(function()
            coroutine.yield(10, 20, 30)
        end)
        local ok, a, b, c = coroutine.resume(co)
        return a, b, c
        "#,
        &[10, 20, 30],
    );
}

// ---- coroutine.status ----

#[test]
fn test_coroutine_status_suspended() {
    run_check_strings(
        r#"
        local co = coroutine.create(function() coroutine.yield() end)
        return coroutine.status(co)
        "#,
        &["suspended"],
    );
}

#[test]
fn test_coroutine_status_dead() {
    run_check_strings(
        r#"
        local co = coroutine.create(function() return 1 end)
        coroutine.resume(co)
        return coroutine.status(co)
        "#,
        &["dead"],
    );
}

#[test]
fn test_coroutine_status_suspended_after_yield() {
    run_check_strings(
        r#"
        local co = coroutine.create(function() coroutine.yield() end)
        coroutine.resume(co)
        return coroutine.status(co)
        "#,
        &["suspended"],
    );
}

// ---- coroutine.wrap ----

#[test]
fn test_coroutine_wrap_basic() {
    run_check_ints(
        r#"
        local gen = coroutine.wrap(function()
            coroutine.yield(1)
            coroutine.yield(2)
            return 3
        end)
        local a = gen()
        local b = gen()
        local c = gen()
        return a, b, c
        "#,
        &[1, 2, 3],
    );
}

#[test]
fn test_coroutine_wrap_with_args() {
    run_check_ints(
        r#"
        local gen = coroutine.wrap(function(n)
            for i = 1, n do
                coroutine.yield(i)
            end
        end)
        local a = gen(3)
        local b = gen()
        local c = gen()
        return a, b, c
        "#,
        &[1, 2, 3],
    );
}

// ---- coroutine.close ----

#[test]
fn test_coroutine_close() {
    let r = run_lua(
        r#"
        local co = coroutine.create(function() coroutine.yield() end)
        coroutine.resume(co) -- now suspended
        local ok = coroutine.close(co)
        return ok, coroutine.status(co)
    "#,
    );
    assert_bool(&r, 0, true);
    // After close, status should be "dead"
}

// ---- Error handling ----

#[test]
fn test_coroutine_resume_dead() {
    let r = run_lua(
        r#"
        local co = coroutine.create(function() return 1 end)
        coroutine.resume(co)
        local ok, msg = coroutine.resume(co)
        return ok
    "#,
    );
    assert_bool(&r, 0, false);
}

#[test]
fn test_coroutine_error_in_coroutine() {
    let r = run_lua(
        r#"
        local co = coroutine.create(function()
            error("boom")
        end)
        local ok, msg = coroutine.resume(co)
        return ok
    "#,
    );
    assert_bool(&r, 0, false);
}

// ---- Fibonacci generator (integration test) ----

#[test]
fn test_coroutine_fibonacci_generator() {
    run_check_ints(
        r#"
        local function fib_gen()
            return coroutine.wrap(function()
                local a, b = 0, 1
                while true do
                    coroutine.yield(a)
                    a, b = b, a + b
                end
            end)
        end

        local gen = fib_gen()
        local r1 = gen()
        local r2 = gen()
        local r3 = gen()
        local r4 = gen()
        local r5 = gen()
        local r6 = gen()
        local r7 = gen()
        return r1, r2, r3, r4, r5, r6, r7
        "#,
        &[0, 1, 1, 2, 3, 5, 8],
    );
}

// ---- isyieldable ----

#[test]
fn test_coroutine_isyieldable_main() {
    let r = run_lua("return coroutine.isyieldable()");
    assert_bool(&r, 0, false);
}

// ---- Producer-consumer pattern ----

#[test]
fn test_coroutine_producer_consumer() {
    run_check_ints(
        r#"
        local function producer()
            return coroutine.wrap(function()
                for i = 1, 5 do
                    coroutine.yield(i * 10)
                end
            end)
        end

        local sum = 0
        local gen = producer()
        for val in gen do
            sum = sum + val
        end
        return sum
        "#,
        &[150], // 10+20+30+40+50
    );
}
