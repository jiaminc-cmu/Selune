use super::helpers::*;

// ---- Basic closure ----

#[test]
fn test_closure_counter() {
    run_check_ints(
        "local function counter()
            local n = 0
            return function()
                n = n + 1
                return n
            end
         end
         local c = counter()
         c()
         c()
         return c()",
        &[3],
    );
}

#[test]
fn test_closure_capture_local() {
    run_check_ints(
        "local x = 10
         local function f() return x end
         return f()",
        &[10],
    );
}

// ---- Upvalue mutation ----

#[test]
fn test_upvalue_mutation() {
    run_check_ints(
        "local x = 0
         local function inc() x = x + 1 end
         inc()
         inc()
         return x",
        &[2],
    );
}

#[test]
fn test_upvalue_shared() {
    run_check_ints(
        "local x = 0
         local function inc() x = x + 1 end
         local function get() return x end
         inc()
         inc()
         inc()
         return get()",
        &[3],
    );
}

// ---- Nested closures ----

#[test]
fn test_nested_closure() {
    run_check_ints(
        "local function make()
            local x = 0
            local function inc()
                x = x + 1
                return function() return x end
            end
            return inc
         end
         local inc = make()
         inc()
         inc()
         local get = inc()
         return get()",
        &[3],
    );
}

#[test]
fn test_closure_over_loop_variable() {
    run_check_ints(
        "local fns = {}
         for i = 1, 3 do
            fns[i] = function() return i end
         end
         return fns[1]() + fns[2]() + fns[3]()",
        &[6],
    );
}

// ---- Upvalue closing ----

#[test]
fn test_upvalue_closed_on_return() {
    run_check_ints(
        "local function make()
            local x = 42
            return function() return x end
         end
         local f = make()
         return f()",
        &[42],
    );
}

#[test]
fn test_upvalue_closed_mutation() {
    run_check_ints(
        "local function make()
            local x = 0
            local function set(v) x = v end
            local function get() return x end
            return set, get
         end
         local set, get = make()
         set(99)
         return get()",
        &[99],
    );
}

// ---- Multiple independent closures ----

#[test]
fn test_multiple_counters() {
    run_check_ints(
        "local function counter()
            local n = 0
            return function()
                n = n + 1
                return n
            end
         end
         local a = counter()
         local b = counter()
         a(); a(); a()
         b()
         return a(), b()",
        &[4, 2],
    );
}

// ---- Closure with table ----

#[test]
fn test_closure_with_table() {
    run_check_ints(
        "local function make()
            local t = {count = 0}
            return function()
                t.count = t.count + 1
                return t.count
            end
         end
         local f = make()
         f(); f()
         return f()",
        &[3],
    );
}

// ---- Higher-order functions ----

#[test]
fn test_higher_order_map() {
    run_check_ints(
        "local function apply(f, x) return f(x) end
         local function make_adder(n)
            return function(x) return x + n end
         end
         local add10 = make_adder(10)
         return apply(add10, 32)",
        &[42],
    );
}

// ---- Accumulator pattern ----

#[test]
fn test_accumulator() {
    run_check_ints(
        "local function make_acc(init)
            local sum = init
            return function(n)
                sum = sum + n
                return sum
            end
         end
         local acc = make_acc(100)
         acc(10)
         acc(20)
         return acc(30)",
        &[160],
    );
}
