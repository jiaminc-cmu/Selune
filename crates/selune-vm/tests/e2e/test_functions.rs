use super::helpers::*;

// ---- Simple function calls ----

#[test]
fn test_simple_function_call() {
    run_check_ints(
        "local function add(a, b) return a + b end
         return add(3, 4)",
        &[7],
    );
}

#[test]
fn test_function_no_args() {
    run_check_ints(
        "local function f() return 42 end
         return f()",
        &[42],
    );
}

#[test]
fn test_function_no_return() {
    let results = run_lua(
        "local function f() end
         return f()",
    );
    assert_eq!(results.len(), 0);
}

#[test]
fn test_function_multiple_returns() {
    run_check_ints(
        "local function f() return 1, 2, 3 end
         local a, b, c = f()
         return a + b + c",
        &[6],
    );
}

#[test]
fn test_function_multiple_returns_direct() {
    run_check_ints(
        "local function f() return 10, 20, 30 end
         return f()",
        &[10, 20, 30],
    );
}

#[test]
fn test_function_discard_extra_returns() {
    run_check_ints(
        "local function f() return 1, 2, 3 end
         local a = f()
         return a",
        &[1],
    );
}

// ---- Recursion ----

#[test]
fn test_factorial() {
    run_check_ints(
        "local function fact(n)
            if n <= 1 then return 1 end
            return n * fact(n - 1)
         end
         return fact(10)",
        &[3628800],
    );
}

#[test]
fn test_fibonacci() {
    run_check_ints(
        "local function fib(n)
            if n < 2 then return n end
            return fib(n - 1) + fib(n - 2)
         end
         return fib(20)",
        &[6765],
    );
}

// ---- Tail calls ----

#[test]
fn test_tail_call() {
    run_check_ints(
        "local function f(n, acc)
            if n <= 0 then return acc end
            return f(n - 1, acc + n)
         end
         return f(100, 0)",
        &[5050],
    );
}

// ---- Nested function calls ----

#[test]
fn test_nested_function_calls() {
    run_check_ints(
        "local function double(x) return x * 2 end
         local function triple(x) return x * 3 end
         return double(triple(5))",
        &[30],
    );
}

#[test]
fn test_function_as_argument() {
    run_check_ints(
        "local function apply(f, x) return f(x) end
         local function double(x) return x * 2 end
         return apply(double, 21)",
        &[42],
    );
}

// ---- Functions in tables ----

#[test]
fn test_function_in_table() {
    run_check_ints(
        "local t = {}
         t.f = function(x) return x + 1 end
         return t.f(41)",
        &[42],
    );
}

#[test]
fn test_method_call_self() {
    run_check_ints(
        "local obj = {x = 10}
         function obj:get() return self.x end
         return obj:get()",
        &[10],
    );
}

#[test]
fn test_method_call_mutate() {
    run_check_ints(
        "local obj = {x = 0}
         function obj:inc() self.x = self.x + 1 end
         obj:inc()
         obj:inc()
         return obj.x",
        &[2],
    );
}

// ---- Varargs ----

#[test]
fn test_varargs_basic() {
    run_check_ints(
        "local function sum(...)
            local args = {...}
            local s = 0
            for i = 1, #args do
                s = s + args[i]
            end
            return s
         end
         return sum(1, 2, 3, 4, 5)",
        &[15],
    );
}

#[test]
fn test_varargs_pass_through() {
    run_check_ints(
        "local function f(...)
            return ...
         end
         return f(10, 20, 30)",
        &[10, 20, 30],
    );
}

#[test]
fn test_varargs_with_fixed() {
    run_check_ints(
        "local function f(a, b, ...)
            local rest = {...}
            return a + b + #rest
         end
         return f(1, 2, 3, 4, 5)",
        &[6],
    );
}

// ---- Call with zero results ----

#[test]
fn test_call_discard_results() {
    run_check_ints(
        "local x = 0
         local function f() x = 42 end
         f()
         return x",
        &[42],
    );
}

// ---- Native functions ----

#[test]
fn test_type_nil() {
    let (proto, strings) =
        selune_compiler::compiler::compile(b"return type(nil)", "=test").unwrap();
    let mut vm = selune_vm::vm::Vm::new();
    let results = vm.execute(&proto, strings).unwrap();
    assert_str(&results, 0, "nil", &vm);
}

#[test]
fn test_type_number() {
    let (proto, strings) = selune_compiler::compiler::compile(b"return type(42)", "=test").unwrap();
    let mut vm = selune_vm::vm::Vm::new();
    let results = vm.execute(&proto, strings).unwrap();
    assert_str(&results, 0, "number", &vm);
}

#[test]
fn test_type_string() {
    let (proto, strings) =
        selune_compiler::compiler::compile(b"return type(\"hello\")", "=test").unwrap();
    let mut vm = selune_vm::vm::Vm::new();
    let results = vm.execute(&proto, strings).unwrap();
    assert_str(&results, 0, "string", &vm);
}

#[test]
fn test_type_boolean() {
    let (proto, strings) =
        selune_compiler::compiler::compile(b"return type(true)", "=test").unwrap();
    let mut vm = selune_vm::vm::Vm::new();
    let results = vm.execute(&proto, strings).unwrap();
    assert_str(&results, 0, "boolean", &vm);
}

#[test]
fn test_type_table() {
    let (proto, strings) = selune_compiler::compiler::compile(b"return type({})", "=test").unwrap();
    let mut vm = selune_vm::vm::Vm::new();
    let results = vm.execute(&proto, strings).unwrap();
    assert_str(&results, 0, "table", &vm);
}

#[test]
fn test_type_function() {
    let (proto, strings) =
        selune_compiler::compiler::compile(b"return type(type)", "=test").unwrap();
    let mut vm = selune_vm::vm::Vm::new();
    let results = vm.execute(&proto, strings).unwrap();
    assert_str(&results, 0, "function", &vm);
}

#[test]
fn test_tonumber_int() {
    run_check_ints("return tonumber(42)", &[42]);
}

#[test]
fn test_tonumber_string() {
    run_check_ints("return tonumber(\"123\")", &[123]);
}

#[test]
fn test_tonumber_nil() {
    let results = run_lua("return tonumber(\"abc\")");
    assert_nil(&results, 0);
}

#[test]
fn test_tostring_int() {
    let (proto, strings) =
        selune_compiler::compiler::compile(b"return tostring(42)", "=test").unwrap();
    let mut vm = selune_vm::vm::Vm::new();
    let results = vm.execute(&proto, strings).unwrap();
    assert_str(&results, 0, "42", &vm);
}

#[test]
fn test_tostring_bool() {
    let (proto, strings) =
        selune_compiler::compiler::compile(b"return tostring(true)", "=test").unwrap();
    let mut vm = selune_vm::vm::Vm::new();
    let results = vm.execute(&proto, strings).unwrap();
    assert_str(&results, 0, "true", &vm);
}

// ---- Stack overflow ----

#[test]
fn test_stack_overflow() {
    let err = run_lua_err(
        "local function f() return f() end
         return f()",
    );
    assert!(
        err.contains("stack overflow"),
        "expected stack overflow, got: {err}"
    );
}
