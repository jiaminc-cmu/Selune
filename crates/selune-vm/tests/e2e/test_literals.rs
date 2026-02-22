use super::helpers::*;
use selune_vm::vm::Vm;

#[test]
fn test_return_integer() {
    let results = run_lua("return 42");
    assert_eq!(results.len(), 1);
    assert_int(&results, 0, 42);
}

#[test]
fn test_return_negative_integer() {
    let results = run_lua("return -7");
    assert_eq!(results.len(), 1);
    assert_int(&results, 0, -7);
}

#[test]
fn test_return_zero() {
    let results = run_lua("return 0");
    assert_eq!(results.len(), 1);
    assert_int(&results, 0, 0);
}

#[test]
fn test_return_float() {
    let results = run_lua("return 3.14");
    assert_eq!(results.len(), 1);
    assert_float(&results, 0, 3.14);
}

#[test]
fn test_return_bool_true() {
    let results = run_lua("return true");
    assert_eq!(results.len(), 1);
    assert_bool(&results, 0, true);
}

#[test]
fn test_return_bool_false() {
    let results = run_lua("return false");
    assert_eq!(results.len(), 1);
    assert_bool(&results, 0, false);
}

#[test]
fn test_return_nil() {
    let results = run_lua("return nil");
    assert_eq!(results.len(), 1);
    assert_nil(&results, 0);
}

#[test]
fn test_return_string() {
    let (proto, strings) = selune_compiler::compiler::compile(b"return \"hello\"", "=test").unwrap();
    let mut vm = Vm::new();
    let results = vm.execute(&proto, strings).unwrap();
    assert_eq!(results.len(), 1);
    assert_str(&results, 0, "hello", &vm);
}

#[test]
fn test_return_multiple() {
    let results = run_lua("return 1, 2, 3");
    assert_eq!(results.len(), 3);
    assert_int(&results, 0, 1);
    assert_int(&results, 1, 2);
    assert_int(&results, 2, 3);
}

#[test]
fn test_return0() {
    let results = run_lua("return");
    assert_eq!(results.len(), 0);
}

#[test]
fn test_empty_program() {
    let results = run_lua("");
    assert_eq!(results.len(), 0);
}

#[test]
fn test_local_assign_return() {
    let results = run_lua("local x = 42; return x");
    assert_eq!(results.len(), 1);
    assert_int(&results, 0, 42);
}

#[test]
fn test_move() {
    let results = run_lua("local a = 1; local b = a; return b");
    assert_eq!(results.len(), 1);
    assert_int(&results, 0, 1);
}

#[test]
fn test_local_nil_default() {
    let results = run_lua("local x; return x");
    assert_eq!(results.len(), 1);
    assert_nil(&results, 0);
}

#[test]
fn test_multiple_locals() {
    let results = run_lua("local a = 10; local b = 20; local c = 30; return a, b, c");
    assert_eq!(results.len(), 3);
    assert_int(&results, 0, 10);
    assert_int(&results, 1, 20);
    assert_int(&results, 2, 30);
}

#[test]
fn test_large_integer() {
    let results = run_lua("return 1000000");
    assert_eq!(results.len(), 1);
    assert_int(&results, 0, 1000000);
}

#[test]
fn test_return_float_zero() {
    let results = run_lua("return 0.0");
    assert_eq!(results.len(), 1);
    assert_float(&results, 0, 0.0);
}
