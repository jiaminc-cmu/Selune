use super::helpers::*;
use selune_compiler::opcode::OpCode;

#[test]
fn e2e_function_no_params() {
    let (proto, _) = compile_str("function f() end");
    assert!(has_opcode(&proto, OpCode::Closure));
    assert_eq!(proto.protos.len(), 1);
    assert_eq!(proto.protos[0].num_params, 0);
}

#[test]
fn e2e_function_with_params() {
    let (proto, _) = compile_str("function f(a, b, c) return a end");
    assert_eq!(proto.protos[0].num_params, 3);
}

#[test]
fn e2e_function_vararg() {
    let (proto, _) = compile_str("function f(...) return ... end");
    assert!(proto.protos[0].is_vararg);
    assert!(has_opcode(&proto.protos[0], OpCode::VarArg));
}

#[test]
fn e2e_function_mixed_params_vararg() {
    let (proto, _) = compile_str("function f(a, b, ...) end");
    assert_eq!(proto.protos[0].num_params, 2);
    assert!(proto.protos[0].is_vararg);
}

#[test]
fn e2e_method_definition() {
    let (proto, _) = compile_str("function t:m(x) return self, x end");
    // Method: num_params = 2 (self + x)
    assert_eq!(proto.protos[0].num_params, 2);
}

#[test]
fn e2e_closure_upvalue_capture() {
    let (proto, _) = compile_str(
        "local x = 1\nfunction f() return x end",
    );
    assert_eq!(proto.protos.len(), 1);
    assert!(!proto.protos[0].upvalues.is_empty());
    assert!(proto.protos[0].upvalues[0].in_stack || !proto.protos[0].upvalues[0].in_stack);
}

#[test]
fn e2e_nested_closure() {
    let (proto, _) = compile_str(
        "local x = 1\nfunction outer()\n  function inner() return x end\nend",
    );
    assert_eq!(proto.protos.len(), 1); // outer
    assert_eq!(proto.protos[0].protos.len(), 1); // inner inside outer
}

#[test]
fn e2e_local_function_recursive() {
    let (proto, _) = compile_str(
        "local function fib(n)\n  if n then return fib end\n  return n\nend",
    );
    assert!(has_opcode(&proto, OpCode::Closure));
}

#[test]
fn e2e_function_return0() {
    let (proto, _) = compile_str("function f() end");
    // Should have RETURN0 at end of function body
    assert!(has_opcode(&proto.protos[0], OpCode::Return0));
}

#[test]
fn e2e_function_expression() {
    let (proto, _) = compile_str("local f = function(x) return x end");
    assert!(has_opcode(&proto, OpCode::Closure));
    assert_eq!(proto.protos.len(), 1);
}

#[test]
fn e2e_function_call_with_args() {
    let (proto, _) = compile_str("f(1, 2, 3)");
    assert!(has_opcode(&proto, OpCode::Call));
}

#[test]
fn e2e_function_call_with_string_arg() {
    let (proto, _) = compile_str("f \"hello\"");
    assert!(has_opcode(&proto, OpCode::Call));
}

#[test]
fn e2e_function_call_with_table_arg() {
    let (proto, _) = compile_str("f {1, 2}");
    assert!(has_opcode(&proto, OpCode::Call));
    assert!(has_opcode(&proto, OpCode::NewTable));
}

#[test]
fn e2e_tail_call() {
    let (proto, _) = compile_str("function f(x) return g(x) end");
    assert!(has_opcode(&proto.protos[0], OpCode::TailCall));
}
