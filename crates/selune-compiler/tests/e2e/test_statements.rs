use super::helpers::*;
use selune_compiler::opcode::OpCode;

#[test]
fn e2e_local_declaration() {
    let (proto, _) = compile_str("local x = 42");
    assert!(has_opcode(&proto, OpCode::LoadI));
}

#[test]
fn e2e_local_nil_default() {
    let (proto, _) = compile_str("local x, y, z");
    assert!(count_opcode(&proto, OpCode::LoadNil) >= 3);
}

#[test]
fn e2e_local_multiple_with_values() {
    let (proto, _) = compile_str("local a, b = 1, 2");
    assert!(count_opcode(&proto, OpCode::LoadI) >= 2);
}

#[test]
fn e2e_local_fewer_values() {
    let (proto, _) = compile_str("local a, b, c = 1");
    // a = 1, b = nil, c = nil
    assert!(has_opcode(&proto, OpCode::LoadI));
    assert!(has_opcode(&proto, OpCode::LoadNil));
}

#[test]
fn e2e_local_function() {
    let (proto, _) = compile_str("local function f(x) return x end");
    assert!(has_opcode(&proto, OpCode::Closure));
    assert_eq!(proto.protos.len(), 1);
    assert_eq!(proto.protos[0].num_params, 1);
}

#[test]
fn e2e_global_assign() {
    let (proto, _) = compile_str("x = 42");
    assert!(has_opcode(&proto, OpCode::SetTabUp));
}

#[test]
fn e2e_global_read() {
    let (proto, _) = compile_str("return x");
    assert!(has_opcode(&proto, OpCode::GetTabUp));
}

#[test]
fn e2e_if_simple() {
    // Constant true: no Test/Jmp needed, body always runs
    let (proto, _) = compile_str("if true then local x = 1 end");
    assert!(!has_opcode(&proto, OpCode::Test));
    // Non-constant condition uses Test + Jmp
    let (proto, _) = compile_str("local y\nif y then local x = 1 end");
    assert!(has_opcode(&proto, OpCode::Test));
    assert!(has_opcode(&proto, OpCode::Jmp));
}

#[test]
fn e2e_if_else() {
    let (proto, _) = compile_str("if true then local x = 1 else local y = 2 end");
    assert!(count_opcode(&proto, OpCode::Jmp) >= 1);
}

#[test]
fn e2e_while_loop() {
    let (proto, _) = compile_str("local i = 10\nwhile i do i = nil end");
    assert!(has_opcode(&proto, OpCode::Test));
    assert!(count_opcode(&proto, OpCode::Jmp) >= 2); // one for test, one for back-jump
}

#[test]
fn e2e_repeat_until() {
    // Constant true: no Test/Jmp, loop runs once
    let (proto, _) = compile_str("repeat local x = 1 until true");
    assert!(!has_opcode(&proto, OpCode::Test));
    // Non-constant condition uses Test + Jmp
    let (proto, _) = compile_str("local y\nrepeat local x = 1 until y");
    assert!(has_opcode(&proto, OpCode::Test));
}

#[test]
fn e2e_numeric_for() {
    let (proto, _) = compile_str("for i = 1, 10 do local x = i end");
    assert!(has_opcode(&proto, OpCode::ForPrep));
    assert!(has_opcode(&proto, OpCode::ForLoop));
}

#[test]
fn e2e_numeric_for_with_step() {
    let (proto, _) = compile_str("for i = 10, 1, -1 do local x = i end");
    assert!(has_opcode(&proto, OpCode::ForPrep));
    assert!(has_opcode(&proto, OpCode::ForLoop));
}

#[test]
fn e2e_generic_for() {
    let (proto, _) = compile_str("for k, v in pairs do end");
    assert!(has_opcode(&proto, OpCode::TForPrep));
    assert!(has_opcode(&proto, OpCode::TForCall));
    assert!(has_opcode(&proto, OpCode::TForLoop));
}

#[test]
fn e2e_do_end() {
    let (proto, _) = compile_str("do local x = 1 end\nlocal y = 2");
    assert!(count_opcode(&proto, OpCode::LoadI) >= 2);
}

#[test]
fn e2e_break() {
    let (proto, _) = compile_str("while true do break end");
    assert!(has_opcode(&proto, OpCode::Jmp));
}

#[test]
fn e2e_goto_forward() {
    let (proto, _) = compile_str("goto done\nlocal x = 1\n::done::");
    assert!(has_opcode(&proto, OpCode::Jmp));
}

#[test]
fn e2e_goto_backward() {
    let (proto, _) = compile_str("::start::\ngoto start");
    assert!(has_opcode(&proto, OpCode::Jmp));
}

#[test]
fn e2e_return_empty() {
    let (proto, _) = compile_str("return");
    assert!(has_opcode(&proto, OpCode::Return0));
}

#[test]
fn e2e_return_single() {
    let (proto, _) = compile_str("return 1");
    assert!(has_opcode(&proto, OpCode::Return1));
}

#[test]
fn e2e_semicolons() {
    let (proto, _) = compile_str(";;;local x = 1;;;");
    assert!(has_opcode(&proto, OpCode::LoadI));
}

#[test]
fn e2e_function_call_statement() {
    let (proto, _) = compile_str("print(42)");
    assert!(has_opcode(&proto, OpCode::Call));
}

#[test]
fn e2e_multiple_assignment() {
    let (proto, _) = compile_str("local a, b\na, b = 1, 2");
    assert!(count_opcode(&proto, OpCode::LoadI) >= 2);
}

#[test]
fn e2e_local_const() {
    let (proto, _) = compile_str("local x <const> = 42");
    assert!(has_opcode(&proto, OpCode::LoadI));
}

#[test]
fn e2e_nested_blocks() {
    let (proto, _) = compile_str("do\n  do\n    local x = 1\n  end\n  local y = 2\nend");
    assert!(count_opcode(&proto, OpCode::LoadI) >= 2);
}
