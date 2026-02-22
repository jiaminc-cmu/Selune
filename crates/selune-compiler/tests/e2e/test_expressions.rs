use super::helpers::*;
use selune_compiler::opcode::OpCode;

#[test]
fn e2e_return_nil() {
    let (proto, _) = compile_str("return nil");
    assert!(has_opcode(&proto, OpCode::LoadNil));
    assert!(has_opcode(&proto, OpCode::Return1));
}

#[test]
fn e2e_return_true() {
    let (proto, _) = compile_str("return true");
    assert!(has_opcode(&proto, OpCode::LoadTrue));
}

#[test]
fn e2e_return_false() {
    let (proto, _) = compile_str("return false");
    assert!(has_opcode(&proto, OpCode::LoadFalse));
}

#[test]
fn e2e_return_integer() {
    let (proto, _) = compile_str("return 42");
    assert!(has_opcode(&proto, OpCode::LoadI) || has_opcode(&proto, OpCode::LoadK));
}

#[test]
fn e2e_return_negative_integer() {
    let (proto, _) = compile_str("return -1");
    // Constant folded: -1 as LoadI
    assert!(has_opcode(&proto, OpCode::LoadI));
}

#[test]
fn e2e_return_float() {
    let (proto, _) = compile_str("return 3.14");
    assert!(has_opcode(&proto, OpCode::LoadK));
    assert!(!proto.constants.is_empty());
}

#[test]
fn e2e_return_string() {
    let (proto, strings) = compile_str("return \"hello world\"");
    assert!(has_opcode(&proto, OpCode::LoadK));
    let s = get_string_constant(&proto, 0, &strings);
    assert_eq!(s, "hello world");
}

#[test]
fn e2e_constant_folding_neg() {
    let (proto, _) = compile_str("return -42");
    // Should be folded into a single LoadI -42
    assert!(has_opcode(&proto, OpCode::LoadI));
    assert!(!has_opcode(&proto, OpCode::Unm));
}

#[test]
fn e2e_constant_folding_not() {
    let (proto, _) = compile_str("return not nil");
    // not nil = true, should be constant folded
    assert!(has_opcode(&proto, OpCode::LoadTrue));
    assert!(!has_opcode(&proto, OpCode::Not));
}

#[test]
fn e2e_constant_folding_bnot() {
    let (proto, _) = compile_str("return ~0");
    // ~0 = -1, should be constant folded
    assert!(has_opcode(&proto, OpCode::LoadI));
    assert!(!has_opcode(&proto, OpCode::BNot));
}

#[test]
fn e2e_arithmetic_ops() {
    let (proto, _) = compile_str("local a = 1\nlocal b = 2\nreturn a + b");
    assert!(
        has_opcode(&proto, OpCode::Add)
            || has_opcode(&proto, OpCode::AddK)
            || has_opcode(&proto, OpCode::AddI)
    );
}

#[test]
fn e2e_comparison_ops() {
    let (proto, _) = compile_str("local a = 1\nlocal b = 2\nif a < b then end");
    assert!(has_opcode(&proto, OpCode::Lt));
}

#[test]
fn e2e_and_short_circuit() {
    let (proto, _) = compile_str("return true and 42");
    assert!(has_opcode(&proto, OpCode::TestSet));
    assert!(has_opcode(&proto, OpCode::Jmp));
}

#[test]
fn e2e_or_short_circuit() {
    let (proto, _) = compile_str("return nil or 42");
    assert!(has_opcode(&proto, OpCode::TestSet));
}

#[test]
fn e2e_table_constructor_empty() {
    let (proto, _) = compile_str("return {}");
    assert!(has_opcode(&proto, OpCode::NewTable));
}

#[test]
fn e2e_table_constructor_array() {
    let (proto, _) = compile_str("return {1, 2, 3}");
    assert!(has_opcode(&proto, OpCode::NewTable));
    assert!(has_opcode(&proto, OpCode::SetList));
}

#[test]
fn e2e_table_constructor_hash() {
    let (proto, _) = compile_str("return {x = 1, y = 2}");
    assert!(has_opcode(&proto, OpCode::NewTable));
    assert!(has_opcode(&proto, OpCode::SetField));
}

#[test]
fn e2e_table_constructor_mixed() {
    let (proto, _) = compile_str("return {1, x = 2, 3}");
    assert!(has_opcode(&proto, OpCode::NewTable));
    assert!(has_opcode(&proto, OpCode::SetField));
    assert!(has_opcode(&proto, OpCode::SetList));
}

#[test]
fn e2e_table_bracket_key() {
    let (proto, _) = compile_str("return {[1] = \"a\", [2] = \"b\"}");
    assert!(has_opcode(&proto, OpCode::NewTable));
    assert!(has_opcode(&proto, OpCode::SetTable) || has_opcode(&proto, OpCode::SetI));
}

#[test]
fn e2e_concat() {
    let (proto, _) = compile_str("local a = \"hello\"\nlocal b = \"world\"\nreturn a .. b");
    assert!(has_opcode(&proto, OpCode::Concat));
}

#[test]
fn e2e_len_operator() {
    let (proto, _) = compile_str("local t = {}\nreturn #t");
    assert!(has_opcode(&proto, OpCode::Len));
}

#[test]
fn e2e_multiple_return_values() {
    let (proto, _) = compile_str("return 1, 2, 3");
    assert!(has_opcode(&proto, OpCode::Return));
    // Return with B > 1 means multiple values
}
