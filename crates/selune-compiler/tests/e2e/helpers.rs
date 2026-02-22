use selune_compiler::compiler::compile;
use selune_compiler::opcode::OpCode;
use selune_compiler::proto::{Constant, Proto};
use selune_core::string::StringInterner;

/// Compile a Lua source string and return the Proto + StringInterner.
pub fn compile_str(source: &str) -> (Proto, StringInterner) {
    compile(source.as_bytes(), "test").unwrap_or_else(|e| {
        panic!("compile failed: {e}\nsource:\n{source}");
    })
}

/// Compile a Lua source string and expect an error.
pub fn compile_str_err(source: &str) -> String {
    match compile(source.as_bytes(), "test") {
        Err(e) => e.message,
        Ok(_) => panic!("expected compile error, got success\nsource:\n{source}"),
    }
}

/// Check if a Proto contains a specific opcode.
pub fn has_opcode(proto: &Proto, op: OpCode) -> bool {
    proto.code.iter().any(|i| i.opcode() == op)
}

/// Count occurrences of an opcode in a Proto.
pub fn count_opcode(proto: &Proto, op: OpCode) -> usize {
    proto.code.iter().filter(|i| i.opcode() == op).count()
}

/// Find the first instruction with a given opcode.
#[allow(dead_code)]
pub fn find_opcode(proto: &Proto, op: OpCode) -> Option<usize> {
    proto.code.iter().position(|i| i.opcode() == op)
}

/// Get string constant value by index.
pub fn get_string_constant(proto: &Proto, idx: usize, strings: &StringInterner) -> String {
    match &proto.constants[idx] {
        Constant::String(id) => String::from_utf8(strings.get_bytes(*id).to_vec()).unwrap(),
        other => panic!("expected string constant, got {other:?}"),
    }
}

/// Get integer constant value by index.
#[allow(dead_code)]
pub fn get_int_constant(proto: &Proto, idx: usize) -> i64 {
    match &proto.constants[idx] {
        Constant::Integer(i) => *i,
        other => panic!("expected integer constant, got {other:?}"),
    }
}
