//! Selune virtual machine: bytecode interpreter (Phase 2).

pub mod arith;
pub mod callinfo;
pub mod coerce;
pub mod compare;
pub mod dispatch;
pub mod error;
pub mod vm;

use error::LuaError;
use selune_core::value::TValue;
use vm::Vm;

/// Compile and execute Lua source code, returning the result values.
pub fn execute_source(source: &str) -> Result<Vec<TValue>, LuaError> {
    let (proto, strings) = selune_compiler::compiler::compile(source.as_bytes(), "=input")
        .map_err(|e| LuaError::Runtime(format!("compile error: {}", e.message)))?;

    let mut vm = Vm::new();
    vm.execute(&proto, strings)
}
