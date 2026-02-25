//! Selune JIT compiler: method-based JIT compilation using Cranelift.

pub mod abi;
pub mod compiler;
pub mod runtime;

pub use abi::JitFunction;
pub use compiler::{JitCompiler, JitError};
