use cranelift_codegen::ir::{types, AbiParam, Signature};
use cranelift_codegen::isa::CallConv;
use selune_vm::vm::Vm;

/// A JIT-compiled function pointer.
///
/// Signature: `unsafe extern "C" fn(vm: *mut Vm, base: usize) -> i64`
///
/// - `vm`: Pointer to the full VM state (for stack access, GC, metamethods, etc.)
/// - `base`: Stack index of this frame's base register (matches CallInfo.base)
/// - Returns: >=0 means number of results placed at stack[base..], <0 means side exit
pub type JitFunction = unsafe extern "C" fn(vm: *mut Vm, base: usize) -> i64;

/// Build the Cranelift IR signature matching `JitFunction`.
///
/// On AArch64: two i64 params (pointer, usize), one i64 return.
pub fn jit_function_signature(call_conv: CallConv) -> Signature {
    let mut sig = Signature::new(call_conv);
    sig.params.push(AbiParam::new(types::I64)); // vm: *mut Vm
    sig.params.push(AbiParam::new(types::I64)); // base: usize
    sig.returns.push(AbiParam::new(types::I64)); // result count or side exit
    sig
}
