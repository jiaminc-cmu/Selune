use selune_compiler::proto::Constant;
use selune_core::value::TValue;
use selune_vm::dispatch::{call_function, constant_to_tvalue, table_index, table_newindex};
use selune_vm::vm::Vm;

use crate::compiler::SIDE_EXIT;

/// Write a TValue (as raw u64 bits) to vm.stack[base + offset].
///
/// # Safety
/// - `vm_ptr` must be a valid, non-null pointer to a live `Vm`.
/// - `base + offset` must be within bounds of `vm.stack`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_set_stack_slot(
    vm_ptr: *mut Vm,
    base: usize,
    offset: usize,
    raw_bits: u64,
) {
    let vm = &mut *vm_ptr;
    let idx = base + offset;
    // Ensure the stack is large enough
    if idx >= vm.stack.len() {
        vm.stack.resize(idx + 1, TValue::nil());
    }
    vm.stack[idx] = TValue::from_raw_bits(raw_bits);
}

/// Read a TValue from vm.stack[base + offset], returning its raw u64 bits.
///
/// # Safety
/// - `vm_ptr` must be a valid, non-null pointer to a live `Vm`.
/// - `base + offset` must be within bounds of `vm.stack`.
///   Returns nil (0x7FF8_0000_0000_0002) if out of bounds.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_get_stack_slot(
    vm_ptr: *mut Vm,
    base: usize,
    offset: usize,
) -> u64 {
    let vm = &*vm_ptr;
    let idx = base + offset;
    if idx < vm.stack.len() {
        vm.stack[idx].raw_bits()
    } else {
        TValue::nil().raw_bits()
    }
}

// ---------------------------------------------------------------------------
// Increment 5: Function calls, upvalues, table access helpers
// ---------------------------------------------------------------------------

/// Get upvalue value: reads the upvalue at index `upval_idx` from the current
/// call frame's closure. Returns raw TValue bits.
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
/// - The current call frame must have a closure with at least `upval_idx + 1` upvalues.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_get_upval(vm_ptr: *mut Vm, upval_idx: u64) -> u64 {
    let vm = &mut *vm_ptr;
    let ci = vm.call_stack.last().expect("jit_rt_get_upval: no call frame");
    let closure_idx = ci.closure_idx.expect("jit_rt_get_upval: no closure");
    let uv_idx = vm.gc.get_closure(closure_idx).upvalues[upval_idx as usize];
    vm.get_upval_value(uv_idx).raw_bits()
}

/// Set upvalue value: writes `val_bits` to the upvalue at index `upval_idx`
/// in the current call frame's closure.
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
/// - The current call frame must have a closure with at least `upval_idx + 1` upvalues.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_set_upval(vm_ptr: *mut Vm, upval_idx: u64, val_bits: u64) {
    let vm = &mut *vm_ptr;
    let ci = vm.call_stack.last().expect("jit_rt_set_upval: no call frame");
    let closure_idx = ci.closure_idx.expect("jit_rt_set_upval: no closure");
    let uv_idx = vm.gc.get_closure(closure_idx).upvalues[upval_idx as usize];
    let val = TValue::from_raw_bits(val_bits);
    vm.set_upval_value(uv_idx, val);
}

/// GetTabUp: R[A] = UpVal[upval_b][K[const_c]]
/// Reads upvalue `upval_b` (should be a table), then indexes it with the string
/// constant at `const_c` in the proto. Returns the result as raw TValue bits.
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
/// - The current call frame must have the correct closure and proto.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_get_tab_up(
    vm_ptr: *mut Vm,
    proto_idx: u64,
    upval_b: u64,
    const_c: u64,
) -> u64 {
    let vm = &mut *vm_ptr;
    let ci = vm.call_stack.last().expect("jit_rt_get_tab_up: no call frame");
    let closure_idx = ci.closure_idx.expect("jit_rt_get_tab_up: no closure");
    let uv_idx = vm.gc.get_closure(closure_idx).upvalues[upval_b as usize];
    let table_val = vm.get_upval_value(uv_idx);

    let proto = &vm.protos[proto_idx as usize];
    let key = match &proto.constants[const_c as usize] {
        Constant::String(sid) => TValue::from_string_id(*sid),
        other => constant_to_tvalue(other, &mut vm.gc),
    };

    match table_index(vm, table_val, key) {
        Ok(result) => result.raw_bits(),
        Err(_) => TValue::nil().raw_bits(),
    }
}

/// SetTabUp: UpVal[upval_a][K[const_b]] = val
/// Writes `val` to the table stored in upvalue `upval_a`, using the string
/// constant at `const_b` as the key. `val_or_c` is either raw TValue bits
/// (when `k_flag` != 0) or a register offset from base (when `k_flag` == 0).
///
/// Returns 0 on success, SIDE_EXIT on error.
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_set_tab_up(
    vm_ptr: *mut Vm,
    base: u64,
    proto_idx: u64,
    upval_a: u64,
    const_b: u64,
    val_or_c: u64,
    k_flag: u64,
) -> i64 {
    let vm = &mut *vm_ptr;
    let ci = vm.call_stack.last().expect("jit_rt_set_tab_up: no call frame");
    let closure_idx = ci.closure_idx.expect("jit_rt_set_tab_up: no closure");
    let uv_idx = vm.gc.get_closure(closure_idx).upvalues[upval_a as usize];
    let table_val = vm.get_upval_value(uv_idx);

    let proto = &vm.protos[proto_idx as usize];
    let key = match &proto.constants[const_b as usize] {
        Constant::String(sid) => TValue::from_string_id(*sid),
        other => constant_to_tvalue(other, &mut vm.gc),
    };

    let val = if k_flag != 0 {
        // val_or_c is a constant index
        constant_to_tvalue(&proto.constants[val_or_c as usize], &mut vm.gc)
    } else {
        // val_or_c is a register offset
        vm.stack[base as usize + val_or_c as usize]
    };

    match table_newindex(vm, table_val, key, val) {
        Ok(()) => 0,
        Err(_) => SIDE_EXIT,
    }
}

/// Call function: invokes the function at stack[base + func_off] with
/// `nargs` arguments from stack[base + func_off + 1 ..].
/// Places results at stack[base + func_off ..].
///
/// Returns number of results, or SIDE_EXIT on error.
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_call(
    vm_ptr: *mut Vm,
    base: u64,
    func_off: u64,
    nargs: u64,
    nresults: i64,
) -> i64 {
    let vm = &mut *vm_ptr;
    let func_idx = base as usize + func_off as usize;

    let func_val = vm.stack[func_idx];
    let arg_start = func_idx + 1;
    let arg_end = arg_start + nargs as usize;

    // Collect args into a temporary Vec
    let args: Vec<TValue> = if arg_end <= vm.stack.len() {
        vm.stack[arg_start..arg_end].to_vec()
    } else {
        // Pad with nil if stack is too short
        let mut a = Vec::with_capacity(nargs as usize);
        for i in 0..nargs as usize {
            if arg_start + i < vm.stack.len() {
                a.push(vm.stack[arg_start + i]);
            } else {
                a.push(TValue::nil());
            }
        }
        a
    };

    // call_function uses vm.stack_top to place the new frame.
    // Set it above the JIT frame's used registers so it doesn't overlap.
    let saved_stack_top = vm.stack_top;
    if vm.stack_top < arg_end {
        vm.stack_top = arg_end;
    }

    match call_function(vm, func_val, &args) {
        Ok(results) => {
            // Restore stack_top
            vm.stack_top = saved_stack_top;

            // Place results at stack[func_idx..]
            let wanted = if nresults < 0 {
                results.len() as i64
            } else {
                nresults
            };

            for i in 0..wanted as usize {
                let val = results.get(i).copied().unwrap_or(TValue::nil());
                let idx = func_idx + i;
                if idx >= vm.stack.len() {
                    vm.stack.resize(idx + 1, TValue::nil());
                }
                vm.stack[idx] = val;
            }

            wanted
        }
        Err(_) => {
            vm.stack_top = saved_stack_top;
            SIDE_EXIT
        }
    }
}

/// Self: R[A+1] = R[B]; R[A] = table_index(R[B], key)
/// `key_bits` is the raw TValue of the key (constant or register value).
///
/// Returns 0 on success, SIDE_EXIT on error.
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_self(
    vm_ptr: *mut Vm,
    base: u64,
    a: u64,
    b: u64,
    key_bits: u64,
) -> i64 {
    let vm = &mut *vm_ptr;
    let base = base as usize;
    let a = a as usize;
    let b = b as usize;

    let table_val = vm.stack[base + b];
    // R[A+1] = R[B] (self/receiver)
    let idx_a1 = base + a + 1;
    if idx_a1 >= vm.stack.len() {
        vm.stack.resize(idx_a1 + 1, TValue::nil());
    }
    vm.stack[idx_a1] = table_val;

    let key = TValue::from_raw_bits(key_bits);
    match table_index(vm, table_val, key) {
        Ok(result) => {
            let idx_a = base + a;
            if idx_a >= vm.stack.len() {
                vm.stack.resize(idx_a + 1, TValue::nil());
            }
            vm.stack[idx_a] = result;
            0
        }
        Err(_) => SIDE_EXIT,
    }
}

/// Table index: R[A] = R[B][key]
/// Returns the result as raw TValue bits. Returns nil on error.
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_table_index(
    vm_ptr: *mut Vm,
    table_bits: u64,
    key_bits: u64,
) -> u64 {
    let vm = &mut *vm_ptr;
    let table_val = TValue::from_raw_bits(table_bits);
    let key = TValue::from_raw_bits(key_bits);
    match table_index(vm, table_val, key) {
        Ok(result) => result.raw_bits(),
        Err(_) => TValue::nil().raw_bits(),
    }
}

/// Table newindex: R[A][key] = val
/// Returns 0 on success, SIDE_EXIT on error.
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_table_newindex(
    vm_ptr: *mut Vm,
    table_bits: u64,
    key_bits: u64,
    val_bits: u64,
) -> i64 {
    let vm = &mut *vm_ptr;
    let table_val = TValue::from_raw_bits(table_bits);
    let key = TValue::from_raw_bits(key_bits);
    let val = TValue::from_raw_bits(val_bits);
    match table_newindex(vm, table_val, key, val) {
        Ok(()) => 0,
        Err(_) => SIDE_EXIT,
    }
}
