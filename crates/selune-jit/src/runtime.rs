use selune_compiler::proto::Constant;
use selune_core::value::TValue;
use selune_vm::arith;
use selune_vm::dispatch::{
    call_function, close_tbc_variables, constant_to_tvalue, table_index, table_newindex,
};
use selune_vm::vm::Vm;

use crate::compiler::SIDE_EXIT;

/// Get the raw pointer to the start of vm.stack's data buffer.
/// JIT code uses this pointer + offset to do inline loads/stores,
/// avoiding the overhead of calling get/set helpers for every access.
///
/// # Safety
/// - `vm_ptr` must be a valid, non-null pointer to a live `Vm`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_get_stack_base(vm_ptr: *mut Vm) -> *const u8 {
    let vm = &*vm_ptr;
    vm.stack.as_ptr() as *const u8
}

/// Get the current length of vm.stack (number of TValue slots).
///
/// # Safety
/// - `vm_ptr` must be a valid, non-null pointer to a live `Vm`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_get_stack_len(vm_ptr: *mut Vm) -> u64 {
    let vm = &*vm_ptr;
    vm.stack.len() as u64
}

/// Ensure vm.stack has at least `min_len` slots. Called before JIT
/// function entry or when inline access detects potential out-of-bounds.
///
/// # Safety
/// - `vm_ptr` must be a valid, non-null pointer to a live `Vm`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_ensure_stack(vm_ptr: *mut Vm, min_len: u64) {
    let vm = &mut *vm_ptr;
    let needed = min_len as usize;
    if vm.stack.len() < needed {
        vm.stack.resize(needed, TValue::nil());
    }
}

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
/// Fast path: if value is a table with no metatable, use raw_get directly.
/// Falls back to table_index for metamethod support.
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
    // Fast path: plain table without metatable
    if let Some(table_idx) = table_val.as_table_idx() {
        let table = vm.gc.get_table(table_idx);
        if table.metatable.is_none() {
            // Use string fast path if key is a string
            if let Some(sid) = key.as_string_id() {
                return table.raw_get_str(sid).raw_bits();
            }
            return vm.gc.table_raw_get(table_idx, key).raw_bits();
        }
    }
    // Slow path: full metamethod dispatch
    match table_index(vm, table_val, key) {
        Ok(result) => result.raw_bits(),
        Err(_) => TValue::nil().raw_bits(),
    }
}

/// Table newindex: R[A][key] = val
/// Fast path: if value is a table with no metatable, use raw_set directly.
/// Falls back to table_newindex for metamethod support.
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
    // Fast path: plain table without metatable
    if let Some(table_idx) = table_val.as_table_idx() {
        let table = vm.gc.get_table(table_idx);
        if table.metatable.is_none() {
            match vm.gc.table_raw_set(table_idx, key, val) {
                Ok(()) => return 0,
                Err(_) => return SIDE_EXIT,
            }
        }
    }
    // Slow path: full metamethod dispatch
    match table_newindex(vm, table_val, key, val) {
        Ok(()) => 0,
        Err(_) => SIDE_EXIT,
    }
}

// ---------------------------------------------------------------------------
// Increment 8: GetI, SetI, Len, Concat, NewTable, SetList
// ---------------------------------------------------------------------------

/// GetI: R[A] = R[B][C] where C is an integer key.
/// Returns the result as raw TValue bits.
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_geti(
    vm_ptr: *mut Vm,
    table_bits: u64,
    index: i64,
) -> u64 {
    let vm = &mut *vm_ptr;
    let table_val = TValue::from_raw_bits(table_bits);
    // Fast path: plain table without metatable
    if let Some(table_idx) = table_val.as_table_idx() {
        let table = vm.gc.get_table(table_idx);
        if table.metatable.is_none() {
            return table.raw_geti(index).raw_bits();
        }
    }
    // Slow path: full metamethod dispatch
    let key = TValue::from_integer(index);
    match table_index(vm, table_val, key) {
        Ok(result) => result.raw_bits(),
        Err(_) => TValue::nil().raw_bits(),
    }
}

/// SetI: R[A][B] = val where B is an integer key.
/// Returns 0 on success, SIDE_EXIT on error.
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_seti(
    vm_ptr: *mut Vm,
    table_bits: u64,
    index: i64,
    val_bits: u64,
) -> i64 {
    let vm = &mut *vm_ptr;
    let table_val = TValue::from_raw_bits(table_bits);
    let val = TValue::from_raw_bits(val_bits);
    // Fast path: plain table without metatable
    if let Some(table_idx) = table_val.as_table_idx() {
        let table = vm.gc.get_table(table_idx);
        if table.metatable.is_none() {
            vm.gc.get_table_mut(table_idx).raw_seti(index, val);
            return 0;
        }
    }
    // Slow path: full metamethod dispatch
    let key = TValue::from_integer(index);
    match table_newindex(vm, table_val, key, val) {
        Ok(()) => 0,
        Err(_) => SIDE_EXIT,
    }
}

/// Len: computes #val, writes result to stack[base+dest].
/// Returns 0 on success, SIDE_EXIT on error.
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_len(
    vm_ptr: *mut Vm,
    base: u64,
    dest: u64,
    src_bits: u64,
) -> i64 {
    let vm = &mut *vm_ptr;
    let src = TValue::from_raw_bits(src_bits);
    let base = base as usize;
    let dest = dest as usize;

    // String fast path
    if let Some(len) = arith::str_len(src, &vm.strings) {
        let result = TValue::from_full_integer(len, &mut vm.gc);
        let idx = base + dest;
        if idx >= vm.stack.len() {
            vm.stack.resize(idx + 1, TValue::nil());
        }
        vm.stack[idx] = result;
        return 0;
    }

    // Table path
    if let Some(table_idx) = src.as_table_idx() {
        // Check for __len metamethod first
        if let Some(mm_names) = vm.mm_names.as_ref() {
            let mm_name = mm_names.len;
            if let Some(mm) = selune_vm::metamethod::get_metamethod(src, mm_name, &vm.gc) {
                match call_function(vm, mm, &[src, src]) {
                    Ok(results) => {
                        let idx = base + dest;
                        if idx >= vm.stack.len() {
                            vm.stack.resize(idx + 1, TValue::nil());
                        }
                        vm.stack[idx] = results.first().copied().unwrap_or(TValue::nil());
                        return 0;
                    }
                    Err(_) => return SIDE_EXIT,
                }
            }
        }
        // No metamethod — use raw length
        let len = vm.gc.get_table(table_idx).length();
        let result = TValue::from_full_integer(len, &mut vm.gc);
        let idx = base + dest;
        if idx >= vm.stack.len() {
            vm.stack.resize(idx + 1, TValue::nil());
        }
        vm.stack[idx] = result;
        return 0;
    }

    // Non-table, non-string: check __len metamethod
    if let Some(mm_names) = vm.mm_names.as_ref() {
        let mm_name = mm_names.len;
        if let Some(mm) = selune_vm::metamethod::get_metamethod(src, mm_name, &vm.gc) {
            match call_function(vm, mm, &[src, src]) {
                Ok(results) => {
                    let idx = base + dest;
                    if idx >= vm.stack.len() {
                        vm.stack.resize(idx + 1, TValue::nil());
                    }
                    vm.stack[idx] = results.first().copied().unwrap_or(TValue::nil());
                    return 0;
                }
                Err(_) => return SIDE_EXIT,
            }
        }
    }

    SIDE_EXIT
}

/// Concat: concatenates `count` values from stack[base+dest..base+dest+count],
/// writes result to stack[base+dest].
/// Returns 0 on success, SIDE_EXIT on error.
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_concat(
    vm_ptr: *mut Vm,
    base: u64,
    dest: u64,
    count: u64,
) -> i64 {
    let vm = &mut *vm_ptr;
    let base = base as usize;
    let dest = dest as usize;
    let count = count as usize;

    let mut values = Vec::with_capacity(count);
    for i in 0..count {
        let idx = base + dest + i;
        if idx < vm.stack.len() {
            values.push(vm.stack[idx]);
        } else {
            values.push(TValue::nil());
        }
    }

    match arith::lua_concat(&values, &vm.gc, &mut vm.strings) {
        arith::ArithResult::Ok(result) => {
            let idx = base + dest;
            if idx >= vm.stack.len() {
                vm.stack.resize(idx + 1, TValue::nil());
            }
            vm.stack[idx] = result;
            0
        }
        _ => {
            // Metamethod or error — side-exit to interpreter
            SIDE_EXIT
        }
    }
}

/// NewTable: allocates a new table with the given capacity hints.
/// Returns raw TValue bits of the new table.
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_newtable(
    vm_ptr: *mut Vm,
    array_hint: u64,
    hash_hint: u64,
) -> u64 {
    let vm = &mut *vm_ptr;
    let table_idx = vm.gc.alloc_table(array_hint as usize, hash_hint as usize);
    TValue::from_table(table_idx).raw_bits()
}

/// SetList: bulk-writes stack values to table array part.
/// table_reg is the register containing the table.
/// Writes stack[base+table_reg+1..base+table_reg+count] to table[offset+1..offset+count].
/// Returns 0 on success, SIDE_EXIT on error.
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_setlist(
    vm_ptr: *mut Vm,
    base: u64,
    table_reg: u64,
    count: u64,
    offset: u64,
) -> i64 {
    let vm = &mut *vm_ptr;
    let base = base as usize;
    let table_reg = table_reg as usize;
    let count = count as usize;
    let offset = offset as usize;

    let table_val = vm.stack[base + table_reg];
    let table_idx = match table_val.as_table_idx() {
        Some(idx) => idx,
        None => return SIDE_EXIT,
    };

    for i in 1..=count {
        let val_idx = base + table_reg + i;
        let val = if val_idx < vm.stack.len() {
            vm.stack[val_idx]
        } else {
            TValue::nil()
        };
        vm.gc.get_table_mut(table_idx).raw_seti((offset + i) as i64, val);
    }

    0
}

/// Runtime helper for TForCall (generic for-loop iterator call).
///
/// Mirrors interpreter TForCall: close upvalues, ensure stack, call iterator,
/// place results in R[A+4]..R[A+3+c].
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_tforcall(
    vm_ptr: *mut Vm,
    base: u64,
    a: u64,
    c: u64,
) -> i64 {
    let vm = &mut *vm_ptr;
    let base = base as usize;
    let a = a as usize;
    let c = c as usize;

    let iter_func = vm.stack[base + a];

    // Fast path: ipairs iterator on plain table — inline the logic directly.
    // This avoids close_upvalues, stack size checks, and call_function overhead.
    // Safe because ipairs doesn't create closures (no upvalues to close) and
    // doesn't grow the stack (writes only to pre-allocated result slots).
    if iter_func.raw_bits() == vm.ipairs_iter_val.raw_bits() {
        let state = vm.stack[base + a + 1];
        let control = vm.stack[base + a + 2];
        // ipairs control is always a small integer (0, 1, 2, ...)
        let i = control.as_integer().unwrap_or(0);
        let next_i = i + 1;
        // Fast table access: check for plain table without metatable
        if let Some(table_idx) = state.as_table_idx() {
            let table = vm.gc.get_table(table_idx);
            if table.metatable.is_none() {
                let val = table.raw_geti(next_i);
                if val.is_nil() {
                    // End of iteration
                    if c >= 1 { vm.stack[base + a + 4] = TValue::nil(); }
                    if c >= 2 { vm.stack[base + a + 5] = TValue::nil(); }
                } else {
                    let key = TValue::from_integer(next_i);
                    if c >= 1 { vm.stack[base + a + 4] = key; }
                    if c >= 2 { vm.stack[base + a + 5] = val; }
                }
                for j in 2..c {
                    vm.stack[base + a + 4 + j] = TValue::nil();
                }
                return 0;
            }
        }
        // Table has metatable or not a table — fall through to slow path
        // (need close_upvalues + stack check for metamethod dispatch)
    }

    // Close upvalues for loop body variables
    vm.close_upvalues(base + a + 4);

    // Ensure stack has space for results
    let min_top = base + a + 4 + c;
    if min_top >= vm.stack.len() {
        vm.stack.resize(min_top + 1, TValue::nil());
    }

    let state = vm.stack[base + a + 1];
    let control = vm.stack[base + a + 2];

    // Handle ipairs with metatable (slow ipairs path)
    if iter_func.raw_bits() == vm.ipairs_iter_val.raw_bits() {
        let i = control.as_full_integer(&vm.gc).unwrap_or(0);
        let next_i = i.wrapping_add(1);
        let key = TValue::from_full_integer(next_i, &mut vm.gc);
        let val = match table_index(vm, state, key) {
            Ok(v) => v,
            Err(_) => return SIDE_EXIT,
        };
        if c >= 1 {
            vm.stack[base + a + 4] = if val.is_nil() { TValue::nil() } else { key };
        }
        if c >= 2 {
            vm.stack[base + a + 5] = val;
        }
        for j in 2..c {
            vm.stack[base + a + 4 + j] = TValue::nil();
        }
        return 0;
    }

    // Slow path: generic iterator via call_function
    // Save/restore stack_top (critical — same pattern as jit_rt_call)
    let saved_stack_top = vm.stack_top;
    if vm.stack_top < min_top {
        vm.stack_top = min_top;
    }

    match call_function(vm, iter_func, &[state, control]) {
        Ok(results) => {
            vm.stack_top = saved_stack_top;
            // Place results in R[A+4]..R[A+3+c]
            for i in 0..c {
                vm.stack[base + a + 4 + i] =
                    results.get(i).copied().unwrap_or(TValue::nil());
            }
            0
        }
        Err(_) => {
            vm.stack_top = saved_stack_top;
            SIDE_EXIT
        }
    }
}

/// Runtime helper for Close opcode.
///
/// Closes TBC (to-be-closed) variables and upvalues from `base + a` onwards.
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_close(
    vm_ptr: *mut Vm,
    _base: u64,
    level: u64,
) -> i64 {
    let vm = &mut *vm_ptr;
    let level = level as usize;

    let ci_idx = vm.call_stack.len() - 1;
    match close_tbc_variables(vm, ci_idx, level, None) {
        Ok(()) => {
            vm.close_upvalues(level);
            0
        }
        Err(_) => SIDE_EXIT,
    }
}

/// Runtime helper for Tbc opcode.
///
/// Marks a variable as to-be-closed. If the value is nil or false, this is a no-op.
/// If the value is non-nil/non-false, it must have a __close metamethod.
/// For generic for loops, the 4th slot is typically nil here.
/// Returns 0 on success, SIDE_EXIT on error (non-closable value).
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_tbc(
    vm_ptr: *mut Vm,
    base: u64,
    a: u64,
) -> i64 {
    let vm = &mut *vm_ptr;
    let base = base as usize;
    let a = a as usize;
    let val = vm.stack[base + a];

    // nil and false are allowed (not to be closed)
    if val.is_falsy() {
        return 0;
    }

    // Non-nil/non-false values must have a __close metamethod
    let mm_name = vm.mm_names.as_ref().unwrap().close;
    if selune_vm::metamethod::get_metamethod(val, mm_name, &vm.gc).is_some() {
        // Register the TBC slot in the current CallInfo
        let ci_idx = vm.call_stack.len() - 1;
        let tbc_slots = vm.call_stack[ci_idx]
            .tbc_slots
            .get_or_insert_with(Vec::new);
        tbc_slots.push(base + a);
        return 0;
    }

    // No __close metamethod — this is an error, side-exit to interpreter
    SIDE_EXIT
}

/// Runtime helper for Closure opcode.
///
/// Creates a new closure by resolving upvalues from the current frame.
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_closure(
    vm_ptr: *mut Vm,
    base: u64,
    proto_idx: u64,
    bx: u64,
    dest: u64,
) -> i64 {
    let vm = &mut *vm_ptr;
    let base = base as usize;
    let proto_idx = proto_idx as usize;
    let bx = bx as usize;
    let dest = dest as usize;

    let child_flat_idx = vm.protos[proto_idx].child_flat_indices[bx];
    let upval_count = vm.protos[child_flat_idx].upvalues.len();

    // Read upvalue descriptors into local buffer
    let mut upval_descs = Vec::with_capacity(upval_count);
    for i in 0..upval_count {
        let desc = &vm.protos[child_flat_idx].upvalues[i];
        upval_descs.push((desc.in_stack, desc.index));
    }

    let ci_idx = vm.call_stack.len() - 1;
    let closure_idx_opt = vm.call_stack[ci_idx].closure_idx;

    let mut upvals = Vec::with_capacity(upval_count);
    for i in 0..upval_count {
        let (in_stack, index) = upval_descs[i];
        if in_stack {
            let stack_idx = base + index as usize;
            let uv_idx = vm.find_or_create_open_upval(stack_idx);
            upvals.push(uv_idx);
        } else if let Some(parent_closure_idx) = closure_idx_opt {
            let parent_closure = vm.gc.get_closure(parent_closure_idx);
            let uv_idx = parent_closure.upvalues[index as usize];
            upvals.push(uv_idx);
        } else {
            return SIDE_EXIT;
        }
    }

    let new_closure_idx = vm.gc.alloc_closure(child_flat_idx, upvals);
    vm.stack[base + dest] = TValue::from_closure(new_closure_idx);
    0
}

/// Runtime helper for VarArg opcode (fixed count only, c > 0).
///
/// Copies `c-1` varargs to R[A]..R[A+c-2].
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_vararg(
    vm_ptr: *mut Vm,
    base: u64,
    a: u64,
    c: u64,
    proto_idx: u64,
) -> i64 {
    let vm = &mut *vm_ptr;
    let base = base as usize;
    let a = a as usize;
    let c = c as usize;
    let proto_idx = proto_idx as usize;

    let ci_idx = vm.call_stack.len() - 1;
    let ci = &vm.call_stack[ci_idx];
    let wanted = c - 1;

    if let Some(vararg_base) = ci.vararg_base {
        let num_params = vm.protos[proto_idx].num_params as usize;
        let vararg_start = vararg_base + num_params;
        let vararg_count = ci.base.saturating_sub(vararg_start);

        // Ensure stack space
        if base + a + wanted >= vm.stack.len() {
            vm.stack.resize(base + a + wanted + 1, TValue::nil());
        }

        for i in 0..wanted {
            if i < vararg_count {
                vm.stack[base + a + i] = vm.stack[vararg_start + i];
            } else {
                vm.stack[base + a + i] = TValue::nil();
            }
        }
    } else {
        // No varargs available, fill with nil
        if base + a + wanted >= vm.stack.len() {
            vm.stack.resize(base + a + wanted + 1, TValue::nil());
        }
        for i in 0..wanted {
            vm.stack[base + a + i] = TValue::nil();
        }
    }
    0
}

/// ForPrep float path: set up float for-loop.
/// Returns 1 if loop enters (body should execute), 0 if skip (empty loop).
/// Box an integer that may exceed the 47-bit small int range.
/// Calls `TValue::from_full_integer()` which GC-boxes if needed.
/// Returns the raw NaN-boxed u64 bits.
///
/// # Safety
/// - `vm_ptr` must be a valid, non-null pointer to a live `Vm`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_box_integer(vm_ptr: *mut Vm, int_val: i64) -> i64 {
    let vm = &mut *vm_ptr;
    let tv = TValue::from_full_integer(int_val, &mut vm.gc);
    tv.raw_bits() as i64
}

/// Reads init/limit/step from R[A], R[A+1], R[A+2].
/// Writes float values to R[A], R[A+1], R[A+2], R[A+3].
#[no_mangle]
pub unsafe extern "C" fn jit_rt_forprep_float(vm_ptr: *mut Vm, base: u64, a: u64) -> i64 {
    let vm = &mut *vm_ptr;
    let base = base as usize;
    let a = a as usize;

    // Convert to float (with string coercion per Lua 5.4 semantics)
    let init = match vm.stack[base + a].as_number(&vm.gc) {
        Some(f) => f,
        None => return SIDE_EXIT,
    };
    let limit = match vm.stack[base + a + 1].as_number(&vm.gc) {
        Some(f) => f,
        None => return SIDE_EXIT,
    };
    let step = match vm.stack[base + a + 2].as_number(&vm.gc) {
        Some(f) => f,
        None => return SIDE_EXIT,
    };

    if step == 0.0 {
        return SIDE_EXIT; // 'for' step is zero — side-exit to let interpreter handle the error
    }

    // Check if loop enters
    let enters = if step > 0.0 { init <= limit } else { init >= limit };
    if !enters {
        return 0; // skip
    }

    // Write float values to stack
    vm.stack[base + a] = TValue::from_float(init);
    vm.stack[base + a + 1] = TValue::from_float(limit);
    vm.stack[base + a + 2] = TValue::from_float(step);
    vm.stack[base + a + 3] = TValue::from_float(init);
    1 // enter body
}

/// ForLoop float path: advance float for-loop.
/// Returns 1 if loop continues, 0 if done.
/// Reads counter/limit/step from R[A], R[A+1], R[A+2].
/// Updates R[A] and R[A+3] with next counter value.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_forloop_float(vm_ptr: *mut Vm, base: u64, a: u64) -> i64 {
    let vm = &mut *vm_ptr;
    let base = base as usize;
    let a = a as usize;

    let counter = match vm.stack[base + a].as_float() {
        Some(f) => f,
        None => return SIDE_EXIT,
    };
    let limit = match vm.stack[base + a + 1].as_float() {
        Some(f) => f,
        None => return SIDE_EXIT,
    };
    let step = match vm.stack[base + a + 2].as_float() {
        Some(f) => f,
        None => return SIDE_EXIT,
    };

    let next = counter + step;
    let continues = if step > 0.0 { next <= limit } else { next >= limit };
    if !continues {
        return 0; // done
    }

    vm.stack[base + a] = TValue::from_float(next);
    vm.stack[base + a + 3] = TValue::from_float(next);
    1 // continue
}
