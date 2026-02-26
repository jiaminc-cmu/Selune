use selune_compiler::proto::Constant;
use selune_core::string::StringId;
use selune_core::value::TValue;
use selune_vm::arith;
use selune_vm::callinfo::{CallInfo, JitCallInfo};
use selune_vm::dispatch::{
    call_function, close_tbc_variables, constant_to_tvalue, execute_from, table_index,
    table_newindex,
};
use selune_vm::vm::{JitFn, JitProtoState, TinyMethodKind, Vm};

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

/// Get a raw pointer to a Table in the GC heap by its index.
/// Returns the pointer as u64 (0 if the slot is empty/freed).
/// JIT code uses this to load table fields (metatable, version) at known offsets.
///
/// # Safety
/// - `vm_ptr` must be a valid, non-null pointer to a live `Vm`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_get_table_ptr(vm_ptr: *mut Vm, table_idx: u64) -> u64 {
    let vm = &*vm_ptr;
    let idx = table_idx as usize;
    if idx < vm.gc.tables.len() {
        if let Some(ref table) = vm.gc.tables[idx] {
            return table as *const _ as u64;
        }
    }
    0
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
        vm.update_stack_data_ptr();
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
        vm.update_stack_data_ptr();
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
    let closure_idx = vm.current_closure_idx().expect("jit_rt_get_upval: no closure");
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
    let closure_idx = vm.current_closure_idx().expect("jit_rt_set_upval: no closure");
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
    let closure_idx = vm.current_closure_idx().expect("jit_rt_get_tab_up: no closure");
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
    let closure_idx = vm.current_closure_idx().expect("jit_rt_set_tab_up: no closure");
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
                    vm.update_stack_data_ptr();
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

/// Fast call: invokes the function at stack[base + func_off] with
/// `nargs` arguments already on the stack at stack[base + func_off + 1 ..].
///
/// Optimizations over `jit_rt_call`:
/// - **No Vec allocation for args**: reads args directly from the stack.
/// - **JIT-to-JIT fast path**: if callee has JIT code, calls it directly
///   with zero heap allocation (push CallInfo, call jit_fn, pop CallInfo).
/// - **Interpreter fast path**: for non-JIT Lua closures, pushes CallInfo
///   and calls `execute_from` directly (skips `call_function` indirection).
/// - Falls back to `call_function` only for native functions and `__call`.
///
/// Returns number of results, or SIDE_EXIT on error.
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_call_fast(
    vm_ptr: *mut Vm,
    base: u64,
    func_off: u64,
    nargs: u64,
    nresults: i64,
) -> i64 {
    let vm = &mut *vm_ptr;
    let func_idx = base as usize + func_off as usize;
    let func_val = *vm.stack.get_unchecked(func_idx);
    let nargs = nargs as usize;
    let arg_end = func_idx + 1 + nargs;

    // Save/restore stack_top (critical — call_function and execute_from use it)
    let saved_stack_top = vm.stack_top;
    if vm.stack_top < arg_end {
        vm.stack_top = arg_end;
    }

    if let Some(closure_idx) = func_val.as_closure_idx() {
        // Lua closure call — fast path
        let closure = vm.gc.get_closure(closure_idx);
        let child_proto_idx = closure.proto_idx;
        let child_proto = vm.protos.get_unchecked(child_proto_idx);
        let num_params = child_proto.num_params as usize;
        let is_vararg = child_proto.is_vararg;
        let max_stack = child_proto.max_stack_size as usize;

        // --- Try tiny method inlining ---
        if nargs >= 1 {
            if let TinyMethodKind::Getter { field_sid } = *vm.tiny_methods.get_unchecked(child_proto_idx) {
                let self_val = *vm.stack.get_unchecked(func_idx + 1);
                if let Some(tbl_idx) = self_val.as_table_idx() {
                    let table = vm.gc.get_table_unchecked(tbl_idx);
                    let result = table.raw_get_str(StringId(field_sid));
                    if !result.is_nil() {
                        vm.stack_top = saved_stack_top;
                        if nresults == 1 {
                            *vm.stack.get_unchecked_mut(func_idx) = result;
                            return 1;
                        } else if nresults == 0 {
                            return 0;
                        } else if nresults < 0 {
                            *vm.stack.get_unchecked_mut(func_idx) = result;
                            return 1;
                        } else {
                            *vm.stack.get_unchecked_mut(func_idx) = result;
                            for i in 1..nresults as usize {
                                *vm.stack.get_unchecked_mut(func_idx + i) = TValue::nil();
                            }
                            return nresults;
                        }
                    }
                    // raw_get_str returned nil — field might be on metatable, fall through
                }
            }
        }

        if vm.call_stack.len() + vm.jit_call_stack.len() >= vm.max_call_depth {
            vm.stack_top = saved_stack_top;
            return SIDE_EXIT;
        }

        let new_base = func_idx + 1;

        // Ensure stack space
        let needed = new_base + max_stack + num_params + 1;
        if needed > vm.stack.len() {
            vm.stack.resize(needed, TValue::nil());
            vm.update_stack_data_ptr();
        }

        // Pad with nil if fewer args than params
        for i in nargs..num_params {
            *vm.stack.get_unchecked_mut(new_base + i) = TValue::nil();
        }

        // --- JIT-to-JIT fast path (non-vararg only) ---
        if !is_vararg && vm.jit_enabled {
            // Check for already-compiled JIT function first (skip counter overhead)
            if let Some(jit_fn) = vm.jit_get_fn(child_proto_idx) {
                // Lightweight JIT-to-JIT call using shadow stack (~32 bytes vs ~120 bytes CallInfo)
                let jit_ci = JitCallInfo {
                    base: new_base,
                    func_stack_idx: func_idx,
                    proto_idx: child_proto_idx,
                    closure_idx_raw: closure_idx.0,
                    num_results: nresults as i32,
                };
                vm.jit_call_stack.push(jit_ci);

                let result = jit_fn(vm as *mut Vm, new_base);

                if result >= 0 {
                    // Close upvalues only if any are open
                    if !vm.open_upvals.is_empty() {
                        vm.close_upvalues(new_base);
                    }
                    vm.jit_call_stack.pop();
                    vm.stack_top = saved_stack_top;

                    // Specialized result placement (most common cases first)
                    if nresults == 1 {
                        // Single result — most common for expressions like f(x) + g(x)
                        *vm.stack.get_unchecked_mut(func_idx) = if result > 0 { *vm.stack.get_unchecked(new_base) } else { TValue::nil() };
                        return 1;
                    } else if nresults == 0 {
                        // Zero results — call for side effects only
                        return 0;
                    } else {
                        // Multi-result
                        let nresults_actual = result as usize;
                        let wanted = if nresults < 0 {
                            nresults_actual as i64
                        } else {
                            nresults
                        };
                        let n = (wanted as usize).min(nresults_actual);
                        for i in 0..n {
                            *vm.stack.get_unchecked_mut(func_idx + i) = *vm.stack.get_unchecked(new_base + i);
                        }
                        for i in n..wanted as usize {
                            *vm.stack.get_unchecked_mut(func_idx + i) = TValue::nil();
                        }
                        return wanted;
                    }
                } else {
                    // SIDE_EXIT from callee
                    vm.jit_call_stack.pop();
                    vm.jit_record_side_exit(child_proto_idx);
                    // Fall through to interpreter path below
                }
            } else {
                // Not yet compiled — increment call count, maybe trigger compilation
                if child_proto_idx < vm.jit_call_counts.len() {
                    vm.jit_call_counts[child_proto_idx] += 1;
                    if vm.jit_call_counts[child_proto_idx] == vm.jit_threshold
                        && !vm.jit_should_skip(child_proto_idx)
                    {
                        if let Some(cb) = vm.jit_compile_callback {
                            cb(vm, child_proto_idx);
                        }
                    }
                }
            }
        }

        // --- Interpreter fallback for Lua closures ---
        // Push CallInfo and call execute_from directly (skip call_function indirection)
        if is_vararg {
            // Vararg setup: move args to vararg area
            let actual_base = new_base + nargs;
            let needed_va = actual_base + max_stack + 1;
            if needed_va > vm.stack.len() {
                vm.stack.resize(needed_va, TValue::nil());
                vm.update_stack_data_ptr();
            }
            for i in 0..num_params.min(nargs) {
                vm.stack[actual_base + i] = vm.stack[new_base + i];
            }
            for i in nargs..num_params {
                vm.stack[actual_base + i] = TValue::nil();
            }
            vm.stack_top = actual_base + max_stack;

            let entry_depth = vm.call_stack.len() + 1;
            let mut ci = CallInfo::new(actual_base, child_proto_idx);
            ci.num_results = -1;
            ci.closure_idx = Some(closure_idx);
            ci.func_stack_idx = func_idx;
            ci.vararg_base = Some(new_base);
            ci.ftransfer = 1;
            ci.ntransfer = num_params as u16;
            ci.saved_hook_line = vm.hook_last_line;
            vm.call_stack.push(ci);

            match execute_from(vm, entry_depth) {
                Ok(results) => {
                    vm.call_stack.truncate(entry_depth - 1);
                    vm.stack_top = saved_stack_top;
                    let wanted = if nresults < 0 {
                        results.len() as i64
                    } else {
                        nresults
                    };
                    for i in 0..wanted as usize {
                        let val = results.get(i).copied().unwrap_or(TValue::nil());
                        vm.stack[func_idx + i] = val;
                    }
                    return wanted;
                }
                Err(_) => {
                    vm.call_stack.truncate(entry_depth - 1);
                    vm.stack_top = saved_stack_top;
                    return SIDE_EXIT;
                }
            }
        } else {
            // Non-vararg, non-JIT: use execute_from directly
            vm.stack_top = new_base + max_stack;

            let entry_depth = vm.call_stack.len() + 1;
            let mut ci = CallInfo::new(new_base, child_proto_idx);
            ci.num_results = -1;
            ci.closure_idx = Some(closure_idx);
            ci.func_stack_idx = func_idx;
            ci.ftransfer = 1;
            ci.ntransfer = num_params as u16;
            ci.saved_hook_line = vm.hook_last_line;
            vm.call_stack.push(ci);

            match execute_from(vm, entry_depth) {
                Ok(results) => {
                    vm.call_stack.truncate(entry_depth - 1);
                    vm.stack_top = saved_stack_top;
                    let wanted = if nresults < 0 {
                        results.len() as i64
                    } else {
                        nresults
                    };
                    for i in 0..wanted as usize {
                        let val = results.get(i).copied().unwrap_or(TValue::nil());
                        vm.stack[func_idx + i] = val;
                    }
                    return wanted;
                }
                Err(_) => {
                    vm.call_stack.truncate(entry_depth - 1);
                    vm.stack_top = saved_stack_top;
                    return SIDE_EXIT;
                }
            }
        }
    }

    // Non-closure (native function or __call metamethod) — fall back to call_function
    // Collect args into a slice from the stack
    let args: Vec<TValue> = (0..nargs)
        .map(|i| {
            let idx = func_idx + 1 + i;
            if idx < vm.stack.len() {
                vm.stack[idx]
            } else {
                TValue::nil()
            }
        })
        .collect();

    match call_function(vm, func_val, &args) {
        Ok(results) => {
            vm.stack_top = saved_stack_top;
            let wanted = if nresults < 0 {
                results.len() as i64
            } else {
                nresults
            };
            for i in 0..wanted as usize {
                let val = results.get(i).copied().unwrap_or(TValue::nil());
                if func_idx + i >= vm.stack.len() {
                    vm.stack.resize(func_idx + i + 1, TValue::nil());
                    vm.update_stack_data_ptr();
                }
                vm.stack[func_idx + i] = val;
            }
            wanted
        }
        Err(_) => {
            vm.stack_top = saved_stack_top;
            SIDE_EXIT
        }
    }
}

/// TailCall handler: calls function at stack[base + func_off] and places
/// results at stack[base + 0..] (the JIT return convention position).
///
/// This is like `jit_rt_call_fast` but places results at R[0] instead of R[A],
/// which is what TailCall needs since the JIT caller will return these results.
///
/// Returns number of results, or SIDE_EXIT on error.
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_tailcall(
    vm_ptr: *mut Vm,
    base: u64,
    func_off: u64,
    nargs: u64,
    nresults: i64,
) -> i64 {
    // Use call_fast to do the actual call — results go to stack[func_idx]
    let result = jit_rt_call_fast(vm_ptr, base, func_off, nargs, nresults);
    if result < 0 {
        return SIDE_EXIT;
    }

    let vm = &mut *vm_ptr;
    let func_idx = base as usize + func_off as usize;
    let base = base as usize;

    // Move results from stack[func_idx..] to stack[base..]
    if func_idx != base {
        let count = result as usize;
        for i in 0..count {
            vm.stack[base + i] = vm.stack[func_idx + i];
        }
    }

    result
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
        vm.update_stack_data_ptr();
    }
    vm.stack[idx_a1] = table_val;

    let key = TValue::from_raw_bits(key_bits);
    match table_index(vm, table_val, key) {
        Ok(result) => {
            let idx_a = base + a;
            if idx_a >= vm.stack.len() {
                vm.stack.resize(idx_a + 1, TValue::nil());
                vm.update_stack_data_ptr();
            }
            vm.stack[idx_a] = result;
            0
        }
        Err(_) => SIDE_EXIT,
    }
}

/// Fast Self: R[A+1] = R[B]; R[A] = lookup(R[B], key)
///
/// Mirrors the interpreter's Self_ fast path (dispatch.rs Self_ handler):
/// 1. Raw lookup in object table (string key fast path)
/// 2. If nil + has metatable → check `__index`
/// 3. If `__index` is a table → raw lookup in that table
/// 4. Only fall back to full `table_index()` for deep chains or function `__index`
///
/// Returns 0 on success, SIDE_EXIT on error.
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_self_fast(
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
    vm.stack[base + a + 1] = table_val;

    let key = TValue::from_raw_bits(key_bits);

    // Fast path: table with string key
    if let Some(table_idx) = table_val.as_table_idx() {
        let key_sid = key.as_string_id();

        // Step 1: Raw lookup in the object table
        let raw_result = if let Some(sid) = key_sid {
            vm.gc.get_table(table_idx).raw_get_str(sid)
        } else {
            vm.gc.table_raw_get(table_idx, key)
        };

        if !raw_result.is_nil() {
            vm.stack[base + a] = raw_result;
            return 0;
        }

        // Step 2: Check metatable.__index
        let table = vm.gc.get_table(table_idx);
        if let Some(mt_idx) = table.metatable {
            let mm_index_name = vm.mm_names.as_ref().unwrap().index;
            let mm_val = vm.gc.get_table(mt_idx).raw_get_str(mm_index_name);

            if let Some(idx_table_idx) = mm_val.as_table_idx() {
                // Step 3: __index is a table → direct lookup
                let idx_result = if let Some(sid) = key_sid {
                    vm.gc.get_table(idx_table_idx).raw_get_str(sid)
                } else {
                    vm.gc.table_raw_get(idx_table_idx, key)
                };

                if !idx_result.is_nil() {
                    vm.stack[base + a] = idx_result;
                    return 0;
                }
                // Fall through to full table_index for deeper chains
            }
            // __index is a function or deeper chain → fall through
        } else {
            // No metatable, raw miss → nil
            vm.stack[base + a] = TValue::nil();
            return 0;
        }
    }

    // Slow path: full metamethod dispatch
    match table_index(vm, table_val, key) {
        Ok(result) => {
            vm.stack[base + a] = result;
            0
        }
        Err(_) => SIDE_EXIT,
    }
}

/// Ultra-fast IC probe for Self_. Returns cached method bits if IC hits, 0 if miss.
/// JIT code calls this first, and only calls jit_rt_self_ic on miss.
///
/// IC hit criteria: table has metatable matching IC, __index table version matches,
/// AND instance table shape hasn't changed (no new keys added).
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
/// - `ic_ptr` must be a valid pointer to a `SelfIcEntry`.
#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn jit_rt_self_ic_check(
    vm_ptr: *mut Vm,
    table_bits: u64,
    ic_ptr: u64,
) -> u64 {
    use selune_vm::vm::SelfIcEntry;

    let vm = &*vm_ptr;
    let table_val = TValue::from_raw_bits(table_bits);

    if let Some(table_idx) = table_val.as_table_idx() {
        let ic = &*(ic_ptr as *const SelfIcEntry);

        // Quick check: IC populated?
        if ic.cached_mt_tag != 0 {
            let table = vm.gc.get_table(table_idx);

            // Check 1: metatable identity
            let mt_raw = table.metatable_raw();
            if mt_raw as u64 + 1 == ic.cached_mt_tag {
                // Check 2: __index table version
                let idx_tbl_idx = ic.cached_index_table_idx as u32;
                let idx_table = vm.gc.get_table(
                    selune_core::gc::GcIdx(idx_tbl_idx, std::marker::PhantomData),
                );
                if idx_table.version as u64 == ic.cached_version {
                    // Check 3: instance shape hasn't changed (no new keys)
                    if table.shape_version as u64 == ic.cached_instance_shape {
                        // IC HIT! Return cached method bits
                        return ic.cached_method_bits;
                    }
                }
            }
        }
    }

    0 // IC miss
}

/// Inline-cache-guarded Self_ dispatch.
///
/// On IC hit: loads cached method directly (zero hash lookups on __index table).
/// On IC miss: does full resolution (same as jit_rt_self_fast) and updates the IC.
///
/// The IC is guarded by (metatable identity, __index table version).
/// Both `cat:speak()` and `dog:speak()` hit the same IC as long as they share
/// the same metatable whose __index table hasn't been modified.
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
/// - `ic_ptr` must be a valid pointer to a `SelfIcEntry`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_self_ic(
    vm_ptr: *mut Vm,
    base: u64,
    a: u64,
    b: u64,
    key_bits: u64,
    ic_ptr: u64,
) -> i64 {
    use selune_vm::vm::SelfIcEntry;

    let vm = &mut *vm_ptr;
    let base = base as usize;
    let a = a as usize;
    let b = b as usize;

    let table_val = vm.stack[base + b];
    // R[A+1] = R[B] (self/receiver)
    vm.stack[base + a + 1] = table_val;

    let ic = &mut *(ic_ptr as *mut SelfIcEntry);

    // Fast path: if receiver is a table, try IC hit
    if let Some(table_idx) = table_val.as_table_idx() {
        let table = vm.gc.get_table(table_idx);

        // Check metatable for IC path
        if let Some(mt_idx) = table.metatable {
            let mt_tag = mt_idx.0 as u64 + 1;

            if ic.cached_mt_tag == mt_tag {
                // Metatable matches — check __index table version
                let idx_tbl_idx = ic.cached_index_table_idx as u32;
                let idx_table = vm.gc.get_table(
                    selune_core::gc::GcIdx(idx_tbl_idx, std::marker::PhantomData),
                );
                if idx_table.version as u64 == ic.cached_version {
                    // IC HIT!
                    // Check if instance shape changed since IC was populated.
                    // If not, the instance doesn't have this key (skip raw lookup).
                    if table.shape_version as u64 != ic.cached_instance_shape {
                        // Shape changed — need to check for instance override
                        let key = TValue::from_raw_bits(key_bits);
                        if let Some(sid) = key.as_string_id() {
                            let raw = table.raw_get_str(sid);
                            if !raw.is_nil() {
                                vm.stack[base + a] = raw;
                                return 0;
                            }
                        }
                        // Key not on instance — update cached shape
                        ic.cached_instance_shape = table.shape_version as u64;
                    }
                    // Use cached method (no instance override)
                    vm.stack[base + a] = TValue::from_raw_bits(ic.cached_method_bits);
                    return 0;
                }
            }

            // IC miss — do full resolution
            let key = TValue::from_raw_bits(key_bits);
            let key_sid = key.as_string_id();

            // Step 1: raw lookup on instance
            let raw_result = if let Some(sid) = key_sid {
                vm.gc.get_table(table_idx).raw_get_str(sid)
            } else {
                vm.gc.table_raw_get(table_idx, key)
            };

            if !raw_result.is_nil() {
                vm.stack[base + a] = raw_result;
                return 0;
            }

            // Step 2: resolve via metatable.__index
            let mm_index_name = vm.mm_names.as_ref().unwrap().index;
            let mm_val = vm.gc.get_table(mt_idx).raw_get_str(mm_index_name);

            if let Some(idx_table_idx) = mm_val.as_table_idx() {
                let idx_result = if let Some(sid) = key_sid {
                    vm.gc.get_table(idx_table_idx).raw_get_str(sid)
                } else {
                    vm.gc.table_raw_get(idx_table_idx, key)
                };

                if !idx_result.is_nil() {
                    // Update IC
                    let idx_table = vm.gc.get_table(idx_table_idx);
                    let inst_table = vm.gc.get_table(table_idx);
                    ic.cached_mt_tag = mt_tag;
                    ic.cached_index_table_idx = idx_table_idx.0 as u64;
                    ic.cached_version = idx_table.version as u64;
                    ic.cached_method_bits = idx_result.raw_bits();
                    ic.cached_instance_shape = inst_table.shape_version as u64;

                    // Cache callee JIT function info for Self_+Call fusion
                    ic.cached_closure_idx = 0;
                    ic.cached_proto_idx = 0;
                    ic.cached_jit_fn_ptr = 0;
                    if let Some(closure_idx) = idx_result.as_closure_idx() {
                        let closure = vm.gc.get_closure(closure_idx);
                        let proto_idx = closure.proto_idx;
                        ic.cached_closure_idx = closure_idx.0 as u64;
                        ic.cached_proto_idx = proto_idx as u64;
                        if let Some(JitProtoState::Compiled(jit_fn)) =
                            vm.jit_proto_state.get(proto_idx)
                        {
                            ic.cached_jit_fn_ptr = *jit_fn as u64;
                        }
                    }

                    vm.stack[base + a] = idx_result;
                    return 0;
                }
            }
            // Fall through to slow path
        } else {
            // No metatable — check raw lookup
            let key = TValue::from_raw_bits(key_bits);
            if let Some(sid) = key.as_string_id() {
                let raw = table.raw_get_str(sid);
                if !raw.is_nil() {
                    vm.stack[base + a] = raw;
                    return 0;
                }
            }
            vm.stack[base + a] = TValue::nil();
            return 0;
        }
    }

    // Slow path: full metamethod dispatch
    let key = TValue::from_raw_bits(key_bits);
    match table_index(vm, table_val, key) {
        Ok(result) => {
            vm.stack[base + a] = result;
            0
        }
        Err(_) => SIDE_EXIT,
    }
}

/// Fused Self_+Call: IC-guarded method resolution + direct JIT-to-JIT dispatch.
///
/// Combines `jit_rt_self_ic_check_fast` + `jit_rt_call_fast` into a single extern "C" call.
/// On IC hit with a cached JIT function pointer, does the full JIT-to-JIT call internally
/// (push JitCallInfo, indirect call, pop, copy results) without any intermediate extern "C" overhead.
///
/// On IC miss or no cached JIT fn: falls back to separate Self_ resolution + generic call_fast.
///
/// Returns: number of results placed (>=0), or SIDE_EXIT on error/deopt.
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
/// - `ic_ptr` must be a valid pointer to a `SelfIcEntry`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_self_call_ic(
    vm_ptr: *mut Vm,
    base: u64,
    a: u64,
    b: u64,
    key_bits: u64,
    ic_ptr: u64,
    nargs: u64,
    nresults: i64,
) -> i64 {
    use selune_vm::vm::SelfIcEntry;

    let vm = &mut *vm_ptr;
    let base = base as usize;
    let a = a as usize;
    let b_val = b as usize;

    let table_val = *vm.stack.get_unchecked(base + b_val);
    // R[A+1] = R[B] (self/receiver)
    *vm.stack.get_unchecked_mut(base + a + 1) = table_val;

    let ic = &mut *(ic_ptr as *mut SelfIcEntry);
    let nargs = nargs as usize;

    // --- IC probe ---
    if let Some(table_idx) = table_val.as_table_idx() {
        if ic.cached_mt_tag != 0 {
            let table = vm.gc.get_table_unchecked(table_idx);
            let mt_raw = table.metatable_raw();
            if mt_raw as u64 + 1 == ic.cached_mt_tag {
                let idx_tbl_idx = ic.cached_index_table_idx as u32;
                let idx_table = vm.gc.get_table_unchecked(
                    selune_core::gc::GcIdx(idx_tbl_idx, std::marker::PhantomData),
                );
                if idx_table.version as u64 == ic.cached_version {
                    // Check instance shape
                    let mut method_bits = ic.cached_method_bits;
                    if table.shape_version as u64 != ic.cached_instance_shape {
                        // Shape changed — check for instance override
                        let key = TValue::from_raw_bits(key_bits);
                        if let Some(sid) = key.as_string_id() {
                            let raw = table.raw_get_str(sid);
                            if !raw.is_nil() {
                                method_bits = raw.raw_bits();
                            } else {
                                ic.cached_instance_shape = table.shape_version as u64;
                            }
                        }
                    }

                    // IC HIT! Store method to R[A]
                    let method = TValue::from_raw_bits(method_bits);
                    let func_idx = base + a;
                    *vm.stack.get_unchecked_mut(func_idx) = method;

                    // --- Try tiny method inlining ---
                    if let Some(closure_idx) = method.as_closure_idx() {
                        let closure = vm.gc.get_closure(closure_idx);
                        let proto_idx = closure.proto_idx;
                        if let TinyMethodKind::Getter { field_sid } = *vm.tiny_methods.get_unchecked(proto_idx) {
                            // self is at R[A+1] (already stored above)
                            let self_val = *vm.stack.get_unchecked(base + a + 1);
                            if let Some(tbl_idx) = self_val.as_table_idx() {
                                let table = vm.gc.get_table_unchecked(tbl_idx);
                                let result = table.raw_get_str(StringId(field_sid));
                                if !result.is_nil() {
                                    if nresults == 1 {
                                        *vm.stack.get_unchecked_mut(func_idx) = result;
                                        return 1;
                                    } else if nresults == 0 {
                                        return 0;
                                    } else if nresults < 0 {
                                        *vm.stack.get_unchecked_mut(func_idx) = result;
                                        return 1;
                                    } else {
                                        *vm.stack.get_unchecked_mut(func_idx) = result;
                                        for i in 1..nresults as usize {
                                            *vm.stack.get_unchecked_mut(func_idx + i) = TValue::nil();
                                        }
                                        return nresults;
                                    }
                                }
                                // raw_get_str returned nil — field might be on metatable, fall through
                            }
                        }
                    }

                    // --- Try fused JIT-to-JIT call ---
                    if ic.cached_jit_fn_ptr != 0 && method_bits == ic.cached_method_bits {
                        // Verify the callee is still the same closure
                        if let Some(closure_idx) = method.as_closure_idx() {
                            if closure_idx.0 as u64 == ic.cached_closure_idx {
                                let jit_fn: JitFn = std::mem::transmute(ic.cached_jit_fn_ptr as usize);
                                let child_proto_idx = ic.cached_proto_idx as usize;
                                let child_proto = vm.protos.get_unchecked(child_proto_idx);
                                let num_params = child_proto.num_params as usize;
                                let max_stack = child_proto.max_stack_size as usize;

                                // Stack depth check
                                if vm.call_stack.len() + vm.jit_call_stack.len() >= vm.max_call_depth {
                                    return SIDE_EXIT;
                                }

                                let new_base = func_idx + 1;

                                // Save/restore stack_top
                                let saved_stack_top = vm.stack_top;
                                let arg_end = new_base + nargs;
                                if vm.stack_top < arg_end {
                                    vm.stack_top = arg_end;
                                }

                                // Ensure stack space
                                let needed = new_base + max_stack + num_params + 1;
                                if needed > vm.stack.len() {
                                    vm.stack.resize(needed, TValue::nil());
                                    vm.update_stack_data_ptr();
                                }

                                // Nil-pad args if needed
                                for i in nargs..num_params {
                                    *vm.stack.get_unchecked_mut(new_base + i) = TValue::nil();
                                }

                                // Push JitCallInfo
                                let jit_ci = JitCallInfo {
                                    base: new_base,
                                    func_stack_idx: func_idx,
                                    proto_idx: child_proto_idx,
                                    closure_idx_raw: closure_idx.0,
                                    num_results: nresults as i32,
                                };
                                vm.jit_call_stack.push(jit_ci);

                                // Direct JIT call
                                let result = jit_fn(vm as *mut Vm, new_base);

                                if result >= 0 {
                                    if !vm.open_upvals.is_empty() {
                                        vm.close_upvalues(new_base);
                                    }
                                    vm.jit_call_stack.pop();
                                    vm.stack_top = saved_stack_top;

                                    // Copy results
                                    if nresults == 1 {
                                        *vm.stack.get_unchecked_mut(func_idx) = if result > 0 { *vm.stack.get_unchecked(new_base) } else { TValue::nil() };
                                        return 1;
                                    } else if nresults == 0 {
                                        return 0;
                                    } else {
                                        let nresults_actual = result as usize;
                                        let wanted = if nresults < 0 { nresults_actual as i64 } else { nresults };
                                        let n = (wanted as usize).min(nresults_actual);
                                        for i in 0..n {
                                            *vm.stack.get_unchecked_mut(func_idx + i) = *vm.stack.get_unchecked(new_base + i);
                                        }
                                        for i in n..wanted as usize {
                                            *vm.stack.get_unchecked_mut(func_idx + i) = TValue::nil();
                                        }
                                        return wanted;
                                    }
                                } else {
                                    // SIDE_EXIT from callee
                                    vm.jit_call_stack.pop();
                                    vm.jit_record_side_exit(child_proto_idx);
                                    vm.stack_top = saved_stack_top;
                                    // Invalidate cached JIT fn (callee was blacklisted)
                                    ic.cached_jit_fn_ptr = 0;
                                    // Fall through to generic call_fast for interpreter fallback
                                }
                            }
                        }
                    } else if ic.cached_jit_fn_ptr == 0 && method_bits == ic.cached_method_bits {
                        // JIT fn not cached yet — try to refresh it
                        if let Some(closure_idx) = method.as_closure_idx() {
                            let closure = vm.gc.get_closure(closure_idx);
                            let proto_idx = closure.proto_idx;
                            if let Some(JitProtoState::Compiled(jit_fn)) = vm.jit_proto_state.get(proto_idx) {
                                ic.cached_closure_idx = closure_idx.0 as u64;
                                ic.cached_proto_idx = proto_idx as u64;
                                ic.cached_jit_fn_ptr = *jit_fn as u64;
                            }
                        }
                    }

                    // IC hit but no fused call — fall through to generic call_fast
                    return jit_rt_call_fast(vm_ptr, base as u64, a as u64, nargs as u64, nresults);
                }
            }
        }
    }

    // --- IC miss: full Self_ resolution + call ---
    // Call jit_rt_self_ic for the Self_ part
    let self_result = jit_rt_self_ic(vm_ptr, base as u64, a as u64, b, key_bits, ic_ptr);
    if self_result == SIDE_EXIT {
        return SIDE_EXIT;
    }

    // Then call_fast for the Call part
    jit_rt_call_fast(vm_ptr, base as u64, a as u64, nargs as u64, nresults)
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
// Fast string-keyed field access helpers (GetField/SetField optimization)
// ---------------------------------------------------------------------------

/// Fast GetField for string constant keys: R[A] = R[B][K[C]]
/// Takes StringId.0 directly (avoids NaN-unboxing the key TValue).
/// Fast path: raw_get_str first. If found, return immediately.
/// If not found and no metatable, return nil.
/// If not found and has metatable, fall back to full table_index.
/// Returns result as raw TValue bits.
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_get_field_str(
    vm_ptr: *mut Vm,
    table_bits: u64,
    string_id: u64,
) -> u64 {
    let vm = &mut *vm_ptr;
    let sid = StringId(string_id as u32);
    if let Some(table_idx) = TValue::from_raw_bits(table_bits).as_table_idx() {
        let table = vm.gc.get_table_unchecked(table_idx);
        // Try raw lookup first — works whether or not table has a metatable
        let result = table.raw_get_str(sid);
        if !result.is_nil() {
            return result.raw_bits();
        }
        // Key not found: check metatable
        if table.metatable.is_none() {
            return TValue::nil().raw_bits();
        }
    }
    // Slow path: full metamethod chain
    let table_val = TValue::from_raw_bits(table_bits);
    let key = TValue::from_string_id(sid);
    match table_index(vm, table_val, key) {
        Ok(result) => result.raw_bits(),
        Err(_) => TValue::nil().raw_bits(),
    }
}

/// Fast SetField for string constant keys: R[A][K[B]] = RK(C)
/// Takes StringId.0 directly (avoids NaN-unboxing the key TValue).
/// Fast path: raw_get_str first. If key exists, overwrite in-place (no alloc → return 0).
/// If key doesn't exist and no metatable, insert new key (possible alloc → return 1).
/// If key doesn't exist and has metatable, fall back to full table_newindex.
/// Returns: 0 = no-alloc (existing key overwrite), 1 = possible alloc, SIDE_EXIT = error.
///
/// # Safety
/// - `vm_ptr` must be a valid pointer to a live `Vm`.
#[no_mangle]
pub unsafe extern "C" fn jit_rt_set_field_str(
    vm_ptr: *mut Vm,
    table_bits: u64,
    string_id: u64,
    val_bits: u64,
) -> i64 {
    let vm = &mut *vm_ptr;
    let sid = StringId(string_id as u32);
    let val = TValue::from_raw_bits(val_bits);
    if let Some(table_idx) = TValue::from_raw_bits(table_bits).as_table_idx() {
        let table = vm.gc.get_table_unchecked(table_idx);
        // Check if key already exists
        let existing = table.raw_get_str(sid);
        if !existing.is_nil() {
            // Key exists: overwrite in-place, no allocation needed
            vm.gc.get_table_mut_unchecked(table_idx).raw_set_str(sid, val);
            return 0; // no-alloc fast path
        }
        // Key doesn't exist
        if table.metatable.is_none() {
            // No metatable: insert directly
            vm.gc.get_table_mut_unchecked(table_idx).raw_set_str(sid, val);
            return 1; // possible alloc (new key insertion)
        }
    }
    // Slow path: full metamethod chain
    let table_val = TValue::from_raw_bits(table_bits);
    let key = TValue::from_string_id(sid);
    match table_newindex(vm, table_val, key, val) {
        Ok(()) => 1,
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
            vm.update_stack_data_ptr();
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
                            vm.update_stack_data_ptr();
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
            vm.update_stack_data_ptr();
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
                        vm.update_stack_data_ptr();
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
                vm.update_stack_data_ptr();
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
        vm.update_stack_data_ptr();
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
        // If the innermost frame is a JIT shadow frame, side-exit — JitCallInfo has no tbc_slots.
        if !vm.jit_call_stack.is_empty() {
            return SIDE_EXIT;
        }
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

    let closure_idx_opt = vm.current_closure_idx();

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
            vm.update_stack_data_ptr();
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
            vm.update_stack_data_ptr();
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

