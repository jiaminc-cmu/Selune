//! Main bytecode dispatch loop.

use crate::arith::{self, ArithOp};
use crate::callinfo::{CallInfo, CallStatus, CloseReturnYieldData};
use crate::coerce;
use crate::compare;
use crate::error::LuaError;
use crate::metamethod;
use crate::vm::Vm;
use selune_compiler::opcode::OpCode;
use selune_compiler::proto::{Constant, Proto};
use selune_core::gc::{GcIdx, NativeContext, NativeError};
use selune_core::value::TValue;

/// Format a runtime error with "source:line: " prefix using current call stack state.
pub fn runtime_error(vm: &Vm, msg: &str) -> LuaError {
    let prefix = get_error_prefix(vm, 0);
    LuaError::Runtime(format!("{}{}", prefix, msg))
}

/// Add source:line prefix to a runtime error if it doesn't already have one.
pub fn add_error_prefix(vm: &Vm, err: LuaError) -> LuaError {
    match err {
        LuaError::Runtime(msg) => {
            let prefix = get_error_prefix(vm, 0);
            // Don't add prefix if it already starts with this exact prefix
            if !prefix.is_empty() && msg.starts_with(&prefix) {
                LuaError::Runtime(msg)
            } else {
                LuaError::Runtime(format!("{}{}", prefix, msg))
            }
        }
        other => other,
    }
}

/// Get error prefix "source:line: " for a given call stack level offset.
/// Level 0 = current frame, 1 = caller, etc.
fn get_error_prefix(vm: &Vm, level: usize) -> String {
    // Walk backwards through call stack to find the right Lua frame
    let mut lua_level = 0;
    for i in (0..vm.call_stack.len()).rev() {
        let ci = &vm.call_stack[i];
        if ci.proto_idx < vm.protos.len() {
            if lua_level == level {
                let proto = &vm.protos[ci.proto_idx];
                let source = proto
                    .source
                    .map(|sid| {
                        let bytes = vm.strings.get_bytes(sid);
                        let s = String::from_utf8_lossy(bytes);
                        crate::vm::format_source_name(&s)
                    })
                    .unwrap_or_else(|| "?".to_string());
                let line: i32 = if proto.line_info.is_empty() {
                    -1
                } else if ci.pc > 0 {
                    proto.get_line(ci.pc - 1) as i32
                } else {
                    proto.get_line(0) as i32
                };
                return format!("{}:{}: ", source, line);
            }
            lua_level += 1;
        }
    }
    String::new()
}

/// Try to find a descriptive name for the value in the given register.
/// Returns something like " (field 'huge')" or " (local 'x')" or empty string.
/// Mirrors Lua 5.4's getobjname/basicgetobjname/findsetreg from ldebug.c.
fn get_obj_name(vm: &Vm, ci_idx: usize, reg: usize) -> String {
    let ci = &vm.call_stack[ci_idx];
    if ci.proto_idx >= vm.protos.len() {
        return String::new();
    }
    let proto = &vm.protos[ci.proto_idx];
    // ci.pc points past the current instruction (already incremented)
    let lastpc = if ci.pc > 1 {
        ci.pc - 1
    } else {
        return String::new();
    };

    // Check if instruction at lastpc is an MM instruction (MMBin, MMBinI, MMBinK)
    // If so, back up one since the previous instruction was not actually executed
    let lastpc = if lastpc > 0 {
        let op = proto.code[lastpc].opcode();
        if op == OpCode::MMBin || op == OpCode::MMBinI || op == OpCode::MMBinK {
            lastpc - 1
        } else {
            lastpc
        }
    } else {
        lastpc
    };

    getobjname(vm, proto, lastpc, reg)
}

/// Find the last unconditional instruction before `lastpc` that set register `reg`.
/// Returns -1 if no such instruction found.
/// Mirrors Lua 5.4's findsetreg from ldebug.c.
fn findsetreg(proto: &Proto, lastpc: usize, reg: usize) -> i32 {
    let mut setreg: i32 = -1;
    let mut jmptarget: usize = 0; // any code before this address is conditional

    for pc in 0..lastpc {
        let inst = proto.code[pc];
        let op = inst.opcode();
        let a = inst.a() as usize;

        let change = match op {
            OpCode::LoadNil => {
                // Sets registers from a to a+b
                let b = inst.b() as usize;
                reg >= a && reg <= a + b
            }
            OpCode::TForCall => {
                // Affects all regs above its base + 2
                reg >= a + 2
            }
            OpCode::Call | OpCode::TailCall => {
                // Affects all registers above base
                reg >= a
            }
            OpCode::Jmp => {
                let sj = inst.get_sj();
                let dest = (pc as i32 + 1 + sj) as usize;
                if dest <= lastpc && dest > jmptarget {
                    jmptarget = dest;
                }
                false
            }
            _ => {
                // Any instruction that sets register A
                sets_reg_a(op) && reg == a
            }
        };

        if change {
            // filterpc: if pc < jmptarget, this is conditional → -1
            setreg = if pc < jmptarget { -1 } else { pc as i32 };
        }
    }

    setreg
}

/// Check if an opcode sets register A (testAMode equivalent).
fn sets_reg_a(op: OpCode) -> bool {
    match op {
        // Instructions that do NOT set register A:
        OpCode::SetTabUp
        | OpCode::SetTable
        | OpCode::SetI
        | OpCode::SetField
        | OpCode::SetUpval
        | OpCode::SetList
        | OpCode::MMBin
        | OpCode::MMBinI
        | OpCode::MMBinK
        | OpCode::Jmp
        | OpCode::Test
        | OpCode::Eq
        | OpCode::Lt
        | OpCode::Le
        | OpCode::EqK
        | OpCode::EqI
        | OpCode::LtI
        | OpCode::LeI
        | OpCode::GtI
        | OpCode::GeI
        | OpCode::Return
        | OpCode::Return0
        | OpCode::Return1
        | OpCode::Close
        | OpCode::Tbc
        | OpCode::ExtraArg
        | OpCode::VarArgPrep => false,
        // All others set register A
        _ => true,
    }
}

/// Check if upvalue b is the environment (_ENV) table for determining
/// whether a GetTabUp is a "global" or "field" access.
fn is_env(vm: &Vm, proto: &Proto, pc: usize, b: usize, is_upval: bool) -> &'static str {
    let name = if is_upval {
        // Upvalue name
        if b < proto.upvalues.len() {
            proto.upvalues[b]
                .name
                .map(|sid| String::from_utf8_lossy(vm.strings.get_bytes(sid)).into_owned())
        } else {
            None
        }
    } else {
        // Register — use basicgetobjname to find what's in that register
        let (kind, name) = basicgetobjname(vm, proto, pc, b);
        if kind == "local" || kind == "upvalue" {
            Some(name)
        } else {
            None
        }
    };
    match name {
        Some(ref n) if n == "_ENV" => "global",
        _ => "field",
    }
}

/// Basic object name resolution: checks locals first, then symbolic execution.
/// Returns (kind, name) where kind is "local", "upvalue", "constant", or "".
/// Mirrors Lua 5.4's basicgetobjname.
fn basicgetobjname(vm: &Vm, proto: &Proto, lastpc: usize, reg: usize) -> (&'static str, String) {
    // First check if `reg` is a known local variable at the current PC
    for lv in &proto.local_vars {
        if lv.reg as usize == reg
            && (lv.start_pc as usize) <= lastpc
            && lastpc < (lv.end_pc as usize)
        {
            let name = String::from_utf8_lossy(vm.strings.get_bytes(lv.name));
            if !name.starts_with('(') {
                return ("local", name.into_owned());
            }
        }
    }

    // Symbolic execution: find the instruction that set this register
    let pc = findsetreg(proto, lastpc, reg);
    if pc == -1 {
        return ("", String::new());
    }
    let pc = pc as usize;
    let inst = proto.code[pc];
    let op = inst.opcode();

    match op {
        OpCode::Move => {
            let b = inst.b() as usize;
            if b < inst.a() as usize {
                return basicgetobjname(vm, proto, pc, b);
            }
        }
        OpCode::GetUpval => {
            let b = inst.b() as usize;
            if b < proto.upvalues.len() {
                if let Some(name_sid) = proto.upvalues[b].name {
                    let name = String::from_utf8_lossy(vm.strings.get_bytes(name_sid));
                    return ("upvalue", name.into_owned());
                }
            }
        }
        OpCode::LoadK => {
            let bx = inst.bx() as usize;
            if bx < proto.constants.len() {
                if let Constant::String(sid) = &proto.constants[bx] {
                    let name = String::from_utf8_lossy(vm.strings.get_bytes(*sid));
                    return ("constant", name.into_owned());
                }
            }
        }
        OpCode::LoadKX => {
            // The constant index is in the next instruction's Ax field
            if pc + 1 < proto.code.len() {
                let ax = proto.code[pc + 1].ax_field() as usize;
                if ax < proto.constants.len() {
                    if let Constant::String(sid) = &proto.constants[ax] {
                        let name = String::from_utf8_lossy(vm.strings.get_bytes(*sid));
                        return ("constant", name.into_owned());
                    }
                }
            }
        }
        _ => {}
    }

    ("", String::new())
}

/// Full object name resolution including table accesses.
/// Returns formatted string like " (global 'x')" or " (local 'f')" or "".
/// Mirrors Lua 5.4's getobjname.
fn getobjname(vm: &Vm, proto: &Proto, lastpc: usize, reg: usize) -> String {
    let (kind, name) = basicgetobjname(vm, proto, lastpc, reg);
    if !kind.is_empty() {
        return format!(" ({} '{}')", kind, name);
    }

    // If basicgetobjname couldn't determine a name, look at the instruction
    // that set the register
    let pc = findsetreg(proto, lastpc, reg);
    if pc == -1 {
        return String::new();
    }
    let pc = pc as usize;
    let inst = proto.code[pc];
    let op = inst.opcode();

    match op {
        OpCode::GetTabUp => {
            let b = inst.b() as usize;
            let c = inst.c() as usize;
            if c < proto.constants.len() {
                if let Constant::String(sid) = &proto.constants[c] {
                    let name = String::from_utf8_lossy(vm.strings.get_bytes(*sid));
                    let kind = is_env(vm, proto, pc, b, true);
                    return format!(" ({} '{}')", kind, name);
                }
            }
        }
        OpCode::GetTable => {
            let c = inst.c() as usize;
            // rname: only use the name if the key is a constant
            let (kind, key_name) = basicgetobjname(vm, proto, pc, c);
            if kind == "constant" && !key_name.is_empty() {
                let b = inst.b() as usize;
                let env_kind = is_env(vm, proto, pc, b, false);
                return format!(" ({} '{}')", env_kind, key_name);
            }
        }
        OpCode::GetI => {
            return " (field 'integer index')".to_string();
        }
        OpCode::GetField => {
            let c = inst.c() as usize;
            if c < proto.constants.len() {
                if let Constant::String(sid) = &proto.constants[c] {
                    let name = String::from_utf8_lossy(vm.strings.get_bytes(*sid));
                    let b = inst.b() as usize;
                    let kind = is_env(vm, proto, pc, b, false);
                    return format!(" ({} '{}')", kind, name);
                }
            }
        }
        OpCode::Self_ => {
            // rkname: check if k flag is set for constant key, otherwise register key
            let c = inst.c() as usize;
            if inst.k() {
                if c < proto.constants.len() {
                    if let Constant::String(sid) = &proto.constants[c] {
                        let name = String::from_utf8_lossy(vm.strings.get_bytes(*sid));
                        return format!(" (method '{}')", name);
                    }
                }
            } else {
                let (_, key_name) = basicgetobjname(vm, proto, pc, c);
                if !key_name.is_empty() {
                    return format!(" (method '{}')", key_name);
                }
            }
        }
        _ => {}
    }

    String::new()
}

/// Enhance a bitwise operation error with source info about which operand failed.
/// `b_reg` and `c_reg` are the register indices of the two operands (c_reg may be None for immediate ops).
fn enhance_bitwise_error(
    vm: &Vm,
    ci_idx: usize,
    e: LuaError,
    b_reg: usize,
    c_reg: Option<usize>,
    vb: TValue,
    vc: TValue,
) -> LuaError {
    match e {
        LuaError::Runtime(msg) if msg.contains("no integer representation") => {
            // Determine which operand caused the error
            let obj_name = if vb.is_float() {
                get_obj_name(vm, ci_idx, b_reg)
            } else if let Some(c) = c_reg {
                if vc.is_float() {
                    get_obj_name(vm, ci_idx, c)
                } else {
                    String::new()
                }
            } else {
                String::new()
            };
            let prefix = get_error_prefix(vm, 0);
            LuaError::Runtime(format!("{}{}{}", prefix, msg, obj_name))
        }
        other => add_error_prefix(vm, other),
    }
}

/// Get the type name for a value, checking __name metafield first.
/// Mirrors Lua 5.4's luaT_objtypename.
fn obj_type_name(val: TValue, vm: &Vm) -> String {
    selune_core::object::obj_type_name(val, &vm.gc, &vm.strings)
}

/// Generate an order comparison error message.
/// When types are the same: "attempt to compare two X values"
/// When types differ: "attempt to compare X with Y"
fn order_error(vm: &Vm, va: TValue, vb: TValue) -> LuaError {
    let t1 = obj_type_name(va, vm);
    let t2 = obj_type_name(vb, vm);
    if t1 == t2 {
        runtime_error(vm, &format!("attempt to compare two {} values", t1))
    } else {
        runtime_error(vm, &format!("attempt to compare {} with {}", t1, t2))
    }
}

/// Get a constant from the current proto, cloned to avoid borrow issues.
#[inline]
/// Execute starting from proto at the given index, returning results.
pub fn execute(vm: &mut Vm, _start_proto_idx: usize) -> Result<Vec<TValue>, LuaError> {
    execute_from(vm, 1)
}

/// Execute the dispatch loop, returning when call_stack depth drops to entry_depth.
pub fn execute_from(vm: &mut Vm, entry_depth: usize) -> Result<Vec<TValue>, LuaError> {
    loop {
        let mut ci_idx = vm.call_stack.len() - 1;
        let mut base = vm.call_stack[ci_idx].base;
        let proto_idx = vm.call_stack[ci_idx].proto_idx;

        // Check if this frame was suspended during close-on-return (fast guard)
        if vm.needs_close_return_resume {
            vm.needs_close_return_resume = false;
            if let CallStatus::CloseReturnYield(_) = &vm.call_stack[ci_idx].call_status {
                // Extract the saved results
                let saved = std::mem::replace(
                    &mut vm.call_stack[ci_idx].call_status,
                    CallStatus::Normal,
                );
                let results = match saved {
                    CallStatus::CloseReturnYield(data) => data.saved_results,
                    _ => unreachable!(),
                };

                // Close any remaining TBC variables for this frame
                match close_tbc_variables(vm, ci_idx, base, None) {
                    Ok(()) => {}
                    Err(LuaError::Yield(vals)) => {
                        // Yield again during remaining closes
                        vm.needs_close_return_resume = true;
                        vm.call_stack[ci_idx].call_status = CallStatus::CloseReturnYield(Box::new(CloseReturnYieldData {
                            saved_results: results,
                            remaining_tbc_slots: vec![],
                        }));
                        return Err(LuaError::Yield(vals));
                    }
                    Err(e) => return Err(e),
                }

                // Close upvalues
                vm.close_upvalues(base);

                // Complete the return
                if vm.call_stack.len() <= entry_depth {
                    return Ok(results);
                }
                return_from_call(vm, &results)?;
                continue;
            }
        }

        let mut pc = vm.call_stack[ci_idx].pc;
        if pc >= vm.protos[proto_idx].code.len() {
            // Fell off the end — return empty
            if vm.call_stack.len() <= entry_depth {
                return Ok(vec![]);
            }
            // Return from nested call
            let results = vec![];
            return_from_call(vm, &results)?;
            continue;
        }

        // Hook dispatch: line and count hooks
        if vm.hooks_active && !vm.in_hook && vm.call_stack[ci_idx].is_lua() {
            // Count hook: decrement first, fire when it reaches 0 (PUC Lua style)
            if vm.hook_mask & HOOK_COUNT != 0 {
                vm.hook_counter = vm.hook_counter.wrapping_sub(1);
                if vm.hook_counter == 0 {
                    vm.hook_counter = vm.hook_count;
                    // Temporarily raise stack_top to protect all frame registers.
                    // After multi-return calls, stack_top may be lowered to reflect
                    // the result count, but the hook function must be placed above
                    // all active registers to avoid overwriting them.
                    let saved_hook_top = vm.stack_top;
                    let max_stack =
                        vm.protos[proto_idx].max_stack_size as usize;
                    let frame_top = base + max_stack;
                    if vm.stack_top < frame_top {
                        vm.stack_top = frame_top;
                    }
                    vm.call_stack[ci_idx].pc = pc;
                    fire_hook(vm, "count", -1, entry_depth)?;
                    vm.stack_top = saved_hook_top;
                    // Re-read ci_idx/base/pc after hook (hook may change call stack)
                    ci_idx = vm.call_stack.len() - 1;
                    base = vm.call_stack[ci_idx].base;
                    pc = vm.call_stack[ci_idx].pc;
                }
            }
            // Line hook
            if vm.hook_mask & HOOK_LINE != 0 && vm.call_stack[ci_idx].is_lua() {
                let proto = &vm.protos[proto_idx];
                let raw_line = proto.get_line(pc);
                // For VarArgPrep (line=0 but NOT stripped code), skip hooks entirely
                // For stripped code, all instructions have line=0; detect via lineinfo emptiness
                let is_stripped = proto.line_info.is_empty();
                if raw_line == 0 && !is_stripped {
                    // VarArgPrep: just update hook_old_pc
                    vm.hook_old_pc = pc;
                } else {
                    // For stripped code: line = -1 (fire_hook converts to nil)
                    // For normal code: line = raw_line
                    let line = if is_stripped { -1i32 } else { raw_line as i32 };
                    // PUC's line hook logic (luaG_traceexec):
                    // hook_old_pc is PUC's L->oldpc equivalent (global, not per-frame)
                    let old_pc = vm.hook_old_pc;
                    // Validate old_pc is within this proto (may be stale from another frame)
                    let old_pc = if old_pc < proto.code.len() { old_pc } else { 0 };
                    // PUC: fire when npci <= oldpc (backward jump) OR changedline
                    let fire = pc <= old_pc || changedline(proto, old_pc, pc);
                    vm.hook_old_pc = pc;
                    if fire {
                        let new_line = line;
                        vm.hook_last_line = new_line;
                        // Same stack_top protection for line hooks
                        let saved_hook_top = vm.stack_top;
                        let max_stack = proto.max_stack_size as usize;
                        let frame_top = base + max_stack;
                        if vm.stack_top < frame_top {
                            vm.stack_top = frame_top;
                        }
                        vm.call_stack[ci_idx].pc = pc;
                        fire_hook(vm, "line", new_line, entry_depth)?;
                        vm.stack_top = saved_hook_top;
                        // Re-read ci_idx/base/pc after hook
                        ci_idx = vm.call_stack.len() - 1;
                        base = vm.call_stack[ci_idx].base;
                        pc = vm.call_stack[ci_idx].pc;
                    }
                } // end else
            }
        }

        let inst = vm.protos[proto_idx].code[pc];
        let op = inst.opcode();
        let a = inst.a() as usize;

        // Advance PC
        pc += 1;

        match op {
            OpCode::Move => {
                let b = inst.b() as usize;
                let val = vm.stack[base + b];
                vm.stack[base + a] = val;
            }

            OpCode::LoadI => {
                let sbx = inst.sbx();
                vm.stack[base + a] = TValue::from_full_integer(sbx as i64, &mut vm.gc);
            }

            OpCode::LoadF => {
                let sbx = inst.sbx();
                vm.stack[base + a] = TValue::from_float(sbx as f64);
            }

            OpCode::LoadK => {
                let bx = inst.bx() as usize;
                let proto = &vm.protos[proto_idx];
                let val = constant_to_tvalue(&proto.constants[bx], &mut vm.gc);
                vm.stack[base + a] = val;
            }

            OpCode::LoadKX => {
                let proto = &vm.protos[proto_idx];
                let next_inst = proto.code[pc];
                pc += 1;
                let ax = next_inst.ax_field() as usize;
                let val = constant_to_tvalue(&proto.constants[ax], &mut vm.gc);
                vm.stack[base + a] = val;
            }

            OpCode::LoadFalse => {
                vm.stack[base + a] = TValue::from_bool(false);
            }

            OpCode::LFalseSkip => {
                vm.stack[base + a] = TValue::from_bool(false);
                pc += 1;
            }

            OpCode::LoadTrue => {
                vm.stack[base + a] = TValue::from_bool(true);
            }

            OpCode::LoadNil => {
                let b = inst.b() as usize;
                for i in a..=a + b {
                    vm.stack[base + i] = TValue::nil();
                }
            }

            // ---- Arithmetic (register-register) with inline fast paths ----
            // On success: store result and skip next MMBIN instruction.
            // On NeedMetamethod: don't skip, let MMBIN handle it.
            OpCode::Add => {
                let b = inst.b() as usize;
                let c = inst.c() as usize;
                let vb = vm.stack[base + b];
                let vc = vm.stack[base + c];
                // Fast path 1: both inline integers (no GC needed)
                if vb.is_integer() && vc.is_integer() {
                    let ib = unsafe { vb.as_integer_unchecked() };
                    let ic = unsafe { vc.as_integer_unchecked() };
                    let result = ib.wrapping_add(ic);
                    vm.stack[base + a] =
                        if result >= selune_core::value::SMALL_INT_MIN
                            && result <= selune_core::value::SMALL_INT_MAX
                        {
                            unsafe { TValue::from_integer_unchecked(result) }
                        } else {
                            TValue::from_full_integer(result, &mut vm.gc)
                        };
                    pc += 1;
                }
                // Fast path 2: both floats (not tagged)
                else if !vb.is_tagged() && !vc.is_tagged() {
                    vm.stack[base + a] = TValue::from_float(
                        unsafe { vb.as_float_unchecked() + vc.as_float_unchecked() });
                    pc += 1;
                }
                // Fast path 3: any integer (inline or boxed)
                else if let (Some(ib), Some(ic)) = (vb.try_as_i64(&vm.gc), vc.try_as_i64(&vm.gc)) {
                    let result = ib.wrapping_add(ic);
                    vm.stack[base + a] = TValue::from_full_integer(result, &mut vm.gc);
                    pc += 1;
                }
                // Slow path: string coercion, metamethods
                else {
                    match arith::arith_op(ArithOp::Add, vb, vc, &mut vm.gc, &vm.strings) {
                        arith::ArithResult::Ok(result) => {
                            vm.stack[base + a] = result;
                            pc += 1;
                        }
                        arith::ArithResult::NeedMetamethod => {}
                        arith::ArithResult::Error(e) => { vm.call_stack[ci_idx].pc = pc; return Err(add_error_prefix(vm, e)); }
                    }
                }
            }
            OpCode::Sub => {
                let b = inst.b() as usize;
                let c = inst.c() as usize;
                let vb = vm.stack[base + b];
                let vc = vm.stack[base + c];
                if vb.is_integer() && vc.is_integer() {
                    let result = unsafe { vb.as_integer_unchecked().wrapping_sub(vc.as_integer_unchecked()) };
                    vm.stack[base + a] =
                        if result >= selune_core::value::SMALL_INT_MIN
                            && result <= selune_core::value::SMALL_INT_MAX
                        {
                            unsafe { TValue::from_integer_unchecked(result) }
                        } else {
                            TValue::from_full_integer(result, &mut vm.gc)
                        };
                    pc += 1;
                } else if !vb.is_tagged() && !vc.is_tagged() {
                    vm.stack[base + a] = TValue::from_float(
                        unsafe { vb.as_float_unchecked() - vc.as_float_unchecked() });
                    pc += 1;
                } else if let (Some(ib), Some(ic)) = (vb.try_as_i64(&vm.gc), vc.try_as_i64(&vm.gc)) {
                    let result = ib.wrapping_sub(ic);
                    vm.stack[base + a] = TValue::from_full_integer(result, &mut vm.gc);
                    pc += 1;
                } else {
                    match arith::arith_op(ArithOp::Sub, vb, vc, &mut vm.gc, &vm.strings) {
                        arith::ArithResult::Ok(result) => {
                            vm.stack[base + a] = result;
                            pc += 1;
                        }
                        arith::ArithResult::NeedMetamethod => {}
                        arith::ArithResult::Error(e) => { vm.call_stack[ci_idx].pc = pc; return Err(add_error_prefix(vm, e)); }
                    }
                }
            }
            OpCode::Mul => {
                let b = inst.b() as usize;
                let c = inst.c() as usize;
                let vb = vm.stack[base + b];
                let vc = vm.stack[base + c];
                if vb.is_integer() && vc.is_integer() {
                    let result = unsafe { vb.as_integer_unchecked().wrapping_mul(vc.as_integer_unchecked()) };
                    vm.stack[base + a] =
                        if result >= selune_core::value::SMALL_INT_MIN
                            && result <= selune_core::value::SMALL_INT_MAX
                        {
                            unsafe { TValue::from_integer_unchecked(result) }
                        } else {
                            TValue::from_full_integer(result, &mut vm.gc)
                        };
                    pc += 1;
                } else if !vb.is_tagged() && !vc.is_tagged() {
                    vm.stack[base + a] = TValue::from_float(
                        unsafe { vb.as_float_unchecked() * vc.as_float_unchecked() });
                    pc += 1;
                } else if let (Some(ib), Some(ic)) = (vb.try_as_i64(&vm.gc), vc.try_as_i64(&vm.gc)) {
                    let result = ib.wrapping_mul(ic);
                    vm.stack[base + a] = TValue::from_full_integer(result, &mut vm.gc);
                    pc += 1;
                } else {
                    match arith::arith_op(ArithOp::Mul, vb, vc, &mut vm.gc, &vm.strings) {
                        arith::ArithResult::Ok(result) => {
                            vm.stack[base + a] = result;
                            pc += 1;
                        }
                        arith::ArithResult::NeedMetamethod => {}
                        arith::ArithResult::Error(e) => { vm.call_stack[ci_idx].pc = pc; return Err(add_error_prefix(vm, e)); }
                    }
                }
            }
            OpCode::Mod => {
                let b = inst.b() as usize;
                let c = inst.c() as usize;
                let vb = vm.stack[base + b];
                let vc = vm.stack[base + c];
                if vb.is_integer() && vc.is_integer() {
                    let ib = unsafe { vb.as_integer_unchecked() };
                    let ic = unsafe { vc.as_integer_unchecked() };
                    if ic == 0 {
                        vm.call_stack[ci_idx].pc = pc;
                        return Err(add_error_prefix(vm, LuaError::Runtime("attempt to perform 'n%0'".to_string())));
                    }
                    let r = ib.wrapping_rem(ic);
                    let result = if r != 0 && (r ^ ic) < 0 { r.wrapping_add(ic) } else { r };
                    // Result magnitude ≤ max(|ib|,|ic|), always fits in 47-bit
                    vm.stack[base + a] = unsafe { TValue::from_integer_unchecked(result) };
                    pc += 1;
                } else if !vb.is_tagged() && !vc.is_tagged() {
                    let fa = unsafe { vb.as_float_unchecked() };
                    let fb = unsafe { vc.as_float_unchecked() };
                    let r = fa % fb;
                    let result = if r != 0.0 && ((r > 0.0) != (fb > 0.0)) { r + fb } else { r };
                    vm.stack[base + a] = TValue::from_float(result);
                    pc += 1;
                } else if let (Some(ib), Some(ic)) = (vb.try_as_i64(&vm.gc), vc.try_as_i64(&vm.gc)) {
                    if ic == 0 {
                        vm.call_stack[ci_idx].pc = pc;
                        return Err(add_error_prefix(vm, LuaError::Runtime("attempt to perform 'n%0'".to_string())));
                    }
                    let r = ib.wrapping_rem(ic);
                    let result = if r != 0 && (r ^ ic) < 0 { r.wrapping_add(ic) } else { r };
                    vm.stack[base + a] = TValue::from_full_integer(result, &mut vm.gc);
                    pc += 1;
                } else {
                    match arith::arith_op(ArithOp::Mod, vb, vc, &mut vm.gc, &vm.strings) {
                        arith::ArithResult::Ok(result) => {
                            vm.stack[base + a] = result;
                            pc += 1;
                        }
                        arith::ArithResult::NeedMetamethod => {}
                        arith::ArithResult::Error(e) => { vm.call_stack[ci_idx].pc = pc; return Err(add_error_prefix(vm, e)); }
                    }
                }
            }
            OpCode::IDiv => {
                let b = inst.b() as usize;
                let c = inst.c() as usize;
                let vb = vm.stack[base + b];
                let vc = vm.stack[base + c];
                if vb.is_integer() && vc.is_integer() {
                    let ib = unsafe { vb.as_integer_unchecked() };
                    let ic = unsafe { vc.as_integer_unchecked() };
                    if ic == 0 {
                        vm.call_stack[ci_idx].pc = pc;
                        return Err(add_error_prefix(vm, LuaError::Runtime("attempt to divide by zero".to_string())));
                    }
                    let d = ib.wrapping_div(ic);
                    let r = ib.wrapping_rem(ic);
                    let result = if r != 0 && (r ^ ic) < 0 { d - 1 } else { d };
                    // Result magnitude ≤ |ib|, always fits in 47-bit
                    vm.stack[base + a] = unsafe { TValue::from_integer_unchecked(result) };
                    pc += 1;
                } else if !vb.is_tagged() && !vc.is_tagged() {
                    let fa = unsafe { vb.as_float_unchecked() };
                    let fb = unsafe { vc.as_float_unchecked() };
                    vm.stack[base + a] = TValue::from_float((fa / fb).floor());
                    pc += 1;
                } else if let (Some(ib), Some(ic)) = (vb.try_as_i64(&vm.gc), vc.try_as_i64(&vm.gc)) {
                    if ic == 0 {
                        vm.call_stack[ci_idx].pc = pc;
                        return Err(add_error_prefix(vm, LuaError::Runtime("attempt to divide by zero".to_string())));
                    }
                    let d = ib.wrapping_div(ic);
                    let r = ib.wrapping_rem(ic);
                    let result = if r != 0 && (r ^ ic) < 0 { d - 1 } else { d };
                    vm.stack[base + a] = TValue::from_full_integer(result, &mut vm.gc);
                    pc += 1;
                } else {
                    match arith::arith_op(ArithOp::IDiv, vb, vc, &mut vm.gc, &vm.strings) {
                        arith::ArithResult::Ok(result) => {
                            vm.stack[base + a] = result;
                            pc += 1;
                        }
                        arith::ArithResult::NeedMetamethod => {}
                        arith::ArithResult::Error(e) => { vm.call_stack[ci_idx].pc = pc; return Err(add_error_prefix(vm, e)); }
                    }
                }
            }
            // Div and Pow always produce float — no integer fast path
            OpCode::Div => {
                let b = inst.b() as usize;
                let c = inst.c() as usize;
                let vb = vm.stack[base + b];
                let vc = vm.stack[base + c];
                if !vb.is_tagged() && !vc.is_tagged() {
                    vm.stack[base + a] = TValue::from_float(
                        unsafe { vb.as_float_unchecked() / vc.as_float_unchecked() });
                    pc += 1;
                } else if let (Some(ib), Some(ic)) = (vb.try_as_i64(&vm.gc), vc.try_as_i64(&vm.gc)) {
                    vm.stack[base + a] = TValue::from_float(ib as f64 / ic as f64);
                    pc += 1;
                } else {
                    match arith::arith_op(ArithOp::Div, vb, vc, &mut vm.gc, &vm.strings) {
                        arith::ArithResult::Ok(result) => {
                            vm.stack[base + a] = result;
                            pc += 1;
                        }
                        arith::ArithResult::NeedMetamethod => {}
                        arith::ArithResult::Error(e) => { vm.call_stack[ci_idx].pc = pc; return Err(add_error_prefix(vm, e)); }
                    }
                }
            }
            OpCode::Pow => {
                let b = inst.b() as usize;
                let c = inst.c() as usize;
                let vb = vm.stack[base + b];
                let vc = vm.stack[base + c];
                match arith::arith_op(ArithOp::Pow, vb, vc, &mut vm.gc, &vm.strings) {
                    arith::ArithResult::Ok(result) => {
                        vm.stack[base + a] = result;
                        pc += 1;
                    }
                    arith::ArithResult::NeedMetamethod => {}
                    arith::ArithResult::Error(e) => { vm.call_stack[ci_idx].pc = pc; return Err(add_error_prefix(vm, e)); }
                }
            }
            OpCode::BAnd | OpCode::BOr | OpCode::BXor | OpCode::Shl | OpCode::Shr => {
                let b = inst.b() as usize;
                let c = inst.c() as usize;
                let vb = vm.stack[base + b];
                let vc = vm.stack[base + c];
                let aop = match op {
                    OpCode::BAnd => ArithOp::BAnd,
                    OpCode::BOr => ArithOp::BOr,
                    OpCode::BXor => ArithOp::BXor,
                    OpCode::Shl => ArithOp::Shl,
                    _ => ArithOp::Shr,
                };
                match arith::bitwise_op(aop, vb, vc, &mut vm.gc, &vm.strings) {
                    arith::ArithResult::Ok(result) => {
                        vm.stack[base + a] = result;
                        pc += 1; // skip MMBin
                    }
                    arith::ArithResult::NeedMetamethod => {} // fall through to MMBin
                    arith::ArithResult::Error(e) => {
                        vm.call_stack[ci_idx].pc = pc;
                        return Err(enhance_bitwise_error(vm, ci_idx, e, b, Some(c), vb, vc));
                    }
                }
            }

            // ---- Arithmetic (register + constant) ----
            OpCode::AddK
            | OpCode::SubK
            | OpCode::MulK
            | OpCode::ModK
            | OpCode::PowK
            | OpCode::DivK
            | OpCode::IDivK => {
                let b = inst.b() as usize;
                let c = inst.c() as usize;
                let vb = vm.stack[base + b];
                let proto = &vm.protos[proto_idx];
                let vc = constant_to_tvalue(&proto.constants[c], &mut vm.gc);
                let aop = match op {
                    OpCode::AddK => ArithOp::Add,
                    OpCode::SubK => ArithOp::Sub,
                    OpCode::MulK => ArithOp::Mul,
                    OpCode::ModK => ArithOp::Mod,
                    OpCode::PowK => ArithOp::Pow,
                    OpCode::DivK => ArithOp::Div,
                    _ => ArithOp::IDiv,
                };
                match arith::arith_op(aop, vb, vc, &mut vm.gc, &vm.strings) {
                    arith::ArithResult::Ok(result) => {
                        vm.stack[base + a] = result;
                        pc += 1; // skip MMBinK
                    }
                    arith::ArithResult::NeedMetamethod => {} // fall through to MMBinK
                    arith::ArithResult::Error(e) => { vm.call_stack[ci_idx].pc = pc; return Err(add_error_prefix(vm, e)); }
                }
            }
            OpCode::BAndK | OpCode::BOrK | OpCode::BXorK => {
                let b = inst.b() as usize;
                let c = inst.c() as usize;
                let vb = vm.stack[base + b];
                let proto = &vm.protos[proto_idx];
                let vc = constant_to_tvalue(&proto.constants[c], &mut vm.gc);
                let aop = match op {
                    OpCode::BAndK => ArithOp::BAnd,
                    OpCode::BOrK => ArithOp::BOr,
                    _ => ArithOp::BXor,
                };
                match arith::bitwise_op(aop, vb, vc, &mut vm.gc, &vm.strings) {
                    arith::ArithResult::Ok(result) => {
                        vm.stack[base + a] = result;
                        pc += 1; // skip MMBinK
                    }
                    arith::ArithResult::NeedMetamethod => {} // fall through to MMBinK
                    arith::ArithResult::Error(e) => {
                        vm.call_stack[ci_idx].pc = pc;
                        return Err(enhance_bitwise_error(vm, ci_idx, e, b, None, vb, vc));
                    }
                }
            }

            // ---- Arithmetic (register + immediate) ----
            OpCode::AddI => {
                let b = inst.b() as usize;
                let sc = inst.c() as i8 as i64;
                let vb = vm.stack[base + b];
                // Fast path 1: inline integer + immediate
                if vb.is_integer() {
                    let result = unsafe { vb.as_integer_unchecked() }.wrapping_add(sc);
                    vm.stack[base + a] =
                        if result >= selune_core::value::SMALL_INT_MIN
                            && result <= selune_core::value::SMALL_INT_MAX
                        {
                            unsafe { TValue::from_integer_unchecked(result) }
                        } else {
                            TValue::from_full_integer(result, &mut vm.gc)
                        };
                    pc += 1;
                }
                // Fast path 2: float + immediate
                else if !vb.is_tagged() {
                    vm.stack[base + a] = TValue::from_float(
                        unsafe { vb.as_float_unchecked() } + sc as f64);
                    pc += 1;
                }
                // Fast path 3: boxed integer + immediate
                else if let Some(ib) = vb.try_as_i64(&vm.gc) {
                    let result = ib.wrapping_add(sc);
                    vm.stack[base + a] = TValue::from_full_integer(result, &mut vm.gc);
                    pc += 1;
                }
                // Slow path
                else {
                    let imm = TValue::from_full_integer(sc, &mut vm.gc);
                    match arith::arith_op(ArithOp::Add, vb, imm, &mut vm.gc, &vm.strings) {
                        arith::ArithResult::Ok(result) => {
                            vm.stack[base + a] = result;
                            pc += 1;
                        }
                        arith::ArithResult::NeedMetamethod => {}
                        arith::ArithResult::Error(e) => { vm.call_stack[ci_idx].pc = pc; return Err(add_error_prefix(vm, e)); }
                    }
                }
            }
            OpCode::ShrI => {
                // ShrI has no following MMBinI (compiler doesn't emit one)
                let b = inst.b() as usize;
                let sc = inst.c() as i8 as i64;
                let vb = vm.stack[base + b];
                let imm = TValue::from_full_integer(sc, &mut vm.gc);
                match arith::bitwise_op(ArithOp::Shr, vb, imm, &mut vm.gc, &vm.strings) {
                    arith::ArithResult::Ok(result) => {
                        vm.stack[base + a] = result;
                    }
                    arith::ArithResult::NeedMetamethod => {
                        let mm_name = vm.mm_names.as_ref().unwrap().shr;
                        let mm = metamethod::get_metamethod(vb, mm_name, &vm.gc);
                        if let Some(mm_func) = mm {
                            vm.call_stack[ci_idx].pc = pc;
                            let result = call_function(vm, mm_func, &[vb, imm])?;
                            vm.stack[base + a] = result.first().copied().unwrap_or(TValue::nil());
                        } else {
                            vm.call_stack[ci_idx].pc = pc;
                            return Err(runtime_error(
                                vm,
                                &format!(
                                    "attempt to perform bitwise operation on a {} value",
                                    obj_type_name(vb, vm)
                                ),
                            ));
                        }
                    }
                    arith::ArithResult::Error(e) => {
                        vm.call_stack[ci_idx].pc = pc;
                        return Err(enhance_bitwise_error(vm, ci_idx, e, b, None, vb, imm));
                    }
                }
            }
            OpCode::ShlI => {
                // ShlI has no following MMBinI (compiler doesn't emit one)
                let b = inst.b() as usize;
                let sc = inst.c() as i8 as i64;
                let vb = vm.stack[base + b];
                let imm = TValue::from_full_integer(sc, &mut vm.gc);
                match arith::bitwise_op(ArithOp::Shl, vb, imm, &mut vm.gc, &vm.strings) {
                    arith::ArithResult::Ok(result) => {
                        vm.stack[base + a] = result;
                    }
                    arith::ArithResult::NeedMetamethod => {
                        let mm_name = vm.mm_names.as_ref().unwrap().shl;
                        let mm = metamethod::get_metamethod(vb, mm_name, &vm.gc);
                        if let Some(mm_func) = mm {
                            vm.call_stack[ci_idx].pc = pc;
                            let result = call_function(vm, mm_func, &[vb, imm])?;
                            vm.stack[base + a] = result.first().copied().unwrap_or(TValue::nil());
                        } else {
                            vm.call_stack[ci_idx].pc = pc;
                            return Err(runtime_error(
                                vm,
                                &format!(
                                    "attempt to perform bitwise operation on a {} value",
                                    obj_type_name(vb, vm)
                                ),
                            ));
                        }
                    }
                    arith::ArithResult::Error(e) => {
                        vm.call_stack[ci_idx].pc = pc;
                        return Err(enhance_bitwise_error(vm, ci_idx, e, b, None, vb, imm));
                    }
                }
            }

            // ---- Unary ----
            OpCode::Unm => {
                let b = inst.b() as usize;
                let vb = vm.stack[base + b];
                match arith::arith_unm(vb, &mut vm.gc, &vm.strings) {
                    arith::ArithResult::Ok(result) => {
                        vm.stack[base + a] = result;
                    }
                    arith::ArithResult::NeedMetamethod => {
                        let mm_name = vm.mm_names.as_ref().unwrap().unm;
                        if let Some(mm) = metamethod::get_metamethod(vb, mm_name, &vm.gc) {
                            vm.call_stack[ci_idx].pc = pc;
                            let result = call_function(vm, mm, &[vb, vb])?;
                            vm.stack[base + a] = result.first().copied().unwrap_or(TValue::nil());
                        } else {
                            vm.call_stack[ci_idx].pc = pc;
                            let obj_name = get_obj_name(vm, ci_idx, b);
                            return Err(runtime_error(
                                vm,
                                &format!(
                                    "attempt to perform arithmetic on a {} value{}",
                                    obj_type_name(vb, vm),
                                    obj_name
                                ),
                            ));
                        }
                    }
                    arith::ArithResult::Error(e) => { vm.call_stack[ci_idx].pc = pc; return Err(add_error_prefix(vm, e)); }
                }
            }
            OpCode::BNot => {
                let b = inst.b() as usize;
                let vb = vm.stack[base + b];
                match arith::arith_bnot(vb, &mut vm.gc, &vm.strings) {
                    arith::ArithResult::Ok(result) => {
                        vm.stack[base + a] = result;
                    }
                    arith::ArithResult::NeedMetamethod => {
                        let mm_name = vm.mm_names.as_ref().unwrap().bnot;
                        if let Some(mm) = metamethod::get_metamethod(vb, mm_name, &vm.gc) {
                            vm.call_stack[ci_idx].pc = pc;
                            let result = call_function(vm, mm, &[vb, vb])?;
                            vm.stack[base + a] = result.first().copied().unwrap_or(TValue::nil());
                        } else {
                            vm.call_stack[ci_idx].pc = pc;
                            let obj_name = get_obj_name(vm, ci_idx, b);
                            return Err(runtime_error(
                                vm,
                                &format!(
                                    "attempt to perform bitwise operation on a {} value{}",
                                    obj_type_name(vb, vm),
                                    obj_name
                                ),
                            ));
                        }
                    }
                    arith::ArithResult::Error(e) => {
                        vm.call_stack[ci_idx].pc = pc;
                        let obj_name = get_obj_name(vm, ci_idx, b);
                        return Err(match e {
                            LuaError::Runtime(msg) => {
                                let prefix = get_error_prefix(vm, 0);
                                LuaError::Runtime(format!("{}{}{}", prefix, msg, obj_name))
                            }
                            other => other,
                        });
                    }
                }
            }
            OpCode::Not => {
                let b = inst.b() as usize;
                let vb = vm.stack[base + b];
                vm.stack[base + a] = TValue::from_bool(vb.is_falsy());
            }
            OpCode::Len => {
                let b = inst.b() as usize;
                let vb = vm.stack[base + b];
                if let Some(len) = arith::str_len(vb, &vm.strings) {
                    vm.stack[base + a] = TValue::from_full_integer(len, &mut vm.gc);
                } else if vb.as_table_idx().is_some() {
                    // Check for __len metamethod first
                    let mm_name = vm.mm_names.as_ref().unwrap().len;
                    if let Some(mm) = metamethod::get_metamethod(vb, mm_name, &vm.gc) {
                        vm.call_stack[ci_idx].pc = pc;
                        let result = call_function(vm, mm, &[vb, vb])?;
                        vm.stack[base + a] = result.first().copied().unwrap_or(TValue::nil());
                    } else {
                        let table_idx = vb.as_table_idx().unwrap();
                        let len = vm.gc.get_table(table_idx).length();
                        vm.stack[base + a] = TValue::from_full_integer(len, &mut vm.gc);
                    }
                } else {
                    // Check for __len metamethod on non-table/non-string values
                    let mm_name = vm.mm_names.as_ref().unwrap().len;
                    if let Some(mm) = metamethod::get_metamethod(vb, mm_name, &vm.gc) {
                        vm.call_stack[ci_idx].pc = pc;
                        let result = call_function(vm, mm, &[vb, vb])?;
                        vm.stack[base + a] = result.first().copied().unwrap_or(TValue::nil());
                    } else {
                        vm.call_stack[ci_idx].pc = pc;
                        let obj_name = get_obj_name(vm, ci_idx, b);
                        return Err(runtime_error(
                            vm,
                            &format!(
                                "attempt to get length of a {} value{}",
                                obj_type_name(vb, vm),
                                obj_name
                            ),
                        ));
                    }
                }
            }
            OpCode::Concat => {
                let b = inst.b() as usize;
                let count = b;
                let mut values = Vec::with_capacity(count);
                for i in 0..count {
                    values.push(vm.stack[base + a + i]);
                }
                match arith::lua_concat(&values, &vm.gc, &mut vm.strings) {
                    arith::ArithResult::Ok(result) => {
                        vm.stack[base + a] = result;
                    }
                    arith::ArithResult::NeedMetamethod => {
                        // PUC Lua concat semantics: process pairwise from end.
                        // At each step, try to coalesce consecutive string/number
                        // values at the end, then apply metamethod for the boundary.
                        let mm_name = vm.mm_names.as_ref().unwrap().concat;
                        let mut top = values.len(); // exclusive upper bound
                        while top > 1 {
                            // Try to concat values[top-2] and values[top-1] as raw
                            let left = values[top - 2];
                            let right = values[top - 1];
                            match arith::lua_concat(&[left, right], &vm.gc, &mut vm.strings) {
                                arith::ArithResult::Ok(result) => {
                                    // Coalesce: replace values[top-2] with result, shrink
                                    values[top - 2] = result;
                                    top -= 1;
                                }
                                _ => {
                                    // Need metamethod
                                    let mm = metamethod::get_metamethod(left, mm_name, &vm.gc)
                                        .or_else(|| {
                                            metamethod::get_metamethod(right, mm_name, &vm.gc)
                                        });
                                    if let Some(mm_func) = mm {
                                        vm.call_stack[ci_idx].pc = pc;
                                        let result = call_function(vm, mm_func, &[left, right])?;
                                        values[top - 2] =
                                            result.first().copied().unwrap_or(TValue::nil());
                                        top -= 1;
                                    } else {
                                        // Error: find the non-concatenable value
                                        let (bad, bad_reg) = if coerce::to_string_for_concat(
                                            left,
                                            &vm.gc,
                                            &mut vm.strings,
                                        )
                                        .is_none()
                                        {
                                            (left, a + top - 2)
                                        } else {
                                            (right, a + top - 1)
                                        };
                                        vm.call_stack[ci_idx].pc = pc;
                                        let obj_name = get_obj_name(vm, ci_idx, bad_reg);
                                        return Err(runtime_error(
                                            vm,
                                            &format!(
                                                "attempt to concatenate a {} value{}",
                                                obj_type_name(bad, vm),
                                                obj_name
                                            ),
                                        ));
                                    }
                                }
                            }
                        }
                        vm.stack[base + a] = values[0];
                    }
                    arith::ArithResult::Error(e) => { vm.call_stack[ci_idx].pc = pc; return Err(add_error_prefix(vm, e)); }
                }
            }

            // ---- Metamethod dispatch (MMBin/MMBinI/MMBinK) ----
            OpCode::MMBin => {
                // A = left operand reg, B = right operand reg, C = metamethod index
                let b_reg = inst.b() as usize;
                let mm_idx = inst.c();
                let va = vm.stack[base + a];
                let vb = vm.stack[base + b_reg];
                let mm_name = vm.mm_names.as_ref().unwrap().from_mm_index(mm_idx);
                // Try left operand's metamethod, then right
                let mm = metamethod::get_metamethod(va, mm_name, &vm.gc)
                    .or_else(|| metamethod::get_metamethod(vb, mm_name, &vm.gc));
                if let Some(mm_func) = mm {
                    vm.call_stack[ci_idx].pc = pc;
                    let result = call_function(vm, mm_func, &[va, vb])
                        .map_err(|e| augment_mm_error(e, mm_idx))?;
                    // Destination = previous instruction's A field
                    let prev_inst = &vm.protos[proto_idx].code[pc - 2];
                    let dest = prev_inst.a() as usize;
                    vm.stack[base + dest] = result.first().copied().unwrap_or(TValue::nil());
                } else {
                    vm.call_stack[ci_idx].pc = pc;
                    // Determine which operand is the offending one
                    let (bad_type, obj_name) = if !va.is_number() && !va.is_integer() {
                        (obj_type_name(va, vm), get_obj_name(vm, ci_idx, a))
                    } else {
                        (obj_type_name(vb, vm), get_obj_name(vm, ci_idx, b_reg))
                    };
                    return Err(runtime_error(
                        vm,
                        &format!(
                            "attempt to perform {} on a {} value{}",
                            mm_op_description(mm_idx),
                            bad_type,
                            obj_name
                        ),
                    ));
                }
            }
            OpCode::MMBinI => {
                // A = left operand reg, sB = immediate, C = metamethod index, k = flip
                let sb = inst.b() as i8 as i64;
                let mm_idx = inst.c();
                let k_flip = inst.k();
                let va = vm.stack[base + a];
                let vb = TValue::from_full_integer(sb, &mut vm.gc);
                let mm_name = vm.mm_names.as_ref().unwrap().from_mm_index(mm_idx);
                // If k_flip, the original operation was `imm op reg` so swap
                let (left, right) = if k_flip { (vb, va) } else { (va, vb) };
                let mm = metamethod::get_metamethod(left, mm_name, &vm.gc)
                    .or_else(|| metamethod::get_metamethod(right, mm_name, &vm.gc));
                if let Some(mm_func) = mm {
                    vm.call_stack[ci_idx].pc = pc;
                    let result = call_function(vm, mm_func, &[left, right])
                        .map_err(|e| augment_mm_error(e, mm_idx))?;
                    let prev_inst = &vm.protos[proto_idx].code[pc - 2];
                    let dest = prev_inst.a() as usize;
                    vm.stack[base + dest] = result.first().copied().unwrap_or(TValue::nil());
                } else {
                    vm.call_stack[ci_idx].pc = pc;
                    let obj_name = get_obj_name(vm, ci_idx, a);
                    return Err(runtime_error(
                        vm,
                        &format!(
                            "attempt to perform {} on a {} value{}",
                            mm_op_description(mm_idx),
                            obj_type_name(va, vm),
                            obj_name
                        ),
                    ));
                }
            }
            OpCode::MMBinK => {
                // A = left operand reg, B = constant index, C = metamethod index, k = flip
                let b_k = inst.b() as usize;
                let mm_idx = inst.c();
                let k_flip = inst.k();
                let va = vm.stack[base + a];
                let proto = &vm.protos[proto_idx];
                let vb = constant_to_tvalue(&proto.constants[b_k], &mut vm.gc);
                let mm_name = vm.mm_names.as_ref().unwrap().from_mm_index(mm_idx);
                let (left, right) = if k_flip { (vb, va) } else { (va, vb) };
                let mm = metamethod::get_metamethod(left, mm_name, &vm.gc)
                    .or_else(|| metamethod::get_metamethod(right, mm_name, &vm.gc));
                if let Some(mm_func) = mm {
                    vm.call_stack[ci_idx].pc = pc;
                    let result = call_function(vm, mm_func, &[left, right])
                        .map_err(|e| augment_mm_error(e, mm_idx))?;
                    let prev_inst = &vm.protos[proto_idx].code[pc - 2];
                    let dest = prev_inst.a() as usize;
                    vm.stack[base + dest] = result.first().copied().unwrap_or(TValue::nil());
                } else {
                    vm.call_stack[ci_idx].pc = pc;
                    let obj_name = get_obj_name(vm, ci_idx, a);
                    return Err(runtime_error(
                        vm,
                        &format!(
                            "attempt to perform {} on a {} value{}",
                            mm_op_description(mm_idx),
                            obj_type_name(va, vm),
                            obj_name
                        ),
                    ));
                }
            }

            // ---- Comparisons ----
            OpCode::Eq => {
                let b = inst.b() as usize;
                let k = inst.k();
                let va = vm.stack[base + a];
                let vb = vm.stack[base + b];
                let (eq, needs_mm) = compare::lua_eq(va, vb, &vm.gc, &vm.strings);
                let result = if needs_mm && !eq {
                    // Try __eq metamethod
                    let mm_name = vm.mm_names.as_ref().unwrap().eq;
                    if let Some(mm) = metamethod::get_metamethod(va, mm_name, &vm.gc)
                        .or_else(|| metamethod::get_metamethod(vb, mm_name, &vm.gc))
                    {
                        vm.call_stack[ci_idx].pc = pc;
                        let res = call_function(vm, mm, &[va, vb])?;
                        !res.first().copied().unwrap_or(TValue::nil()).is_falsy()
                    } else {
                        eq
                    }
                } else {
                    eq
                };
                if result != k {
                    pc += 1;
                }
            }
            OpCode::Lt => {
                let b = inst.b() as usize;
                let k = inst.k();
                let va = vm.stack[base + a];
                let vb = vm.stack[base + b];
                // Fast path: both inline integers
                if va.is_integer() && vb.is_integer() {
                    let result = unsafe { va.as_integer_unchecked() < vb.as_integer_unchecked() };
                    if result != k { pc += 1; }
                } else if !va.is_tagged() && !vb.is_tagged() {
                    let result = unsafe { va.as_float_unchecked() < vb.as_float_unchecked() };
                    if result != k { pc += 1; }
                } else {
                    let result = match compare::lua_lt(va, vb, &vm.gc, &vm.strings) {
                        compare::CompareResult::Ok(v) => v,
                        compare::CompareResult::NeedMetamethod => {
                            let mm_name = vm.mm_names.as_ref().unwrap().lt;
                            if let Some(mm) = metamethod::get_metamethod(va, mm_name, &vm.gc)
                                .or_else(|| metamethod::get_metamethod(vb, mm_name, &vm.gc))
                            {
                                vm.call_stack[ci_idx].pc = pc;
                                let res = call_function(vm, mm, &[va, vb]).map_err(|e| {
                                    augment_mm_error(e, 13)
                                })?;
                                !res.first().copied().unwrap_or(TValue::nil()).is_falsy()
                            } else {
                                vm.call_stack[ci_idx].pc = pc;
                                return Err(order_error(vm, va, vb));
                            }
                        }
                    };
                    if result != k { pc += 1; }
                }
            }
            OpCode::Le => {
                let b = inst.b() as usize;
                let k = inst.k();
                let va = vm.stack[base + a];
                let vb = vm.stack[base + b];
                if va.is_integer() && vb.is_integer() {
                    let result = unsafe { va.as_integer_unchecked() <= vb.as_integer_unchecked() };
                    if result != k { pc += 1; }
                } else if !va.is_tagged() && !vb.is_tagged() {
                    let result = unsafe { va.as_float_unchecked() <= vb.as_float_unchecked() };
                    if result != k { pc += 1; }
                } else {
                    let result = match compare::lua_le(va, vb, &vm.gc, &vm.strings) {
                        compare::CompareResult::Ok(v) => v,
                        compare::CompareResult::NeedMetamethod => {
                            let mm_name = vm.mm_names.as_ref().unwrap().le;
                            if let Some(mm) = metamethod::get_metamethod(va, mm_name, &vm.gc)
                                .or_else(|| metamethod::get_metamethod(vb, mm_name, &vm.gc))
                            {
                                vm.call_stack[ci_idx].pc = pc;
                                let res = call_function(vm, mm, &[va, vb]).map_err(|e| {
                                    augment_mm_error(e, 14)
                                })?;
                                !res.first().copied().unwrap_or(TValue::nil()).is_falsy()
                            } else {
                                vm.call_stack[ci_idx].pc = pc;
                                return Err(order_error(vm, va, vb));
                            }
                        }
                    };
                    if result != k { pc += 1; }
                }
            }
            OpCode::EqK => {
                let b = inst.b() as usize;
                let k = inst.k();
                let va = vm.stack[base + a];
                let proto = &vm.protos[proto_idx];
                let vb = constant_to_tvalue(&proto.constants[b], &mut vm.gc);
                let (eq, _) = compare::lua_eq(va, vb, &vm.gc, &vm.strings);
                if eq != k {
                    pc += 1;
                }
            }
            OpCode::EqI => {
                let sb = inst.b() as i8 as i64;
                let k = inst.k();
                let va = vm.stack[base + a];
                // Fast path: inline integer comparison
                if va.is_integer() {
                    let eq = unsafe { va.as_integer_unchecked() } == sb;
                    if eq != k {
                        pc += 1;
                    }
                } else if !va.is_tagged() {
                    // Float == int comparison
                    let eq = unsafe { va.as_float_unchecked() } == sb as f64;
                    if eq != k {
                        pc += 1;
                    }
                } else {
                    let imm = TValue::from_full_integer(sb, &mut vm.gc);
                    let (eq, _) = compare::lua_eq(va, imm, &vm.gc, &vm.strings);
                    if eq != k {
                        pc += 1;
                    }
                }
            }
            OpCode::LtI => {
                let sb = inst.b() as i8 as i64;
                let k = inst.k();
                let va = vm.stack[base + a];
                // Fast path: inline integer < immediate
                if va.is_integer() {
                    let result = unsafe { va.as_integer_unchecked() } < sb;
                    if result != k { pc += 1; }
                } else if !va.is_tagged() {
                    let result = unsafe { va.as_float_unchecked() } < sb as f64;
                    if result != k { pc += 1; }
                } else {
                    let imm = TValue::from_full_integer(sb, &mut vm.gc);
                    let result = match compare::lua_lt(va, imm, &vm.gc, &vm.strings) {
                        compare::CompareResult::Ok(v) => v,
                        compare::CompareResult::NeedMetamethod => {
                            let mm_name = vm.mm_names.as_ref().unwrap().lt;
                            if let Some(mm) = metamethod::get_metamethod(va, mm_name, &vm.gc) {
                                vm.call_stack[ci_idx].pc = pc;
                                let res = call_function(vm, mm, &[va, imm])?;
                                !res.first().copied().unwrap_or(TValue::nil()).is_falsy()
                            } else {
                                vm.call_stack[ci_idx].pc = pc;
                                return Err(order_error(vm, va, imm));
                            }
                        }
                    };
                    if result != k { pc += 1; }
                }
            }
            OpCode::LeI => {
                let sb = inst.b() as i8 as i64;
                let k = inst.k();
                let va = vm.stack[base + a];
                if va.is_integer() {
                    let result = unsafe { va.as_integer_unchecked() } <= sb;
                    if result != k { pc += 1; }
                } else if !va.is_tagged() {
                    let result = unsafe { va.as_float_unchecked() } <= sb as f64;
                    if result != k { pc += 1; }
                } else {
                    let imm = TValue::from_full_integer(sb, &mut vm.gc);
                    let result = match compare::lua_le(va, imm, &vm.gc, &vm.strings) {
                        compare::CompareResult::Ok(v) => v,
                        compare::CompareResult::NeedMetamethod => {
                            let mm_name = vm.mm_names.as_ref().unwrap().le;
                            if let Some(mm) = metamethod::get_metamethod(va, mm_name, &vm.gc) {
                                vm.call_stack[ci_idx].pc = pc;
                                let res = call_function(vm, mm, &[va, imm])?;
                                !res.first().copied().unwrap_or(TValue::nil()).is_falsy()
                            } else {
                                vm.call_stack[ci_idx].pc = pc;
                                return Err(order_error(vm, va, imm));
                            }
                        }
                    };
                    if result != k { pc += 1; }
                }
            }
            OpCode::GtI => {
                let sb = inst.b() as i8 as i64;
                let k = inst.k();
                let va = vm.stack[base + a];
                if va.is_integer() {
                    let result = unsafe { va.as_integer_unchecked() } > sb;
                    if result != k { pc += 1; }
                } else if !va.is_tagged() {
                    let result = unsafe { va.as_float_unchecked() } > sb as f64;
                    if result != k { pc += 1; }
                } else {
                    let imm = TValue::from_full_integer(sb, &mut vm.gc);
                    let result = match compare::lua_lt(imm, va, &vm.gc, &vm.strings) {
                        compare::CompareResult::Ok(v) => v,
                        compare::CompareResult::NeedMetamethod => {
                            let mm_name = vm.mm_names.as_ref().unwrap().lt;
                            if let Some(mm) = metamethod::get_metamethod(va, mm_name, &vm.gc) {
                                vm.call_stack[ci_idx].pc = pc;
                                let res = call_function(vm, mm, &[imm, va])?;
                                !res.first().copied().unwrap_or(TValue::nil()).is_falsy()
                            } else {
                                vm.call_stack[ci_idx].pc = pc;
                                return Err(order_error(vm, imm, va));
                            }
                        }
                    };
                    if result != k { pc += 1; }
                }
            }
            OpCode::GeI => {
                let sb = inst.b() as i8 as i64;
                let k = inst.k();
                let va = vm.stack[base + a];
                if va.is_integer() {
                    let result = unsafe { va.as_integer_unchecked() } >= sb;
                    if result != k { pc += 1; }
                } else if !va.is_tagged() {
                    let result = unsafe { va.as_float_unchecked() } >= sb as f64;
                    if result != k { pc += 1; }
                } else {
                    let imm = TValue::from_full_integer(sb, &mut vm.gc);
                    let result = match compare::lua_le(imm, va, &vm.gc, &vm.strings) {
                        compare::CompareResult::Ok(v) => v,
                        compare::CompareResult::NeedMetamethod => {
                            let mm_name = vm.mm_names.as_ref().unwrap().le;
                            if let Some(mm) = metamethod::get_metamethod(va, mm_name, &vm.gc) {
                                vm.call_stack[ci_idx].pc = pc;
                                let res = call_function(vm, mm, &[imm, va])?;
                                !res.first().copied().unwrap_or(TValue::nil()).is_falsy()
                            } else {
                                vm.call_stack[ci_idx].pc = pc;
                                return Err(order_error(vm, imm, va));
                            }
                        }
                    };
                    if result != k { pc += 1; }
                }
            }
            OpCode::Test => {
                let k = inst.k();
                let va = vm.stack[base + a];
                if va.is_truthy() == k {
                    pc += 1;
                }
            }
            OpCode::TestSet => {
                let b = inst.b() as usize;
                let k = inst.k();
                let vb = vm.stack[base + b];
                // Lua 5.4: if (l_isfalse(rb) != k) then pc++ else R[A] := R[B]
                if vb.is_truthy() == k {
                    // condition failed → skip next instruction
                    pc += 1;
                } else {
                    // condition passed → set R[A] = R[B]
                    vm.stack[base + a] = vb;
                }
            }

            // ---- Control flow ----
            OpCode::Jmp => {
                let sj = inst.get_sj();
                let new_pc = pc as i64 + sj as i64;
                pc = new_pc as usize;
            }

            // ---- Numeric for loop ----
            OpCode::ForPrep => {
                let init = vm.stack[base + a];
                let limit = vm.stack[base + a + 1];
                let step = vm.stack[base + a + 2];

                // Check if init and step are actual integers (not string coercion)
                // Per Lua 5.4: "If both the initial value and the step are integers,
                // the loop is done with integers; note that the limit does not need to be an integer."
                let maybe_i_init = init.as_full_integer(&vm.gc);
                let maybe_i_step = step.as_full_integer(&vm.gc);

                if let (Some(i_init), Some(i_step)) = (maybe_i_init, maybe_i_step) {
                    // Init and step are integers. Limit may be float/string.
                    if i_step == 0 {
                        vm.call_stack[ci_idx].pc = pc;
                        return Err(runtime_error(vm, "'for' step is zero"));
                    }
                    // Try to convert limit to integer (check actual type first)
                    let limit_result = if let Some(il) = limit.as_full_integer(&vm.gc) {
                        Ok(il)
                    } else {
                        // Limit is a float or string. Convert to number, then floor/ceil.
                        let f_limit =
                            coerce::to_number(limit, &vm.gc, &vm.strings).ok_or_else(|| {
                                let tname = obj_type_name(limit, vm);
                                runtime_error(
                                    vm,
                                    &format!("bad 'for' limit (number expected, got {})", tname),
                                )
                            })?;
                        if f_limit.is_nan() {
                            Err(false) // NaN: loop never runs
                        } else if i_step > 0 {
                            // floor: largest integer <= f_limit
                            if f_limit > i64::MAX as f64 {
                                // Positive limit beyond i64::MAX: loop may run "forever"
                                Ok(i64::MAX)
                            } else if f_limit < i64::MIN as f64 {
                                // Negative limit below i64::MIN: step>0 can never reach it
                                Err(false) // skip loop
                            } else {
                                Ok(f_limit.floor() as i64)
                            }
                        } else {
                            // ceil: smallest integer >= f_limit
                            if f_limit < i64::MIN as f64 {
                                // Negative limit beyond i64::MIN: loop may run "forever"
                                Ok(i64::MIN)
                            } else if f_limit > i64::MAX as f64 {
                                // Positive limit above i64::MAX: step<0 can never reach it
                                Err(false) // skip loop
                            } else {
                                Ok(f_limit.ceil() as i64)
                            }
                        }
                    };
                    match limit_result {
                        Ok(i_limit) => {
                            // Check if loop should execute at all
                            let should_enter = if i_step > 0 {
                                i_init <= i_limit
                            } else {
                                i_init >= i_limit
                            };
                            if !should_enter {
                                // Store 0 count in limit slot, skip loop
                                vm.stack[base + a] = TValue::from_full_integer(i_init, &mut vm.gc);
                                vm.stack[base + a + 1] = TValue::from_full_integer(0, &mut vm.gc);
                                vm.stack[base + a + 2] =
                                    TValue::from_full_integer(i_step, &mut vm.gc);
                                vm.stack[base + a + 3] =
                                    TValue::from_full_integer(i_init, &mut vm.gc);
                                let sbx = inst.sbx();
                                pc =
                                    (pc as i64 + sbx as i64) as usize;
                                pc += 1;
                            } else {
                                // Pre-compute iteration count as unsigned
                                // PUC Lua: count = (limit_u - init_u) / step_u
                                let count = if i_step > 0 {
                                    let range = (i_limit as u64).wrapping_sub(i_init as u64);
                                    range / (i_step as u64)
                                } else {
                                    // step < 0
                                    let range = (i_init as u64).wrapping_sub(i_limit as u64);
                                    // For negative step: -(step + 1) + 1 = -step as unsigned
                                    let abs_step = (-(i_step as i128)) as u64;
                                    range / abs_step
                                };
                                // Store counter in R(A), iteration count in R(A+1), step in R(A+2)
                                vm.stack[base + a] = TValue::from_full_integer(i_init, &mut vm.gc);
                                vm.stack[base + a + 1] =
                                    TValue::from_full_integer(count as i64, &mut vm.gc);
                                vm.stack[base + a + 2] =
                                    TValue::from_full_integer(i_step, &mut vm.gc);
                                vm.stack[base + a + 3] =
                                    TValue::from_full_integer(i_init, &mut vm.gc);
                            }
                        }
                        Err(_) => {
                            // Skip loop entirely: limit is out of range for step direction
                            vm.stack[base + a] = TValue::from_full_integer(i_init, &mut vm.gc);
                            vm.stack[base + a + 1] = TValue::from_full_integer(0, &mut vm.gc);
                            vm.stack[base + a + 2] = TValue::from_full_integer(i_step, &mut vm.gc);
                            vm.stack[base + a + 3] = TValue::from_full_integer(i_init, &mut vm.gc);
                            let sbx = inst.sbx();
                            pc =
                                (pc as i64 + sbx as i64) as usize;
                            pc += 1;
                        }
                    }
                } else {
                    // Float loop: at least one of init/step is not an integer
                    let f_init = coerce::to_number(init, &vm.gc, &vm.strings).ok_or_else(|| {
                        let tname = obj_type_name(init, vm);
                        runtime_error(
                            vm,
                            &format!("bad 'for' initial value (number expected, got {})", tname),
                        )
                    })?;
                    let f_limit =
                        coerce::to_number(limit, &vm.gc, &vm.strings).ok_or_else(|| {
                            let tname = obj_type_name(limit, vm);
                            runtime_error(
                                vm,
                                &format!("bad 'for' limit (number expected, got {})", tname),
                            )
                        })?;
                    let f_step = coerce::to_number(step, &vm.gc, &vm.strings).ok_or_else(|| {
                        let tname = obj_type_name(step, vm);
                        runtime_error(
                            vm,
                            &format!("bad 'for' step (number expected, got {})", tname),
                        )
                    })?;
                    if f_step == 0.0 {
                        vm.call_stack[ci_idx].pc = pc;
                        return Err(runtime_error(vm, "'for' step is zero"));
                    }
                    vm.stack[base + a] = TValue::from_float(f_init);
                    vm.stack[base + a + 1] = TValue::from_float(f_limit);
                    vm.stack[base + a + 2] = TValue::from_float(f_step);
                    vm.stack[base + a + 3] = TValue::from_float(f_init);
                    let should_enter = if f_step > 0.0 {
                        f_init <= f_limit
                    } else {
                        f_init >= f_limit
                    };
                    if !should_enter {
                        let sbx = inst.sbx();
                        pc =
                            (pc as i64 + sbx as i64) as usize;
                        pc += 1;
                    }
                }
            }

            OpCode::ForLoop => {
                let counter = vm.stack[base + a];
                let count_val = vm.stack[base + a + 1];
                let step = vm.stack[base + a + 2];
                // Fast path: ALL THREE values are inline integers
                if counter.is_integer() && count_val.is_integer() && step.is_integer() {
                    let i_counter = unsafe { counter.as_integer_unchecked() };
                    let i_count = unsafe { count_val.as_integer_unchecked() };
                    let i_step = unsafe { step.as_integer_unchecked() };
                    // Count-based integer loop: decrement count, check for underflow
                    let count_u = (i_count as u64).wrapping_sub(1);
                    if count_u != u64::MAX {
                        let next = i_counter.wrapping_add(i_step);
                        if !vm.open_upvals.is_empty() {
                            vm.close_upvalues(base + a + 3);
                        }
                        // Fast path: if next fits in 47-bit inline range (overwhelmingly common)
                        if next >= selune_core::value::SMALL_INT_MIN
                            && next <= selune_core::value::SMALL_INT_MAX
                        {
                            let next_tv = unsafe { TValue::from_integer_unchecked(next) };
                            // count_u is always decreasing from initial (which was inline), fits
                            let count_tv =
                                unsafe { TValue::from_integer_unchecked(count_u as i64) };
                            vm.stack[base + a] = next_tv;
                            vm.stack[base + a + 1] = count_tv;
                            vm.stack[base + a + 3] = next_tv;
                        } else {
                            vm.stack[base + a] = TValue::from_full_integer(next, &mut vm.gc);
                            vm.stack[base + a + 1] =
                                TValue::from_full_integer(count_u as i64, &mut vm.gc);
                            vm.stack[base + a + 3] = TValue::from_full_integer(next, &mut vm.gc);
                        }
                        let sbx = inst.sbx();
                        pc =
                            (pc as i64 + sbx as i64) as usize;
                    }
                } else if counter.is_float() {
                    // Float path (includes !is_tagged plain floats and canonical NaN)
                    if let (Some(f_counter), Some(f_limit), Some(f_step)) = (
                        counter.as_float(),
                        vm.stack[base + a + 1].as_float(),
                        vm.stack[base + a + 2].as_float(),
                    ) {
                        let next = f_counter + f_step;
                        let continue_loop = if f_step > 0.0 {
                            next <= f_limit
                        } else {
                            next >= f_limit
                        };
                        if continue_loop {
                            if !vm.open_upvals.is_empty() {
                                vm.close_upvalues(base + a + 3);
                            }
                            vm.stack[base + a] = TValue::from_float(next);
                            vm.stack[base + a + 3] = TValue::from_float(next);
                            let sbx = inst.sbx();
                            pc =
                                (pc as i64 + sbx as i64) as usize;
                        }
                    }
                } else {
                    // Boxed int fallback (rare — extreme integer ranges)
                    let count_val = vm.stack[base + a + 1];
                    let step = vm.stack[base + a + 2];
                    if let (Some(i_counter), Some(i_count), Some(i_step)) = (
                        counter.as_full_integer(&vm.gc),
                        count_val.as_full_integer(&vm.gc),
                        step.as_full_integer(&vm.gc),
                    ) {
                        let count_u = (i_count as u64).wrapping_sub(1);
                        if count_u != u64::MAX {
                            let next = i_counter.wrapping_add(i_step);
                            if !vm.open_upvals.is_empty() {
                                vm.close_upvalues(base + a + 3);
                            }
                            vm.stack[base + a] = TValue::from_full_integer(next, &mut vm.gc);
                            vm.stack[base + a + 1] =
                                TValue::from_full_integer(count_u as i64, &mut vm.gc);
                            vm.stack[base + a + 3] = TValue::from_full_integer(next, &mut vm.gc);
                            let sbx = inst.sbx();
                            pc =
                                (pc as i64 + sbx as i64) as usize;
                        }
                    }
                }
            }

            // ---- Returns ----
            OpCode::Return0 => {
                // Fast path: no TBC, no open upvalues, no hooks, not entry depth
                if vm.call_stack[ci_idx].tbc_slots_is_empty()
                    && vm.open_upvals.is_empty()
                    && !vm.hooks_active
                    && vm.call_stack.len() > entry_depth
                {
                    let func_stack_idx = vm.call_stack[ci_idx].func_stack_idx;
                    let num_results_r0 = vm.call_stack[ci_idx].num_results;
                    let call_status = &vm.call_stack[ci_idx].call_status;
                    let is_normal = matches!(call_status, CallStatus::Normal);
                    if is_normal {
                        vm.call_stack.pop();
                        if num_results_r0 < 0 {
                            vm.stack_top = func_stack_idx;
                        } else {
                            for i in 0..(num_results_r0 as usize) {
                                vm.stack[func_stack_idx + i] = TValue::nil();
                            }
                        }
                        continue;
                    }
                }

                // Slow path
                vm.call_stack[ci_idx].pc = pc;
                match close_tbc_variables(vm, ci_idx, base, None) {
                    Ok(()) => {}
                    Err(LuaError::Yield(vals)) => {
                        // Save return state for resume
                        vm.needs_close_return_resume = true;
                        vm.call_stack[ci_idx].call_status = CallStatus::CloseReturnYield(Box::new(CloseReturnYieldData {
                            saved_results: vec![],
                            remaining_tbc_slots: vec![],
                        }));
                        return Err(LuaError::Yield(vals));
                    }
                    Err(e) => return Err(e),
                }
                vm.close_upvalues(base);
                if vm.call_stack.len() <= entry_depth {
                    // Fire return hook before early return (e.g., __close called via call_function)
                    if vm.hooks_active
                        && !vm.in_hook
                        && vm.hook_mask & HOOK_RETURN != 0
                        && vm.call_stack.last().is_some_and(|ci| ci.is_lua())
                    {
                        let ci = vm.call_stack.len() - 1;
                        vm.call_stack[ci].ntransfer = 0;
                        vm.call_stack[ci_idx].pc = pc;
                        let _ = fire_hook(vm, "return", -1, entry_depth);
                    }
                    return Ok(vec![]);
                }
                vm.call_stack[ci_idx].pc = pc;
                return_from_call(vm, &[])?;
            }

            OpCode::Return1 => {
                let val = vm.stack[base + a];

                // Fast path: no TBC, no open upvalues in this frame, no hooks, not entry depth
                if vm.call_stack[ci_idx].tbc_slots_is_empty()
                    && vm.open_upvals.is_empty()
                    && !vm.hooks_active
                    && vm.call_stack.len() > entry_depth
                {
                    let func_stack_idx = vm.call_stack[ci_idx].func_stack_idx;
                    let num_results_r1 = vm.call_stack[ci_idx].num_results;
                    let call_status = &vm.call_stack[ci_idx].call_status;
                    let is_normal = matches!(call_status, CallStatus::Normal);
                    if is_normal {
                        vm.call_stack.pop();
                        if num_results_r1 < 0 {
                            vm.stack[func_stack_idx] = val;
                            vm.stack_top = func_stack_idx + 1;
                        } else {
                            vm.stack[func_stack_idx] = val;
                            for i in 1..(num_results_r1 as usize) {
                                vm.stack[func_stack_idx + i] = TValue::nil();
                            }
                        }
                        continue;
                    }
                }

                // Slow path
                vm.call_stack[ci_idx].ftransfer = (a + 1) as u16;
                vm.call_stack[ci_idx].pc = pc;
                match close_tbc_variables(vm, ci_idx, base, None) {
                    Ok(()) => {}
                    Err(LuaError::Yield(vals)) => {
                        vm.needs_close_return_resume = true;
                        vm.call_stack[ci_idx].call_status = CallStatus::CloseReturnYield(Box::new(CloseReturnYieldData {
                            saved_results: vec![val],
                            remaining_tbc_slots: vec![],
                        }));
                        return Err(LuaError::Yield(vals));
                    }
                    Err(e) => return Err(e),
                }
                vm.close_upvalues(base);
                if vm.call_stack.len() <= entry_depth {
                    // Fire return hook before early return
                    if vm.hooks_active
                        && !vm.in_hook
                        && vm.hook_mask & HOOK_RETURN != 0
                        && vm.call_stack.last().is_some_and(|ci| ci.is_lua())
                    {
                        let ci = vm.call_stack.len() - 1;
                        vm.call_stack[ci].ntransfer = 1;
                        vm.call_stack[ci_idx].pc = pc;
                        let _ = fire_hook(vm, "return", -1, entry_depth);
                    }
                    return Ok(vec![val]);
                }
                vm.call_stack[ci_idx].pc = pc;
                return_from_call(vm, &[val])?;
            }

            OpCode::Return => {
                // Set ftransfer for return hook (1-based local index)
                vm.call_stack[ci_idx].ftransfer = (a + 1) as u16;
                let b = inst.b() as usize;
                let mut results = Vec::new();
                if b == 0 {
                    let top = vm.stack_top;
                    for i in (base + a)..top {
                        results.push(vm.stack[i]);
                    }
                } else {
                    let count = b - 1;
                    for i in 0..count {
                        results.push(vm.stack[base + a + i]);
                    }
                }
                vm.call_stack[ci_idx].pc = pc;
                match close_tbc_variables(vm, ci_idx, base, None) {
                    Ok(()) => {}
                    Err(LuaError::Yield(vals)) => {
                        vm.needs_close_return_resume = true;
                        vm.call_stack[ci_idx].call_status = CallStatus::CloseReturnYield(Box::new(CloseReturnYieldData {
                            saved_results: results,
                            remaining_tbc_slots: vec![],
                        }));
                        return Err(LuaError::Yield(vals));
                    }
                    Err(e) => return Err(e),
                }
                vm.close_upvalues(base);
                if vm.call_stack.len() <= entry_depth {
                    // Fire return hook before early return
                    if vm.hooks_active
                        && !vm.in_hook
                        && vm.hook_mask & HOOK_RETURN != 0
                        && vm.call_stack.last().is_some_and(|ci| ci.is_lua())
                    {
                        let ci = vm.call_stack.len() - 1;
                        vm.call_stack[ci].ntransfer = results.len() as u16;
                        vm.call_stack[ci_idx].pc = pc;
                        let _ = fire_hook(vm, "return", -1, entry_depth);
                    }
                    return Ok(results);
                }
                vm.call_stack[ci_idx].pc = pc;
                return_from_call(vm, &results)?;
            }

            OpCode::VarArgPrep => {
                // For the top-level chunk, this is a no-op.
                // For vararg functions, the caller has already set up vararg_base.
            }

            // ---- Closure ----
            OpCode::Closure => {
                let bx = inst.bx() as usize;
                // Use pre-flattened child proto index (no clone needed)
                let child_flat_idx = vm.protos[proto_idx].child_flat_indices[bx];

                // Read upvalue descriptors into a local array to release the borrow
                let upval_count = vm.protos[child_flat_idx].upvalues.len();
                let mut upval_descs_buf = [(false, 0u8); 256];
                for i in 0..upval_count {
                    let desc = &vm.protos[child_flat_idx].upvalues[i];
                    upval_descs_buf[i] = (desc.in_stack, desc.index);
                }

                // Capture upvalues
                let closure_idx_opt = vm.call_stack[ci_idx].closure_idx;
                let mut upvals = Vec::with_capacity(upval_count);
                for i in 0..upval_count {
                    let (in_stack, index) = upval_descs_buf[i];
                    if in_stack {
                        // Upvalue is in the current function's stack
                        let stack_idx = base + index as usize;
                        let uv_idx = vm.find_or_create_open_upval(stack_idx);
                        upvals.push(uv_idx);
                    } else {
                        // Upvalue is in the enclosing function's upvalue list
                        if let Some(parent_closure_idx) = closure_idx_opt {
                            let parent_closure = vm.gc.get_closure(parent_closure_idx);
                            let uv_idx = parent_closure.upvalues[index as usize];
                            upvals.push(uv_idx);
                        } else {
                            return Err(LuaError::Runtime(
                                "cannot capture upvalue from non-closure".to_string(),
                            ));
                        }
                    }
                }

                let new_closure_idx = vm.gc.alloc_closure(child_flat_idx, upvals);
                vm.stack[base + a] = TValue::from_closure(new_closure_idx);
            }

            // ---- Function calls ----
            OpCode::Call => {
                let b = inst.b() as usize;
                let c = inst.c() as usize;
                let func_val = vm.stack[base + a];
                let num_args = if b == 0 {
                    vm.stack_top - (base + a + 1)
                } else {
                    b - 1
                };
                let num_results = if c == 0 { -1i32 } else { c as i32 - 1 };

                if vm.call_stack.len() >= vm.max_call_depth {
                    return Err(LuaError::StackOverflow);
                }

                if let Some(closure_idx) = func_val.as_closure_idx() {
                    // Lua function call
                    let closure = vm.gc.get_closure(closure_idx);
                    let child_proto_idx = closure.proto_idx;
                    let child_proto = &vm.protos[child_proto_idx];
                    let num_params = child_proto.num_params as usize;
                    let is_vararg = child_proto.is_vararg;
                    let max_stack = child_proto.max_stack_size as usize;

                    let func_stack_pos = base + a;
                    let new_base = func_stack_pos + 1;

                    // --- JIT fast path ---
                    if vm.jit_enabled && !is_vararg {
                        // Increment call count and trigger compilation if needed
                        if child_proto_idx < vm.jit_call_counts.len() {
                            vm.jit_call_counts[child_proto_idx] += 1;
                            if vm.jit_call_counts[child_proto_idx] == vm.jit_threshold
                                && !vm.jit_functions.contains_key(&child_proto_idx)
                            {
                                if let Some(cb) = vm.jit_compile_callback {
                                    vm.call_stack[ci_idx].pc = pc;
                                    cb(vm, child_proto_idx);
                                }
                            }
                        }

                        // Execute JIT code if available
                        if let Some(&jit_fn) = vm.jit_functions.get(&child_proto_idx) {
                            vm.ensure_stack(new_base, max_stack + 1);

                            // Nil-fill extra params
                            for i in num_args..num_params {
                                vm.stack[new_base + i] = TValue::nil();
                            }

                            // Push a CallInfo so runtime helpers can find the closure
                            let mut ci = CallInfo::new(new_base, child_proto_idx);
                            ci.num_results = num_results;
                            ci.closure_idx = Some(closure_idx);
                            ci.func_stack_idx = func_stack_pos;
                            ci.ftransfer = 1;
                            ci.ntransfer = num_params as u16;
                            ci.saved_hook_line = vm.hook_last_line;
                            vm.call_stack.push(ci);
                            vm.call_stack[ci_idx].pc = pc;

                            let result = unsafe { jit_fn(vm as *mut Vm, new_base) };

                            if result >= 0 {
                                // JIT succeeded — place results directly at func_stack_pos
                                let nresults_actual = result as usize;
                                // Close upvalues for JIT frame
                                vm.close_upvalues(new_base);
                                // Pop JIT frame
                                vm.call_stack.pop();
                                // Place results without Vec allocation
                                if num_results < 0 {
                                    // Multi-return: copy results to func_stack_pos
                                    for i in 0..nresults_actual {
                                        vm.stack[func_stack_pos + i] = vm.stack[new_base + i];
                                    }
                                    vm.stack_top = func_stack_pos + nresults_actual;
                                } else {
                                    let count = num_results as usize;
                                    for i in 0..count {
                                        if i < nresults_actual {
                                            vm.stack[func_stack_pos + i] = vm.stack[new_base + i];
                                        } else {
                                            vm.stack[func_stack_pos + i] = TValue::nil();
                                        }
                                    }
                                }
                                continue;
                            } else {
                                // SIDE_EXIT — pop the JIT CallInfo, fall through to interpreter
                                eprintln!("[JIT] Side-exit proto {} (inline Call)", child_proto_idx);
                                vm.call_stack.pop();
                                let count = vm.jit_side_exit_counts
                                    .entry(child_proto_idx)
                                    .or_insert(0);
                                *count += 1;
                                if *count >= 3 {
                                    eprintln!("[JIT] Blacklisted proto {}", child_proto_idx);
                                    vm.jit_functions.remove(&child_proto_idx);
                                }
                            }
                        }
                    }

                    if is_vararg {
                        // Move fixed params to the right, store varargs
                        let _vararg_count = num_args.saturating_sub(num_params);
                        let actual_base = new_base + num_args; // after all args

                        vm.ensure_stack(actual_base, max_stack + 1);

                        // Copy fixed params to the new base
                        for i in 0..num_params.min(num_args) {
                            vm.stack[actual_base + i] = vm.stack[new_base + i];
                        }
                        // Nil-fill remaining params
                        for i in num_args..num_params {
                            vm.stack[actual_base + i] = TValue::nil();
                        }

                        vm.stack_top = actual_base + max_stack;

                        let mut ci = CallInfo::new(actual_base, child_proto_idx);
                        ci.num_results = num_results;
                        ci.closure_idx = Some(closure_idx);
                        ci.func_stack_idx = func_stack_pos;
                        ci.vararg_base = Some(new_base);
                        ci.ftransfer = 1;
                        ci.ntransfer = num_params as u16;
                        ci.saved_hook_line = vm.hook_last_line;
                        vm.call_stack.push(ci);
                        // Reset hook tracking for new frame (PUC: L->oldpc = 0)
                        if vm.hooks_active {
                            vm.hook_last_line = -1;
                            vm.hook_old_pc = 0;
                            if vm.hook_mask & HOOK_CALL != 0 {
                                vm.call_stack[ci_idx].pc = pc;
                                fire_hook(vm, "call", -1, entry_depth)?;
                            }
                        }
                    } else {
                        vm.ensure_stack(new_base, max_stack + 1);

                        // Nil-fill extra params
                        for i in num_args..num_params {
                            vm.stack[new_base + i] = TValue::nil();
                        }

                        vm.stack_top = new_base + max_stack;

                        let mut ci = CallInfo::new(new_base, child_proto_idx);
                        ci.num_results = num_results;
                        ci.closure_idx = Some(closure_idx);
                        ci.func_stack_idx = func_stack_pos;
                        ci.ftransfer = 1;
                        ci.ntransfer = num_params as u16;
                        ci.saved_hook_line = vm.hook_last_line;
                        vm.call_stack.push(ci);
                        // Reset hook tracking for new frame (PUC: L->oldpc = 0)
                        if vm.hooks_active {
                            vm.hook_last_line = -1;
                            vm.hook_old_pc = 0;
                            if vm.hook_mask & HOOK_CALL != 0 {
                                vm.call_stack[ci_idx].pc = pc;
                                fire_hook(vm, "call", -1, entry_depth)?;
                            }
                        }
                    }
                } else if let Some(native_idx) = func_val.as_native_idx() {
                    // Check for special pcall/xpcall dispatch
                    let is_pcall = vm.pcall_idx == Some(native_idx);
                    let is_xpcall = vm.xpcall_idx == Some(native_idx);

                    if is_pcall {
                        // pcall(func, ...) → call func with remaining args
                        let pcall_func = if num_args > 0 {
                            vm.stack[base + a + 1]
                        } else {
                            TValue::nil()
                        };
                        let pcall_args: Vec<TValue> =
                            (1..num_args).map(|i| vm.stack[base + a + 1 + i]).collect();

                        let result_base = base + a;
                        // Push native frame for pcall so it appears in tracebacks
                        let pcall_func_pos = base + a;
                        let mut pcall_ci = CallInfo::new(pcall_func_pos, usize::MAX);
                        pcall_ci.set_is_lua(false);
                        pcall_ci.func_stack_idx = pcall_func_pos;
                        vm.call_stack.push(pcall_ci);
                        let callee_frame_idx = vm.call_stack.len();
                        vm.call_stack[ci_idx].pc = pc;
                        match call_function(vm, pcall_func, &pcall_args) {
                            Ok(results) => {
                                vm.call_stack.pop(); // pop pcall frame
                                                     // Place (true, results...)
                                let mut all = vec![TValue::from_bool(true)];
                                all.extend(results);
                                let result_count = if num_results < 0 {
                                    all.len()
                                } else {
                                    num_results as usize
                                };
                                for i in 0..result_count {
                                    vm.stack[result_base + i] =
                                        all.get(i).copied().unwrap_or(TValue::nil());
                                }
                                if num_results < 0 {
                                    vm.stack_top = result_base + all.len();
                                }
                            }
                            Err(LuaError::Yield(vals)) => {
                                // Yield must propagate through pcall.
                                // Mark the direct callee frame (not the top frame, which
                                // may be deeper in nested pcall) so that when it returns
                                // on resume, return_from_call wraps results as pcall (true, ...).
                                // Don't pop pcall frame — it stays for yield continuation
                                if callee_frame_idx < vm.call_stack.len() {
                                    vm.call_stack[callee_frame_idx].call_status =
                                        CallStatus::PcallYield {
                                            result_base,
                                            num_results,
                                        };
                                }
                                return Err(LuaError::Yield(vals));
                            }
                            Err(e) => {
                                vm.call_stack.pop(); // pop pcall frame
                                                     // Place (false, error_value)
                                let err_val = e.to_tvalue(&mut vm.strings);
                                let all = [TValue::from_bool(false), err_val];
                                let result_count = if num_results < 0 {
                                    all.len()
                                } else {
                                    num_results as usize
                                };
                                for i in 0..result_count {
                                    vm.stack[result_base + i] =
                                        all.get(i).copied().unwrap_or(TValue::nil());
                                }
                                if num_results < 0 {
                                    vm.stack_top = result_base + all.len();
                                }
                            }
                        }
                    } else if is_xpcall {
                        // xpcall(func, handler, ...) → call func, on error call handler
                        let xpcall_func = if num_args > 0 {
                            vm.stack[base + a + 1]
                        } else {
                            TValue::nil()
                        };
                        let handler = if num_args > 1 {
                            vm.stack[base + a + 2]
                        } else {
                            TValue::nil()
                        };
                        let xpcall_args: Vec<TValue> =
                            (2..num_args).map(|i| vm.stack[base + a + 1 + i]).collect();

                        let result_base = base + a;
                        // Push native frame for xpcall so it appears in tracebacks
                        let xpcall_func_pos = base + a;
                        let mut xpcall_ci = CallInfo::new(xpcall_func_pos, usize::MAX);
                        xpcall_ci.set_is_lua(false);
                        xpcall_ci.func_stack_idx = xpcall_func_pos;
                        vm.call_stack.push(xpcall_ci);
                        let callee_frame_idx = vm.call_stack.len();
                        vm.call_stack[ci_idx].pc = pc;
                        match call_function(vm, xpcall_func, &xpcall_args) {
                            Ok(results) => {
                                vm.call_stack.pop(); // pop xpcall frame
                                let mut all = vec![TValue::from_bool(true)];
                                all.extend(results);
                                let result_count = if num_results < 0 {
                                    all.len()
                                } else {
                                    num_results as usize
                                };
                                for i in 0..result_count {
                                    vm.stack[result_base + i] =
                                        all.get(i).copied().unwrap_or(TValue::nil());
                                }
                                if num_results < 0 {
                                    vm.stack_top = result_base + all.len();
                                }
                            }
                            Err(LuaError::Yield(vals)) => {
                                // Yield must propagate through xpcall.
                                // Mark the direct callee frame so resume wraps results correctly.
                                // Don't pop xpcall frame — it stays for yield continuation
                                if callee_frame_idx < vm.call_stack.len() {
                                    vm.call_stack[callee_frame_idx].call_status =
                                        CallStatus::XpcallYield {
                                            result_base,
                                            num_results,
                                            handler,
                                        };
                                }
                                return Err(LuaError::Yield(vals));
                            }
                            Err(e) => {
                                vm.call_stack.pop(); // pop xpcall frame
                                                     // Call handler with error value
                                let err_val = e.to_tvalue(&mut vm.strings);
                                vm.call_stack[ci_idx].pc = pc;
                                let handler_result = call_function(vm, handler, &[err_val]);
                                match handler_result {
                                    Ok(results) => {
                                        let mut all = vec![TValue::from_bool(false)];
                                        all.extend(results);
                                        let result_count = if num_results < 0 {
                                            all.len()
                                        } else {
                                            num_results as usize
                                        };
                                        for i in 0..result_count {
                                            vm.stack[result_base + i] =
                                                all.get(i).copied().unwrap_or(TValue::nil());
                                        }
                                        if num_results < 0 {
                                            vm.stack_top = result_base + all.len();
                                        }
                                    }
                                    Err(_handler_err) => {
                                        // Handler itself errored — PUC Lua returns fixed message
                                        let msg_sid = vm.strings.intern(b"error in error handling");
                                        let handler_err_val = TValue::from_string_id(msg_sid);
                                        let all = [TValue::from_bool(false), handler_err_val];
                                        let result_count = if num_results < 0 {
                                            all.len()
                                        } else {
                                            num_results as usize
                                        };
                                        for i in 0..result_count {
                                            vm.stack[result_base + i] =
                                                all.get(i).copied().unwrap_or(TValue::nil());
                                        }
                                        if num_results < 0 {
                                            vm.stack_top = result_base + all.len();
                                        }
                                    }
                                }
                            }
                        }
                    } else if vm.is_redirect_native(native_idx) {
                        // Redirect through call_function for full VM access
                        // Collect args BEFORE firing hook
                        let args: Vec<TValue> =
                            (0..num_args).map(|i| vm.stack[base + a + 1 + i]).collect();

                        // Fire call hook for redirect native functions
                        if vm.hooks_active && !vm.in_hook && vm.hook_mask & HOOK_CALL != 0 {
                            let mut ci = CallInfo::new(base + a, usize::MAX);
                            ci.set_is_lua(false);
                            ci.func_stack_idx = base + a;
                            ci.num_results = num_results;
                            ci.ftransfer = 1;
                            ci.ntransfer = num_args as u16;
                            vm.call_stack.push(ci);
                            // Don't lower stack_top — keep it at caller's max to protect locals
                            vm.call_stack[ci_idx].pc = pc;
                            let _ = fire_hook(vm, "call", -1, entry_depth);
                            vm.call_stack.pop();
                            ci_idx = vm.call_stack.len() - 1;
                            base = vm.call_stack[ci_idx].base;
                        }

                        // For error(), push native CI so it appears in tracebacks
                        let is_error_fn = vm.error_idx == Some(native_idx);
                        if is_error_fn {
                            let error_func_pos = base + a;
                            let mut error_ci = CallInfo::new(error_func_pos, usize::MAX);
                            error_ci.set_is_lua(false);
                            error_ci.func_stack_idx = error_func_pos;
                            error_ci.num_results = num_results;
                            vm.call_stack.push(error_ci);
                        }

                        vm.call_stack[ci_idx].pc = pc;
                        let results = match call_function(vm, func_val, &args) {
                            Ok(r) => r,
                            Err(LuaError::Yield(vals)) => {
                                if is_error_fn {
                                    vm.call_stack.pop();
                                }
                                return Err(LuaError::Yield(vals));
                            }
                            Err(e) => {
                                // Leave error CI on stack for traceback visibility
                                // (other redirect natives just propagate the error)
                                return Err(e);
                            }
                        };
                        if is_error_fn {
                            vm.call_stack.pop();
                        }

                        // Fire return hook BEFORE placing results in caller's registers
                        // so the hook data doesn't overwrite locals.
                        if vm.hooks_active && !vm.in_hook && vm.hook_mask & HOOK_RETURN != 0 {
                            // Place hook frame and results above stack_top to avoid clobbering
                            let hook_func_pos = vm.stack_top;
                            let nres = results.len();
                            vm.ensure_stack(hook_func_pos + 1, nres + 1);
                            vm.stack[hook_func_pos] = func_val;
                            for i in 0..nres {
                                vm.stack[hook_func_pos + 1 + i] =
                                    results.get(i).copied().unwrap_or(TValue::nil());
                            }
                            let saved_top = vm.stack_top;
                            vm.stack_top = hook_func_pos + 1 + nres;
                            let mut ci = CallInfo::new(hook_func_pos, usize::MAX);
                            ci.set_is_lua(false);
                            ci.func_stack_idx = hook_func_pos;
                            ci.ftransfer = 1;
                            ci.ntransfer = nres as u16;
                            vm.call_stack.push(ci);
                            vm.call_stack[ci_idx].pc = pc;
                            let _ = fire_hook(vm, "return", -1, entry_depth);
                            vm.call_stack.pop();
                            ci_idx = vm.call_stack.len() - 1;
                            base = vm.call_stack[ci_idx].base;
                            vm.stack_top = saved_top;
                        }

                        // Now place results in caller's registers
                        let result_base = base + a;
                        let result_count = if num_results < 0 {
                            results.len()
                        } else {
                            num_results as usize
                        };
                        vm.ensure_stack(result_base, result_count + 1);
                        for i in 0..result_count {
                            vm.stack[result_base + i] =
                                results.get(i).copied().unwrap_or(TValue::nil());
                        }
                        if num_results < 0 {
                            vm.stack_top = result_base + results.len();
                        }
                        // PUC rethook: update L->oldpc after C function returns
                        // Use pc-1 because local pc has been advanced past the Call instruction
                        if vm.hooks_active {
                            vm.hook_old_pc = pc - 1;
                        }
                    } else {
                        // Normal native function call
                        // Use fixed-size buffer for args to avoid heap allocation
                        let arg_start = base + a + 1;
                        let mut arg_buf: [TValue; 8] = [TValue::nil(); 8];
                        let args_vec: Vec<TValue>;
                        let args: &[TValue] = if num_args <= 8 {
                            for i in 0..num_args {
                                arg_buf[i] = vm.stack[arg_start + i];
                            }
                            &arg_buf[..num_args]
                        } else {
                            args_vec = (0..num_args).map(|i| vm.stack[arg_start + i]).collect();
                            &args_vec
                        };

                        let hooks_active_now = vm.hooks_active && !vm.in_hook;

                        // Fire call hook for native functions
                        if hooks_active_now && vm.hook_mask & HOOK_CALL != 0 {
                            let mut ci = CallInfo::new(base + a, usize::MAX);
                            ci.set_is_lua(false);
                            ci.func_stack_idx = base + a;
                            ci.num_results = num_results;
                            ci.ftransfer = 1;
                            ci.ntransfer = num_args as u16;
                            vm.call_stack.push(ci);
                            vm.call_stack[ci_idx].pc = pc;
                            let _ = fire_hook(vm, "call", -1, entry_depth);
                            vm.call_stack.pop();
                            ci_idx = vm.call_stack.len() - 1;
                            base = vm.call_stack[ci_idx].base;
                        }

                        // Only push native CI frame when hooks are active (for tracebacks).
                        // On error we push it lazily.
                        let pushed_ci = if hooks_active_now {
                            let native_func_pos = base + a;
                            let mut native_ci = CallInfo::new(native_func_pos, usize::MAX);
                            native_ci.set_is_lua(false);
                            native_ci.func_stack_idx = native_func_pos;
                            native_ci.num_results = num_results;
                            vm.call_stack.push(native_ci);
                            true
                        } else {
                            false
                        };

                        let native_ref = vm.gc.get_native(native_idx);
                        let native_fn = native_ref.func;
                        let native_upvalue = native_ref.upvalue;
                        let mut ctx = NativeContext {
                            args,
                            gc: &mut vm.gc,
                            strings: &mut vm.strings,
                            upvalue: native_upvalue,
                        };
                        let results = match native_fn(&mut ctx) {
                            Ok(r) => r,
                            Err(e) => {
                                // Push CI frame for traceback if we didn't already
                                if !pushed_ci {
                                    let native_func_pos = base + a;
                                    let mut native_ci = CallInfo::new(native_func_pos, usize::MAX);
                                    native_ci.set_is_lua(false);
                                    native_ci.func_stack_idx = native_func_pos;
                                    native_ci.num_results = num_results;
                                    vm.call_stack.push(native_ci);
                                }
                                vm.call_stack[ci_idx].pc = pc;
                                let mut err = map_native_error(e);
                                err = qualify_func_name_in_error(vm, ci_idx, func_val, err);
                                err = adjust_method_error(vm, ci_idx, err);
                                return Err(add_error_prefix(vm, err));
                            }
                        };
                        if pushed_ci {
                            vm.call_stack.pop();
                            ci_idx = vm.call_stack.len() - 1;
                            base = vm.call_stack[ci_idx].base;
                        }

                        // Fire return hook BEFORE placing results in caller's registers
                        if hooks_active_now && vm.hook_mask & HOOK_RETURN != 0 {
                            let hook_func_pos = vm.stack_top;
                            let nres = results.len();
                            vm.ensure_stack(hook_func_pos + 1, nres + 1);
                            vm.stack[hook_func_pos] = func_val;
                            for i in 0..nres {
                                vm.stack[hook_func_pos + 1 + i] =
                                    results.get(i).copied().unwrap_or(TValue::nil());
                            }
                            let saved_top = vm.stack_top;
                            vm.stack_top = hook_func_pos + 1 + nres;
                            let mut ci = CallInfo::new(hook_func_pos, usize::MAX);
                            ci.set_is_lua(false);
                            ci.func_stack_idx = hook_func_pos;
                            ci.ftransfer = 1;
                            ci.ntransfer = nres as u16;
                            vm.call_stack.push(ci);
                            vm.call_stack[ci_idx].pc = pc;
                            let _ = fire_hook(vm, "return", -1, entry_depth);
                            vm.call_stack.pop();
                            ci_idx = vm.call_stack.len() - 1;
                            base = vm.call_stack[ci_idx].base;
                            vm.stack_top = saved_top;
                        }

                        // Place results in caller's registers
                        let result_base = base + a;
                        let result_count = if num_results < 0 {
                            results.len()
                        } else {
                            num_results as usize
                        };
                        vm.ensure_stack(result_base, result_count + 1);

                        for i in 0..result_count {
                            let val = results.get(i).copied().unwrap_or(TValue::nil());
                            vm.stack[result_base + i] = val;
                        }

                        if num_results < 0 {
                            vm.stack_top = result_base + results.len();
                        }
                        // PUC rethook: update L->oldpc after C function returns
                        // Use pc-1 because local pc has been advanced past the Call instruction
                        if vm.hooks_active {
                            vm.hook_old_pc = pc - 1;
                        }
                    }
                } else {
                    // Try __call metamethod
                    let mm_name = vm.mm_names.as_ref().unwrap().call;
                    if let Some(mm) = metamethod::get_metamethod(func_val, mm_name, &vm.gc) {
                        let mut mm_args = vec![func_val];
                        for i in 0..num_args {
                            mm_args.push(vm.stack[base + a + 1 + i]);
                        }
                        vm.call_stack[ci_idx].pc = pc;
                        let results = call_function(vm, mm, &mm_args)?;

                        let result_base = base + a;
                        let result_count = if num_results < 0 {
                            results.len()
                        } else {
                            num_results as usize
                        };

                        for i in 0..result_count {
                            let val = results.get(i).copied().unwrap_or(TValue::nil());
                            vm.stack[result_base + i] = val;
                        }

                        if num_results < 0 {
                            vm.stack_top = result_base + results.len();
                        }
                    } else {
                        vm.call_stack[ci_idx].pc = pc;
                        let obj_name = get_obj_name(vm, ci_idx, a);
                        return Err(runtime_error(
                            vm,
                            &format!(
                                "attempt to call a {} value{}",
                                obj_type_name(func_val, vm),
                                obj_name
                            ),
                        ));
                    }
                }
            }

            OpCode::TailCall => {
                let b = inst.b() as usize;
                let func_val = vm.stack[base + a];
                let num_args = if b == 0 {
                    vm.stack_top - (base + a + 1)
                } else {
                    b - 1
                };

                // Detect infinite tail recursion
                const MAX_TAIL_CALLS: u32 = 1_000_000;
                vm.call_stack[ci_idx].tail_count += 1;
                if vm.call_stack[ci_idx].tail_count > MAX_TAIL_CALLS {
                    return Err(LuaError::StackOverflow);
                }

                if let Some(closure_idx) = func_val.as_closure_idx() {
                    let closure = vm.gc.get_closure(closure_idx);
                    let child_proto_idx = closure.proto_idx;
                    let child_proto = &vm.protos[child_proto_idx];
                    let num_params = child_proto.num_params as usize;
                    let is_vararg = child_proto.is_vararg;
                    let max_stack = child_proto.max_stack_size as usize;

                    // Close upvalues for current frame
                    vm.close_upvalues(base);

                    let func_stack_pos = vm.call_stack[ci_idx].func_stack_idx;
                    let new_base = func_stack_pos + 1;

                    // Shift args down to reuse the current frame's stack space
                    vm.stack[func_stack_pos] = func_val;
                    for i in 0..num_args {
                        vm.stack[new_base + i] = vm.stack[base + a + 1 + i];
                    }

                    if is_vararg {
                        let actual_base = new_base + num_args;
                        vm.ensure_stack(actual_base, max_stack + 1);

                        for i in 0..num_params.min(num_args) {
                            vm.stack[actual_base + i] = vm.stack[new_base + i];
                        }
                        for i in num_args..num_params {
                            vm.stack[actual_base + i] = TValue::nil();
                        }

                        vm.stack_top = actual_base + max_stack;

                        let ci = &mut vm.call_stack[ci_idx];
                        ci.base = actual_base;
                        ci.pc = 0;
                        ci.proto_idx = child_proto_idx;
                        ci.closure_idx = Some(closure_idx);
                        ci.func_stack_idx = func_stack_pos;
                        ci.vararg_base = Some(new_base);
                        ci.set_is_tail_call(true);
                        ci.ftransfer = 1;
                        ci.ntransfer = num_params as u16;
                        pc = 0;
                        // Fire "tail call" hook
                        if vm.hooks_active && !vm.in_hook && vm.hook_mask & HOOK_CALL != 0 {
                            vm.hook_last_line = -1;
                            vm.call_stack[ci_idx].pc = pc;
                            fire_hook(vm, "tail call", -1, entry_depth)?;
                        }
                    } else {
                        vm.ensure_stack(new_base, max_stack + 1);

                        for i in num_args..num_params {
                            vm.stack[new_base + i] = TValue::nil();
                        }

                        vm.stack_top = new_base + max_stack;

                        let ci = &mut vm.call_stack[ci_idx];
                        ci.base = new_base;
                        ci.pc = 0;
                        ci.proto_idx = child_proto_idx;
                        ci.closure_idx = Some(closure_idx);
                        ci.func_stack_idx = func_stack_pos;
                        ci.vararg_base = None;
                        ci.set_is_tail_call(true);
                        ci.ftransfer = 1;
                        ci.ntransfer = num_params as u16;
                        pc = 0;
                        // Fire "tail call" hook
                        if vm.hooks_active && !vm.in_hook && vm.hook_mask & HOOK_CALL != 0 {
                            vm.hook_last_line = -1;
                            vm.call_stack[ci_idx].pc = pc;
                            fire_hook(vm, "tail call", -1, entry_depth)?;
                        }
                    }
                } else if let Some(native_idx) = func_val.as_native_idx() {
                    // Tail call to native: just call it normally and return
                    let args: Vec<TValue> =
                        (0..num_args).map(|i| vm.stack[base + a + 1 + i]).collect();

                    let results = if vm.is_redirect_native(native_idx) {
                        vm.call_stack[ci_idx].pc = pc;
                        call_function(vm, func_val, &args)?
                    } else {
                        let native_ref = vm.gc.get_native(native_idx);
                        let native_fn = native_ref.func;
                        let native_upvalue = native_ref.upvalue;
                        let mut ctx = NativeContext {
                            args: &args,
                            gc: &mut vm.gc,
                            strings: &mut vm.strings,
                            upvalue: native_upvalue,
                        };
                        match native_fn(&mut ctx) {
                            Ok(r) => r,
                            Err(e) => {
                                vm.call_stack[ci_idx].pc = pc;
                                let mut err = map_native_error(e);
                                err = qualify_func_name_in_error(vm, ci_idx, func_val, err);
                                err = adjust_method_error(vm, ci_idx, err);
                                return Err(add_error_prefix(vm, err));
                            }
                        }
                    };

                    vm.close_upvalues(base);
                    if vm.call_stack.len() <= entry_depth {
                        return Ok(results);
                    }
                    vm.call_stack[ci_idx].pc = pc;
                    return_from_call(vm, &results)?;
                } else {
                    // Try __call metamethod for TailCall — resolve iteratively
                    let mm_name = vm.mm_names.as_ref().unwrap().call;
                    let mut current = func_val;
                    let mut extra_self_args: Vec<TValue> = Vec::new();
                    loop {
                        if let Some(mm) = metamethod::get_metamethod(current, mm_name, &vm.gc) {
                            extra_self_args.push(current);
                            current = mm;
                            if current.as_closure_idx().is_some()
                                || current.as_native_idx().is_some()
                            {
                                break;
                            }
                        } else {
                            vm.call_stack[ci_idx].pc = pc;
                            let obj_name = get_obj_name(vm, ci_idx, a);
                            return Err(LuaError::Runtime(format!(
                                "attempt to call a {} value{}",
                                obj_type_name(current, vm),
                                obj_name
                            )));
                        }
                    }
                    // Build args: all the extra self args (in order) + original args
                    let mut mm_args = extra_self_args;
                    for i in 0..num_args {
                        mm_args.push(vm.stack[base + a + 1 + i]);
                    }
                    if let Some(closure_idx) = current.as_closure_idx() {
                        // Can do a real tail call with the resolved closure
                        let closure = vm.gc.get_closure(closure_idx);
                        let child_proto_idx = closure.proto_idx;
                        let child_proto = &vm.protos[child_proto_idx];
                        let num_params = child_proto.num_params as usize;
                        let is_vararg = child_proto.is_vararg;
                        let max_stack = child_proto.max_stack_size as usize;
                        let mm_num_args = mm_args.len();

                        vm.close_upvalues(base);
                        let func_stack_pos = vm.call_stack[ci_idx].func_stack_idx;
                        let new_base = func_stack_pos + 1;

                        vm.stack[func_stack_pos] = current;
                        vm.stack[new_base..(mm_num_args + new_base)]
                            .copy_from_slice(&mm_args[..mm_num_args]);

                        if is_vararg {
                            let actual_base = new_base + mm_num_args;
                            vm.ensure_stack(actual_base, max_stack + 1);
                            for i in 0..num_params.min(mm_num_args) {
                                vm.stack[actual_base + i] = vm.stack[new_base + i];
                            }
                            for i in mm_num_args..num_params {
                                vm.stack[actual_base + i] = TValue::nil();
                            }
                            vm.stack_top = actual_base + max_stack;
                            let ci = &mut vm.call_stack[ci_idx];
                            ci.base = actual_base;
                            ci.pc = 0;
                            ci.proto_idx = child_proto_idx;
                            ci.closure_idx = Some(closure_idx);
                            ci.func_stack_idx = func_stack_pos;
                            ci.vararg_base = Some(new_base);
                            pc = 0;
                        } else {
                            vm.ensure_stack(new_base, max_stack + 1);
                            for i in mm_num_args..num_params {
                                vm.stack[new_base + i] = TValue::nil();
                            }
                            vm.stack_top = new_base + max_stack;
                            let ci = &mut vm.call_stack[ci_idx];
                            ci.base = new_base;
                            ci.pc = 0;
                            ci.proto_idx = child_proto_idx;
                            ci.closure_idx = Some(closure_idx);
                            ci.func_stack_idx = func_stack_pos;
                            ci.vararg_base = None;
                            pc = 0;
                        }
                    } else {
                        // Native — call it normally and return
                        vm.call_stack[ci_idx].pc = pc;
                        let results = call_function_resolved(vm, current, &mm_args)?;

                        vm.close_upvalues(base);
                        if vm.call_stack.len() <= entry_depth {
                            return Ok(results);
                        }
                        vm.call_stack[ci_idx].pc = pc;
                        return_from_call(vm, &results)?;
                    }
                }
            }

            // ---- Vararg ----
            OpCode::VarArg => {
                let c = inst.c() as usize;
                let ci = &vm.call_stack[ci_idx];
                if let Some(vararg_base) = ci.vararg_base {
                    let num_params = vm.protos[proto_idx].num_params as usize;
                    // Varargs start after fixed params in the original arg area
                    let vararg_start = vararg_base + num_params;
                    let vararg_count = ci.base.saturating_sub(vararg_start);
                    let wanted = if c == 0 { vararg_count } else { c - 1 };

                    vm.ensure_stack(base + a, wanted + 1);

                    for i in 0..wanted {
                        if i < vararg_count {
                            vm.stack[base + a + i] = vm.stack[vararg_start + i];
                        } else {
                            vm.stack[base + a + i] = TValue::nil();
                        }
                    }

                    if c == 0 {
                        vm.stack_top = base + a + wanted;
                    }
                } else {
                    // No varargs available
                    let wanted = if c == 0 { 0 } else { c - 1 };
                    for i in 0..wanted {
                        vm.stack[base + a + i] = TValue::nil();
                    }
                    if c == 0 {
                        vm.stack_top = base + a;
                    }
                }
            }

            // ---- Upvalue operations ----
            OpCode::GetUpval => {
                let b = inst.b() as usize;
                let closure_idx = vm.call_stack[ci_idx].closure_idx.ok_or_else(|| {
                    LuaError::Runtime("GetUpval: no closure in frame".to_string())
                })?;
                let uv_idx = vm.gc.get_closure(closure_idx).upvalues[b];
                let val = vm.get_upval_value(uv_idx);
                vm.stack[base + a] = val;
            }

            OpCode::SetUpval => {
                let b = inst.b() as usize;
                let closure_idx = vm.call_stack[ci_idx].closure_idx.ok_or_else(|| {
                    LuaError::Runtime("SetUpval: no closure in frame".to_string())
                })?;
                let uv_idx = vm.gc.get_closure(closure_idx).upvalues[b];
                let val = vm.stack[base + a];
                vm.set_upval_value(uv_idx, val);
            }

            OpCode::Close => {
                vm.call_stack[ci_idx].pc = pc;
                close_tbc_variables(vm, ci_idx, base + a, None)?;
                vm.close_upvalues(base + a);
            }

            OpCode::Tbc => {
                let val = vm.stack[base + a];
                // nil and false are allowed as "not to be closed"
                if !val.is_falsy() {
                    // Non-nil/non-false values must have a __close metamethod
                    let mm_name = vm.mm_names.as_ref().unwrap().close;
                    if metamethod::get_metamethod(val, mm_name, &vm.gc).is_none() {
                        // Look up variable name from local_vars
                        let proto = &vm.protos[proto_idx];
                        let tbc_pc = pc.saturating_sub(1);
                        let var_name = proto
                            .local_vars
                            .iter()
                            .find(|lv| {
                                lv.reg as usize == a
                                    && (lv.start_pc as usize) <= tbc_pc
                                    && tbc_pc < (lv.end_pc as usize)
                            })
                            .map(|lv| {
                                String::from_utf8_lossy(vm.strings.get_bytes(lv.name)).into_owned()
                            })
                            .unwrap_or_else(|| "?".to_string());
                        vm.call_stack[ci_idx].pc = pc;
                        return Err(runtime_error(
                            vm,
                            &format!("variable '{}' got a non-closable value", var_name),
                        ));
                    }
                }
                // Register this stack slot as to-be-closed
                vm.call_stack[ci_idx].tbc_slots_push(base + a);
            }

            // ---- Generic for loop ----
            OpCode::TForPrep => {
                let sbx = inst.sbx();
                // Jump forward to TFORCALL
                pc = (pc as i64 + sbx as i64) as usize;
            }

            OpCode::TForCall => {
                let c = inst.c() as usize; // number of loop variables
                                           // Close upvalues for loop body variables BEFORE calling iterator
                                           // (so closures from previous iteration capture the old values,
                                           //  not the new values that the iterator is about to produce)
                vm.close_upvalues(base + a + 4);
                // Ensure stack_top is above all for-generic slots (including TBC and loop vars)
                // so that call_function doesn't overwrite them when setting up the call frame
                let min_top = base + a + 4 + c;
                if vm.stack_top < min_top {
                    vm.ensure_stack(base, a + 4 + c + 1);
                    vm.stack_top = min_top;
                }
                let iter_func = vm.stack[base + a];
                let state = vm.stack[base + a + 1];
                let control = vm.stack[base + a + 2];
                // Call iterator function: iter_func(state, control)
                vm.call_stack[ci_idx].pc = pc;
                let results = call_function(vm, iter_func, &[state, control])?;
                // Place results in R[A+4], R[A+5], ... R[A+3+c]
                for i in 0..c {
                    vm.stack[base + a + 4 + i] = results.get(i).copied().unwrap_or(TValue::nil());
                }
            }

            OpCode::TForLoop => {
                let sbx = inst.sbx();
                // A = base+2 (control variable position)
                // Check R[A+2] = first loop variable (which is at base+4 = (base+2)+2)
                let first_result = vm.stack[base + a + 2];
                if !first_result.is_nil() {
                    // Update control variable = first result
                    vm.stack[base + a] = first_result;
                    // Jump back to loop body
                    pc =
                        (pc as i64 + sbx as i64) as usize;
                }
            }

            // ---- Table operations ----
            OpCode::NewTable => {
                let b = inst.b() as usize;
                let c = inst.c() as usize;
                if inst.k() {
                    pc += 1;
                }
                let table_idx = vm.gc.alloc_table(b, c);
                vm.stack[base + a] = TValue::from_table(table_idx);
            }

            OpCode::GetTable => {
                let b = inst.b() as usize;
                let c = inst.c() as usize;
                let table_val = vm.stack[base + b];
                let key = vm.stack[base + c];
                vm.call_stack[ci_idx].pc = pc;
                let result = table_index(vm, table_val, key)
                    .map_err(|e| augment_index_error(e, vm, ci_idx, b))?;
                vm.stack[base + a] = result;
            }

            OpCode::GetI => {
                let b = inst.b() as usize;
                let c = inst.c() as i64;
                let table_val = vm.stack[base + b];
                // Fast path: plain table (no metatable) — direct raw access
                if let Some(table_idx) = table_val.as_table_idx() {
                    let table = vm.gc.get_table(table_idx);
                    if table.metatable.is_none() {
                        vm.stack[base + a] = table.raw_geti(c);
                    } else {
                        let key = TValue::from_integer(c);
                        vm.call_stack[ci_idx].pc = pc;
                        let result = table_index(vm, table_val, key)
                            .map_err(|e| augment_index_error(e, vm, ci_idx, b))?;
                        vm.stack[base + a] = result;
                    }
                } else {
                    let key = TValue::from_integer(c);
                    vm.call_stack[ci_idx].pc = pc;
                    let result = table_index(vm, table_val, key)
                        .map_err(|e| augment_index_error(e, vm, ci_idx, b))?;
                    vm.stack[base + a] = result;
                }
            }

            OpCode::GetField => {
                let b = inst.b() as usize;
                let c = inst.c() as usize;
                let table_val = vm.stack[base + b];
                let key_sid = match &vm.protos[proto_idx].constants[c] {
                    Constant::String(sid) => *sid,
                    _ => {
                        return Err(LuaError::Runtime(
                            "GetField: non-string constant".to_string(),
                        ))
                    }
                };
                // Fast path: plain table (no metatable) — direct string lookup
                if let Some(table_idx) = table_val.as_table_idx() {
                    let table = vm.gc.get_table(table_idx);
                    if table.metatable.is_none() {
                        vm.stack[base + a] = table.raw_get_str(key_sid);
                    } else {
                        let key = TValue::from_string_id(key_sid);
                        vm.call_stack[ci_idx].pc = pc;
                        let result = table_index(vm, table_val, key)
                            .map_err(|e| augment_index_error(e, vm, ci_idx, b))?;
                        vm.stack[base + a] = result;
                    }
                } else {
                    let key = TValue::from_string_id(key_sid);
                    vm.call_stack[ci_idx].pc = pc;
                    let result = table_index(vm, table_val, key)
                        .map_err(|e| augment_index_error(e, vm, ci_idx, b))?;
                    vm.stack[base + a] = result;
                }
            }

            OpCode::SetTable => {
                let b = inst.b() as usize;
                let c = inst.c() as usize;
                let table_val = vm.stack[base + a];
                let key = vm.stack[base + b];
                let val = if inst.k() {
                    let proto = &vm.protos[proto_idx];
                    constant_to_tvalue(&proto.constants[c], &mut vm.gc)
                } else {
                    vm.stack[base + c]
                };
                vm.call_stack[ci_idx].pc = pc;
                table_newindex(vm, table_val, key, val)
                    .map_err(|e| augment_index_error(e, vm, ci_idx, a))?;
            }

            OpCode::SetI => {
                let b = inst.b() as i64;
                let c = inst.c() as usize;
                let table_val = vm.stack[base + a];
                let val = if inst.k() {
                    let proto = &vm.protos[proto_idx];
                    constant_to_tvalue(&proto.constants[c], &mut vm.gc)
                } else {
                    vm.stack[base + c]
                };
                // Fast path: plain table (no metatable) — direct raw set
                if let Some(table_idx) = table_val.as_table_idx() {
                    let table = vm.gc.get_table(table_idx);
                    if table.metatable.is_none() {
                        let key = TValue::from_integer(b);
                        vm.gc
                            .table_raw_set(table_idx, key, val)
                            .map_err(|e: &str| LuaError::Runtime(e.to_string()))?;
                    } else {
                        let key = TValue::from_integer(b);
                        vm.call_stack[ci_idx].pc = pc;
                        table_newindex(vm, table_val, key, val)
                            .map_err(|e| augment_index_error(e, vm, ci_idx, a))?;
                    }
                } else {
                    let key = TValue::from_integer(b);
                    vm.call_stack[ci_idx].pc = pc;
                    table_newindex(vm, table_val, key, val)
                        .map_err(|e| augment_index_error(e, vm, ci_idx, a))?;
                }
            }

            OpCode::SetField => {
                let b = inst.b() as usize;
                let c = inst.c() as usize;
                let table_val = vm.stack[base + a];
                let proto = &vm.protos[proto_idx];
                let key_sid = match &proto.constants[b] {
                    Constant::String(sid) => *sid,
                    _ => {
                        return Err(LuaError::Runtime(
                            "SetField: non-string constant".to_string(),
                        ))
                    }
                };
                let val = if inst.k() {
                    constant_to_tvalue(&proto.constants[c], &mut vm.gc)
                } else {
                    vm.stack[base + c]
                };
                // Fast path: plain table (no metatable) — direct raw set
                if let Some(table_idx) = table_val.as_table_idx() {
                    let table = vm.gc.get_table(table_idx);
                    if table.metatable.is_none() {
                        let key = TValue::from_string_id(key_sid);
                        vm.gc
                            .table_raw_set(table_idx, key, val)
                            .map_err(|e: &str| LuaError::Runtime(e.to_string()))?;
                    } else {
                        let key = TValue::from_string_id(key_sid);
                        vm.call_stack[ci_idx].pc = pc;
                        table_newindex(vm, table_val, key, val)
                            .map_err(|e| augment_index_error(e, vm, ci_idx, a))?;
                    }
                } else {
                    let key = TValue::from_string_id(key_sid);
                    vm.call_stack[ci_idx].pc = pc;
                    table_newindex(vm, table_val, key, val)
                        .map_err(|e| augment_index_error(e, vm, ci_idx, a))?;
                }
            }

            OpCode::GetTabUp => {
                let b = inst.b() as usize;
                let c = inst.c() as usize;
                // Get upvalue[B] which should be a table, then index by K[C]
                let closure_idx = vm.call_stack[ci_idx]
                    .closure_idx
                    .ok_or_else(|| LuaError::Runtime("GetTabUp: no closure".to_string()))?;
                let closure = vm.gc.get_closure(closure_idx);
                if b >= closure.upvalues.len() {
                    return Err(LuaError::Runtime(format!(
                        "GetTabUp: upvalue index {} out of range (closure has {} upvalues)",
                        b,
                        closure.upvalues.len()
                    )));
                }
                let uv_idx = closure.upvalues[b];
                let upval = vm.get_upval_value(uv_idx);
                let key_sid = match &vm.protos[proto_idx].constants[c] {
                    Constant::String(sid) => *sid,
                    _ => {
                        return Err(LuaError::Runtime(
                            "GetTabUp: non-string constant".to_string(),
                        ))
                    }
                };
                let key = TValue::from_string_id(key_sid);
                vm.call_stack[ci_idx].pc = pc;
                let result = table_index(vm, upval, key)?;
                vm.stack[base + a] = result;
            }

            OpCode::SetTabUp => {
                let b = inst.b() as usize;
                let c = inst.c() as usize;
                let closure_idx = vm.call_stack[ci_idx]
                    .closure_idx
                    .ok_or_else(|| LuaError::Runtime("SetTabUp: no closure".to_string()))?;
                let uv_idx = vm.gc.get_closure(closure_idx).upvalues[a];
                let upval = vm.get_upval_value(uv_idx);
                let proto = &vm.protos[proto_idx];
                let key_sid = match &proto.constants[b] {
                    Constant::String(sid) => *sid,
                    _ => {
                        return Err(LuaError::Runtime(
                            "SetTabUp: non-string constant".to_string(),
                        ))
                    }
                };
                let val = if inst.k() {
                    constant_to_tvalue(&proto.constants[c], &mut vm.gc)
                } else {
                    vm.stack[base + c]
                };
                let key = TValue::from_string_id(key_sid);
                vm.call_stack[ci_idx].pc = pc;
                table_newindex(vm, upval, key, val)?;
            }

            OpCode::SetList => {
                let b = inst.b() as usize;
                let mut c = inst.c() as usize;
                if inst.k() {
                    let proto = &vm.protos[proto_idx];
                    let next_inst = proto.code[pc];
                    pc += 1;
                    c += next_inst.ax_field() as usize * 256;
                }
                let table_val = vm.stack[base + a];
                let table_idx = table_val
                    .as_table_idx()
                    .ok_or_else(|| LuaError::Runtime("SetList: not a table".to_string()))?;
                let count = if b == 0 {
                    vm.stack_top - (base + a + 1)
                } else {
                    b
                };
                let offset = (c - 1) * 50;
                for i in 1..=count {
                    let val = vm.stack[base + a + i];
                    vm.gc
                        .get_table_mut(table_idx)
                        .raw_seti((offset + i) as i64, val);
                }
            }

            OpCode::Self_ => {
                let b = inst.b() as usize;
                let c = inst.c() as usize;
                let table_val = vm.stack[base + b];
                vm.stack[base + a + 1] = table_val;
                let key = if inst.k() {
                    let proto = &vm.protos[proto_idx];
                    constant_to_tvalue(&proto.constants[c], &mut vm.gc)
                } else {
                    vm.stack[base + c]
                };
                // Fast path for Self_: obj is a table, try raw lookup first,
                // then check metatable.__index table (common OOP pattern)
                if let Some(table_idx) = table_val.as_table_idx() {
                    let key_sid = key.as_string_id();
                    let raw_result = if let Some(sid) = key_sid {
                        vm.gc.get_table(table_idx).raw_get_str(sid)
                    } else {
                        vm.gc.table_raw_get(table_idx, key)
                    };
                    if !raw_result.is_nil() {
                        vm.stack[base + a] = raw_result;
                    } else {
                        // Check metatable.__index (common: points to a class table)
                        let table = vm.gc.get_table(table_idx);
                        if let Some(mt_idx) = table.metatable {
                            let mm_index_name = vm.mm_names.as_ref().unwrap().index;
                            let mm_val = vm.gc.get_table(mt_idx).raw_get_str(mm_index_name);
                            if let Some(idx_table_idx) = mm_val.as_table_idx() {
                                // __index is a table: direct lookup
                                let idx_result = if let Some(sid) = key_sid {
                                    vm.gc.get_table(idx_table_idx).raw_get_str(sid)
                                } else {
                                    vm.gc.table_raw_get(idx_table_idx, key)
                                };
                                if !idx_result.is_nil() {
                                    vm.stack[base + a] = idx_result;
                                } else {
                                    // Deep chain or nil — use full table_index
                                    vm.call_stack[ci_idx].pc = pc;
                                    let result = table_index(vm, table_val, key)
                                        .map_err(|e| augment_index_error(e, vm, ci_idx, b))?;
                                    vm.stack[base + a] = result;
                                }
                            } else {
                                // __index is a function or something else — use full path
                                vm.call_stack[ci_idx].pc = pc;
                                let result = table_index(vm, table_val, key)
                                    .map_err(|e| augment_index_error(e, vm, ci_idx, b))?;
                                vm.stack[base + a] = result;
                            }
                        } else {
                            // No metatable, raw miss → nil
                            vm.stack[base + a] = TValue::nil();
                        }
                    }
                } else {
                    vm.call_stack[ci_idx].pc = pc;
                    let result = table_index(vm, table_val, key)
                        .map_err(|e| augment_index_error(e, vm, ci_idx, b))?;
                    vm.stack[base + a] = result;
                }
            }

            OpCode::ExtraArg => {}
        }
        // Flush local pc back to call stack.
        // After Return/Call opcodes ci_idx may have changed (frame popped/pushed),
        // so only flush if the current call stack still has our frame.
        if ci_idx < vm.call_stack.len() {
            vm.call_stack[ci_idx].pc = pc;
        }
    }
}

/// Get the proto for the current call frame.
#[allow(dead_code)]
fn get_proto(vm: &Vm, ci_idx: usize) -> &Proto {
    &vm.protos[vm.call_stack[ci_idx].proto_idx]
}

/// Close to-be-closed variables from the given call frame whose stack index >= from_level.
/// Calls __close(val, error_or_nil) in reverse order.
///
/// PUC Lua 5.4 semantics: when a __close method raises an error, that error
/// **replaces** the current error and is passed to subsequent __close calls.
/// All TBC variables are always closed regardless of errors.
/// Returns the final (possibly replaced) error.
fn close_tbc_variables(
    vm: &mut Vm,
    ci_idx: usize,
    from_level: usize,
    error_val: Option<TValue>,
) -> Result<(), LuaError> {
    // Track the evolving error — starts as the incoming error
    let mut current_err: Option<TValue> = error_val;

    // Process TBC slots in reverse order, removing them one at a time
    loop {
        // Find the last (highest-index) TBC slot >= from_level
        let slot = {
            let tbc = vm.call_stack[ci_idx].tbc_slots.as_deref().unwrap_or(&[]);
            let mut best: Option<(usize, usize)> = None; // (vec_idx, stack_slot)
            for (i, &s) in tbc.iter().enumerate() {
                if s >= from_level {
                    match best {
                        None => best = Some((i, s)),
                        Some((_, bs)) if s > bs => best = Some((i, s)),
                        _ => {}
                    }
                }
            }
            best
        };

        let (vec_idx, slot) = match slot {
            Some(v) => v,
            None => break, // no more TBC slots to close
        };

        // Remove this slot from the tracking list
        vm.call_stack[ci_idx].tbc_slots.as_mut().unwrap().remove(vec_idx);

        let val = vm.stack[slot];
        // Skip nil and false values (Lua 5.4: false is valid as "not to be closed")
        if val.is_falsy() {
            continue;
        }
        // Look up __close metamethod
        let mm_name = vm.mm_names.as_ref().unwrap().close;
        if let Some(mm) = metamethod::get_metamethod(val, mm_name, &vm.gc) {
            // Call __close(val, current_error_or_nil)
            let err_arg = current_err.unwrap_or(TValue::nil());
            vm.in_tbc_close += 1;
            let result = call_function(vm, mm, &[val, err_arg]);
            vm.in_tbc_close -= 1;
            match result {
                Ok(_) => { /* continue */ }
                Err(LuaError::Yield(vals)) => {
                    // Yield propagates immediately
                    // Remaining TBC slots are still in tbc_slots for later
                    return Err(LuaError::Yield(vals));
                }
                Err(e) => {
                    // Error in __close replaces the current error
                    current_err = Some(e.to_tvalue(&mut vm.strings));
                    vm.last_error_from_close = true;
                }
            }
        } else {
            // __close was removed after Tbc check — generate error about missing metamethod
            let err_msg = "attempt to call a nil value (metamethod 'close')".to_string();
            let sid = vm.strings.intern_or_create(err_msg.as_bytes());
            current_err = Some(TValue::from_string_id(sid));
            vm.last_error_from_close = true;
        }
    }

    // If we accumulated an error, propagate it
    if let Some(err) = current_err {
        return Err(LuaError::LuaValue(err));
    }
    Ok(())
}

/// Close TBC variables during error unwinding.
/// Collects all TBC slots from frames [target_depth..len), pops those frames,
/// then closes TBC variables in reverse order (highest stack slot first).
/// This matches PUC Lua behavior: callee frames are removed from the call stack
/// before __close handlers run, so debug.getinfo sees the correct caller (e.g. pcall).
fn unwind_tbc(vm: &mut Vm, target_depth: usize, error_val: Option<TValue>) -> Option<TValue> {
    let len = vm.call_stack.len();
    // Collect all TBC slots from frames being unwound
    let mut all_tbc_slots: Vec<usize> = Vec::new();
    for ci_idx in target_depth..len {
        if let Some(ref mut slots) = vm.call_stack[ci_idx].tbc_slots {
            all_tbc_slots.append(slots);
        }
    }
    // Sort in descending order (close highest stack slots first)
    all_tbc_slots.sort_unstable_by(|a, b| b.cmp(a));
    // Pop the unwinding frames BEFORE calling __close handlers
    vm.call_stack.truncate(target_depth);
    // Now close TBC variables with the call stack already unwound
    let mut current_err = error_val;
    for slot in all_tbc_slots {
        let val = vm.stack[slot];
        if val.is_falsy() {
            continue;
        }
        let mm_name = vm.mm_names.as_ref().unwrap().close;
        if let Some(mm) = metamethod::get_metamethod(val, mm_name, &vm.gc) {
            let err_arg = current_err.unwrap_or(TValue::nil());
            vm.in_tbc_close += 1;
            let result = call_function(vm, mm, &[val, err_arg]);
            vm.in_tbc_close -= 1;
            match result {
                Ok(_) => { /* __close succeeded; current_err preserved */ }
                Err(LuaError::Yield(_vals)) => {
                    // Yield during error unwind TBC — unusual but possible
                    // For now, treat as error
                    current_err = Some(TValue::nil());
                }
                Err(e) => {
                    // Error in __close replaces the current error
                    current_err = Some(e.to_tvalue(&mut vm.strings));
                }
            }
        }
    }
    current_err
}

/// Maximum number of __index/__newindex chain steps before erroring (matches PUC Lua).
const MAXTAGLOOP: usize = 2000;

/// Table index with __index metamethod support.
/// Handles: tables (with fallback to __index), and non-table values with __index.
/// Iterative implementation with MAXTAGLOOP guard to prevent infinite loops.
pub fn table_index(vm: &mut Vm, table_val: TValue, key: TValue) -> Result<TValue, LuaError> {
    let mut current = table_val;
    // Cache mm_name once before the loop to avoid repeated Option unwrap.
    let mm_name = vm.mm_names.as_ref().unwrap().index;
    // Pre-check if key is a string for fast-path raw_get_str.
    let key_sid = key.as_string_id();

    for _ in 0..MAXTAGLOOP {
        if let Some(table_idx) = current.as_table_idx() {
            // Fast path: use raw_get_str directly for string keys (skips boxed-int check,
            // as_integer check, as_float check, and tvalue_to_table_key conversion).
            let result = if let Some(sid) = key_sid {
                vm.gc.get_table(table_idx).raw_get_str(sid)
            } else {
                vm.gc.table_raw_get(table_idx, key)
            };
            if !result.is_nil() {
                return Ok(result);
            }
            // Check __index metamethod
            if let Some(mm) = metamethod::get_metamethod(current, mm_name, &vm.gc) {
                if mm.is_gc()
                    && (mm.gc_sub_tag() == Some(selune_core::gc::GC_SUB_CLOSURE)
                        || mm.gc_sub_tag() == Some(selune_core::gc::GC_SUB_NATIVE))
                {
                    // __index is a function: call with (table, key)
                    let results = call_function(vm, mm, &[current, key])?;
                    return Ok(results.first().copied().unwrap_or(TValue::nil()));
                }
                // __index is another value: continue chain with it as the new "table"
                current = mm;
                continue;
            } else {
                return Ok(TValue::nil());
            }
        } else {
            // Non-table: check for __index metamethod (valid for userdata, numbers, etc.)
            if let Some(mm) = metamethod::get_metamethod(current, mm_name, &vm.gc) {
                if mm.is_gc()
                    && (mm.gc_sub_tag() == Some(selune_core::gc::GC_SUB_CLOSURE)
                        || mm.gc_sub_tag() == Some(selune_core::gc::GC_SUB_NATIVE))
                {
                    // __index is a function: call with (object, key)
                    let results = call_function(vm, mm, &[current, key])?;
                    return Ok(results.first().copied().unwrap_or(TValue::nil()));
                }
                // __index is another value: continue chain
                current = mm;
                continue;
            } else {
                return Err(runtime_error(
                    vm,
                    &format!("attempt to index a {} value", obj_type_name(current, vm)),
                ));
            }
        }
    }
    Err(LuaError::Runtime(
        "'__index' chain too long; possible loop".to_string(),
    ))
}

/// Table newindex with __newindex metamethod support.
/// Iterative implementation with MAXTAGLOOP guard to prevent infinite loops.
pub fn table_newindex(
    vm: &mut Vm,
    table_val: TValue,
    key: TValue,
    val: TValue,
) -> Result<(), LuaError> {
    let mut current = table_val;
    // Cache mm_name once before the loop.
    let mm_name = vm.mm_names.as_ref().unwrap().newindex;
    // Pre-check if key is a string for fast-path lookup.
    let key_sid = key.as_string_id();

    for _ in 0..MAXTAGLOOP {
        if let Some(table_idx) = current.as_table_idx() {
            // Check if key already exists (raw) — fast path for string keys
            let existing = if let Some(sid) = key_sid {
                vm.gc.get_table(table_idx).raw_get_str(sid)
            } else {
                vm.gc.table_raw_get(table_idx, key)
            };
            if !existing.is_nil() {
                // Key exists, just set it (no metamethod)
                vm.gc
                    .table_raw_set(table_idx, key, val)
                    .map_err(|e: &str| LuaError::Runtime(e.to_string()))?;
                return Ok(());
            }
            // Key doesn't exist: check __newindex metamethod
            if let Some(mm) = metamethod::get_metamethod(current, mm_name, &vm.gc) {
                if mm.is_gc()
                    && (mm.gc_sub_tag() == Some(selune_core::gc::GC_SUB_CLOSURE)
                        || mm.gc_sub_tag() == Some(selune_core::gc::GC_SUB_NATIVE))
                {
                    // __newindex is a function: call with (table, key, value)
                    call_function(vm, mm, &[current, key, val])?;
                    return Ok(());
                }
                // __newindex is another value: continue chain
                current = mm;
                continue;
            } else {
                // No __newindex: just raw set
                vm.gc
                    .table_raw_set(table_idx, key, val)
                    .map_err(|e: &str| LuaError::Runtime(e.to_string()))?;
                return Ok(());
            }
        } else {
            // Non-table: check __newindex metamethod
            if let Some(mm) = metamethod::get_metamethod(current, mm_name, &vm.gc) {
                if mm.is_gc()
                    && (mm.gc_sub_tag() == Some(selune_core::gc::GC_SUB_CLOSURE)
                        || mm.gc_sub_tag() == Some(selune_core::gc::GC_SUB_NATIVE))
                {
                    // __newindex is a function: call with (object, key, value)
                    call_function(vm, mm, &[current, key, val])?;
                    return Ok(());
                }
                // __newindex is another value: continue chain
                current = mm;
                continue;
            } else {
                return Err(runtime_error(
                    vm,
                    &format!("attempt to index a {} value", obj_type_name(current, vm)),
                ));
            }
        }
    }
    Err(LuaError::Runtime(
        "'__newindex' chain too long; possible loop".to_string(),
    ))
}

/// Return from a function call, placing results in the caller's frame.
/// If the frame has PcallYield/XpcallYield status (from yielding through pcall/xpcall),
/// wraps results with (true, ...) and places at the pcall's result_base instead.
fn return_from_call(vm: &mut Vm, results: &[TValue]) -> Result<(), LuaError> {
    let ci_idx = vm.call_stack.len() - 1;
    let call_status = vm.call_stack[ci_idx].call_status.clone();
    let num_results = vm.call_stack[ci_idx].num_results;
    let func_stack_idx = vm.call_stack[ci_idx].func_stack_idx;

    // Fire return hook before popping the frame
    if vm.hooks_active
        && !vm.in_hook
        && vm.hook_mask & HOOK_RETURN != 0
        && vm.call_stack[ci_idx].is_lua()
    {
        // ftransfer/ntransfer should already be set by the Return opcode handler
        // ntransfer is set to actual result count
        vm.call_stack[ci_idx].ntransfer = results.len() as u16;
        let _ = fire_hook(vm, "return", -1, 0);
    }

    // Save the popped frame's saved_hook_line for restoration
    let saved_hook_line = vm
        .call_stack
        .last()
        .map(|ci| ci.saved_hook_line)
        .unwrap_or(-1);
    vm.call_stack.pop();

    match call_status {
        CallStatus::PcallYield {
            result_base,
            num_results: pcall_num_results,
        }
        | CallStatus::XpcallYield {
            result_base,
            num_results: pcall_num_results,
            ..
        } => {
            // Wrap results as pcall success: (true, results...)
            let mut all = vec![TValue::from_bool(true)];
            all.extend(results.iter().copied());
            let result_count = if pcall_num_results < 0 {
                all.len()
            } else {
                pcall_num_results as usize
            };
            vm.ensure_stack(result_base, result_count + 1);
            for i in 0..result_count {
                vm.stack[result_base + i] = all.get(i).copied().unwrap_or(TValue::nil());
            }
            if pcall_num_results < 0 {
                vm.stack_top = result_base + all.len();
            }
            // Pop the pcall/xpcall native CI that's now on top of the call stack
            // (it was left there when yield propagated through pcall)
            if let Some(top) = vm.call_stack.last() {
                if top.proto_idx == usize::MAX {
                    vm.call_stack.pop();
                }
            }
        }
        CallStatus::Normal | CallStatus::CloseReturnYield(_) => {
            // Normal result placement at func_stack_idx
            if num_results < 0 {
                for (i, &val) in results.iter().enumerate() {
                    vm.stack[func_stack_idx + i] = val;
                }
                vm.stack_top = func_stack_idx + results.len();
            } else {
                let count = num_results as usize;
                for i in 0..count {
                    let val = results.get(i).copied().unwrap_or(TValue::nil());
                    vm.stack[func_stack_idx + i] = val;
                }
            }
        }
    }

    // Restore hook_last_line from the popped frame's saved value (PUC: per-CI previousline)
    if vm.hooks_active {
        vm.hook_last_line = saved_hook_line;
        // PUC rethook: L->oldpc = pcRel(ci->u.l.savedpc, ci_func(ci)->p)
        // Set hook_old_pc to the CALL instruction (pc - 1) so the next line
        // hook check compares with the correct baseline. In PUC, savedpc is
        // one behind npci after vmfetch; our pc is already the next instruction.
        if let Some(caller) = vm.call_stack.last() {
            if caller.is_lua() && caller.pc > 0 {
                vm.hook_old_pc = caller.pc - 1;
            }
        }
    }

    Ok(())
}

/// Augment an index error with object name from the register that was indexed.
fn augment_index_error(e: LuaError, vm: &Vm, ci_idx: usize, reg: usize) -> LuaError {
    match &e {
        LuaError::Runtime(msg) if msg.contains("attempt to index") => {
            let obj_name = get_obj_name(vm, ci_idx, reg);
            if obj_name.is_empty() {
                e
            } else {
                LuaError::Runtime(format!("{}{}", msg, obj_name))
            }
        }
        _ => e,
    }
}

/// Augment an error from calling a metamethod with the metamethod name.
fn augment_mm_error(e: LuaError, mm_idx: u8) -> LuaError {
    match e {
        LuaError::Runtime(msg) if msg.contains("attempt to call") => {
            let mm_name = mm_index_to_name(mm_idx);
            LuaError::Runtime(format!("{} (metamethod '{}')", msg, mm_name))
        }
        other => other,
    }
}

/// Map mm_idx to metamethod name string.
fn mm_index_to_name(mm_idx: u8) -> &'static str {
    match mm_idx {
        0 => "add",
        1 => "sub",
        2 => "mul",
        3 => "mod",
        4 => "pow",
        5 => "div",
        6 => "idiv",
        7 => "band",
        8 => "bor",
        9 => "bxor",
        10 => "shl",
        11 => "shr",
        12 => "concat",
        13 => "lt",
        14 => "le",
        _ => "?",
    }
}

/// Map a NativeError to a LuaError.
fn map_native_error(e: NativeError) -> LuaError {
    match e {
        NativeError::String(s) => LuaError::Runtime(s),
        NativeError::Value(v) => LuaError::LuaValue(v),
        NativeError::IoError(s, _errno) => LuaError::Runtime(s),
    }
}

/// Adjust error messages from native functions when called via method syntax (Self_ instruction).
/// In Lua 5.4, "bad argument #1" becomes "bad self" and other arg numbers decrease by 1.
fn adjust_method_error(vm: &Vm, ci_idx: usize, err: LuaError) -> LuaError {
    let ci = &vm.call_stack[ci_idx];
    if ci.proto_idx >= vm.protos.len() {
        return err; // Not a Lua frame
    }
    let proto = &vm.protos[ci.proto_idx];
    // The current pc points past the Call instruction. The Call is at pc-1.
    // The Self_ would be before that. We need to check if the Call was preceded by Self_.
    let call_pc = if ci.pc > 1 {
        ci.pc - 1
    } else {
        return err;
    };
    // Self_ sets R[A] and R[A+1], then Call uses R[A]. The Self_ is typically at call_pc - 1,
    // but there could be instructions between (e.g., for extra args). Check a few back.
    let call_inst = proto.code[call_pc];
    let call_a = call_inst.a() as usize;
    // Look back for a Self_ that set register call_a
    let start = call_pc.saturating_sub(5);
    let mut is_method = false;
    for pc in (start..call_pc).rev() {
        let inst = proto.code[pc];
        if inst.opcode() == OpCode::Self_ && inst.a() as usize == call_a {
            is_method = true;
            break;
        }
    }
    if !is_method {
        return err;
    }
    match err {
        LuaError::Runtime(msg) => {
            // Replace "bad argument #1" with "bad self"
            let msg = msg.replace("bad argument #1", "bad self");
            // Shift other argument numbers: #2 -> #1, #3 -> #2, etc.
            let msg = shift_arg_numbers(&msg);
            LuaError::Runtime(msg)
        }
        other => other,
    }
}

/// Shift "bad argument #N" to "bad argument #(N-1)" for N >= 2.
fn shift_arg_numbers(msg: &str) -> String {
    use std::fmt::Write;
    let pattern = "bad argument #";
    let mut result = String::with_capacity(msg.len());
    let mut rest = msg;
    while let Some(pos) = rest.find(pattern) {
        result.push_str(&rest[..pos]);
        result.push_str(pattern);
        rest = &rest[pos + pattern.len()..];
        // Parse the number
        let num_end = rest
            .find(|c: char| !c.is_ascii_digit())
            .unwrap_or(rest.len());
        if num_end > 0 {
            if let Ok(n) = rest[..num_end].parse::<u32>() {
                if n >= 2 {
                    let _ = write!(result, "{}", n - 1);
                } else {
                    result.push_str(&rest[..num_end]);
                }
            } else {
                result.push_str(&rest[..num_end]);
            }
            rest = &rest[num_end..];
        }
    }
    result.push_str(rest);
    result
}

/// Search _G (and one level of sub-tables) for a function value, returning its qualified name.
/// Mirrors Lua 5.4's pushglobalfuncname from ldebug.c.
fn push_global_func_name(vm: &Vm, func: TValue) -> Option<String> {
    let env_idx = vm.env_idx?;
    let env = vm.gc.get_table(env_idx);
    // First search top-level globals
    for (key, val) in env.hash_entries() {
        if *val == func {
            if let selune_core::table::TableKey::String(sid) = key {
                let name = String::from_utf8_lossy(vm.strings.get_bytes(*sid));
                return Some(name.into_owned());
            }
        }
    }
    // Search one level deep in table-valued entries (e.g., table.sort, math.sin)
    for (key, val) in env.hash_entries() {
        if let Some(tidx) = val.as_table_idx() {
            if let selune_core::table::TableKey::String(mod_sid) = key {
                let sub_table = vm.gc.get_table(tidx);
                for (sub_key, sub_val) in sub_table.hash_entries() {
                    if *sub_val == func {
                        if let selune_core::table::TableKey::String(fn_sid) = sub_key {
                            let mod_name = String::from_utf8_lossy(vm.strings.get_bytes(*mod_sid));
                            let fn_name = String::from_utf8_lossy(vm.strings.get_bytes(*fn_sid));
                            return Some(format!("{}.{}", mod_name, fn_name));
                        }
                    }
                }
            }
        }
    }
    None
}

/// Replace the function name in a "bad argument #N to 'name'" error with a qualified name.
/// Only uses global table search — bytecode-based resolution is handled separately.
fn qualify_func_name_in_error(
    vm: &Vm,
    _ci_idx: usize,
    func_val: TValue,
    err: LuaError,
) -> LuaError {
    match &err {
        LuaError::Runtime(msg) if msg.contains("to '") => {
            if let Some(qualified) = push_global_func_name(vm, func_val) {
                if let Some(start) = msg.find("to '") {
                    let after = &msg[start + 4..];
                    if let Some(end) = after.find('\'') {
                        let current_name = &after[..end];
                        if current_name != qualified {
                            let rest = &after[end + 1..]; // skip past closing quote
                            let new_msg = format!("{}to '{}'{}", &msg[..start], qualified, rest);
                            return LuaError::Runtime(new_msg);
                        }
                    }
                }
            }
            err
        }
        _ => err,
    }
}

/// Return the operation description for metamethod error messages.
fn mm_op_description(mm_idx: u8) -> &'static str {
    match mm_idx {
        0..=6 => "arithmetic",         // add, sub, mul, mod, pow, div, idiv
        7..=11 => "bitwise operation", // band, bor, bxor, shl, shr
        12 => "concatenation",         // concat
        _ => "arithmetic",
    }
}

/// Call a Lua function (closure, native, or __call metamethod) with given args.
/// This is used by metamethod dispatch, pcall, xpcall, and TFORCALL.
/// Perform table.sort with full VM access for Lua comparator callbacks.
fn do_table_sort(
    vm: &mut Vm,
    table_idx: GcIdx<selune_core::table::Table>,
    comp: Option<TValue>,
) -> Result<(), LuaError> {
    vm.nonyieldable_depth += 1;
    let result = do_table_sort_inner(vm, table_idx, comp);
    vm.nonyieldable_depth -= 1;
    result
}

fn do_table_sort_inner(
    vm: &mut Vm,
    table_idx: GcIdx<selune_core::table::Table>,
    comp: Option<TValue>,
) -> Result<(), LuaError> {
    let table_val = TValue::from_table(table_idx);
    // Get length respecting __len metamethod
    let len = obj_len(vm, table_val)?;

    if len <= 1 {
        return Ok(());
    }

    // Check for array too big (PUC Lua limit: INT_MAX - 1)
    const TAB_MAXN: i64 = (i32::MAX as i64) - 1;
    if len > TAB_MAXN {
        return Err(LuaError::Runtime("array too big".to_string()));
    }

    let len = len as usize;

    // Read all values into a Vec, respecting __index metamethods
    let mut values: Vec<TValue> = Vec::with_capacity(len);
    for i in 1..=len {
        let key = TValue::from_full_integer(i as i64, &mut vm.gc);
        let val = table_index(vm, table_val, key)?;
        values.push(val);
    }

    // Check for invalid order function before sorting:
    // PUC Lua detects this when comp(a, a) returns true (non-strict order)
    if let Some(comp_fn) = comp {
        if !values.is_empty() {
            let test_val = values[0];
            let result =
                call_function(vm, comp_fn, &[test_val, test_val]).map_err(|e| match e {
                    LuaError::Yield(_) => {
                        LuaError::Runtime("attempt to yield across a C-call boundary".to_string())
                    }
                    other => other,
                })?;
            if result.first().map(|v| v.is_truthy()).unwrap_or(false) {
                return Err(LuaError::Runtime(
                    "invalid order function for sorting".to_string(),
                ));
            }
        }
    }

    // Insertion sort (stable, allows Lua callbacks between comparisons)
    for i in 1..values.len() {
        let key = values[i];
        let mut j = i;
        while j > 0 {
            let should_swap = if let Some(comp_fn) = comp {
                let results =
                    call_function(vm, comp_fn, &[key, values[j - 1]]).map_err(|e| match e {
                        LuaError::Yield(_) => LuaError::Runtime(
                            "attempt to yield across a C-call boundary".to_string(),
                        ),
                        other => other,
                    })?;
                results.first().map(|v| v.is_truthy()).unwrap_or(false)
            } else {
                // Use full < operator with metamethod support
                sort_default_lt(vm, key, values[j - 1])?
            };

            if should_swap {
                values[j] = values[j - 1];
                j -= 1;
            } else {
                break;
            }
        }
        values[j] = key;
    }

    // Write sorted values back, respecting __newindex metamethods
    for (i, &v) in values.iter().enumerate() {
        let key = TValue::from_full_integer((i + 1) as i64, &mut vm.gc);
        table_newindex(vm, table_val, key, v)?;
    }

    Ok(())
}

/// Default < comparison for table.sort, supporting metamethods.
fn sort_default_lt(vm: &mut Vm, va: TValue, vb: TValue) -> Result<bool, LuaError> {
    match compare::lua_lt(va, vb, &vm.gc, &vm.strings) {
        compare::CompareResult::Ok(v) => Ok(v),
        compare::CompareResult::NeedMetamethod => {
            let mm_name = vm.mm_names.as_ref().unwrap().lt;
            if let Some(mm) = metamethod::get_metamethod(va, mm_name, &vm.gc)
                .or_else(|| metamethod::get_metamethod(vb, mm_name, &vm.gc))
            {
                let res = call_function(vm, mm, &[va, vb])?;
                Ok(!res.first().copied().unwrap_or(TValue::nil()).is_falsy())
            } else {
                Err(order_error(vm, va, vb))
            }
        }
    }
}

/// string.gsub implementation — needs full VM access for function replacement.
fn do_string_gsub(
    vm: &mut Vm,
    subject: &[u8],
    pat: &[u8],
    repl: TValue,
    max_n: Option<i64>,
) -> Result<(Vec<u8>, i64), LuaError> {
    use selune_stdlib::pattern::{self, CAP_POSITION};

    let max_replacements = max_n.unwrap_or(i64::MAX);
    let mut result = Vec::new();
    let mut count = 0i64;
    let mut src = 0usize;
    // Track the end of the last successful replacement to prevent repeated empty matches
    // at the same position (Lua 5.3.3+ semantics).
    let mut lastmatch: Option<usize> = None;
    let anchor = !pat.is_empty() && pat[0] == b'^';
    let match_pat = if anchor { &pat[1..] } else { pat };

    // Create matcher once and reuse across iterations (avoids re-allocation per position).
    let mut matcher = pattern::PatternMatcher::new(subject, match_pat);

    loop {
        if count >= max_replacements || src > subject.len() {
            break;
        }

        // Try to match at position `src`.
        let ms = matcher.try_match_at(src);

        match ms {
            Err(e) => return Err(LuaError::Runtime(e)),
            Ok(Some(ms)) => {
                let (match_start, match_end) = ms.captures[0];
                debug_assert_eq!(match_start, src);

                // Check for repeated empty match at the same position.
                if match_end == match_start && lastmatch == Some(match_end) {
                    // Skip this empty match; push current char and advance.
                    if src < subject.len() {
                        result.push(subject[src]);
                        src += 1;
                    } else {
                        break;
                    }
                    if anchor {
                        break;
                    }
                    continue;
                }

                // Compute replacement
                let replacement = if let Some(repl_sid) = repl.as_string_id() {
                    let repl_bytes = vm.strings.get_bytes(repl_sid).to_vec();
                    pattern::expand_replacement(&repl_bytes, &ms, subject)
                        .map_err(LuaError::Runtime)?
                } else if let Some(_repl_table_idx) = repl.as_table_idx() {
                    let key = if ms.captures.len() > 1 {
                        let (cs, ce) = ms.captures[1];
                        if ce == CAP_POSITION {
                            TValue::from_full_integer((cs + 1) as i64, &mut vm.gc)
                        } else {
                            let slice = &subject[cs..ce];
                            let sid = vm.strings.intern_or_create(slice);
                            TValue::from_string_id(sid)
                        }
                    } else {
                        let slice = &subject[match_start..match_end];
                        let sid = vm.strings.intern_or_create(slice);
                        TValue::from_string_id(sid)
                    };
                    let val = table_index(vm, repl, key)?;
                    if val.is_falsy() {
                        subject[match_start..match_end].to_vec()
                    } else {
                        gsub_value_to_string(val, &vm.gc, &vm.strings)?
                    }
                } else if repl.is_function() {
                    let args: Vec<TValue> = if ms.captures.len() > 1 {
                        (1..ms.captures.len())
                            .map(|i| {
                                let (cs, ce) = ms.captures[i];
                                if ce == CAP_POSITION {
                                    TValue::from_full_integer((cs + 1) as i64, &mut vm.gc)
                                } else {
                                    let slice = &subject[cs..ce];
                                    let sid = vm.strings.intern_or_create(slice);
                                    TValue::from_string_id(sid)
                                }
                            })
                            .collect()
                    } else {
                        let slice = &subject[match_start..match_end];
                        let sid = vm.strings.intern_or_create(slice);
                        vec![TValue::from_string_id(sid)]
                    };
                    vm.nonyieldable_depth += 1;
                    let results = call_function(vm, repl, &args);
                    vm.nonyieldable_depth -= 1;
                    let results = results?;
                    let val = results.first().copied().unwrap_or(TValue::nil());
                    if val.is_falsy() {
                        subject[match_start..match_end].to_vec()
                    } else {
                        gsub_value_to_string(val, &vm.gc, &vm.strings)?
                    }
                } else {
                    return Err(LuaError::Runtime(
                        "bad argument #3 to 'gsub' (string/function/table expected)".to_string(),
                    ));
                };

                result.extend_from_slice(&replacement);
                count += 1;
                src = match_end;
                lastmatch = Some(match_end);
            }
            Ok(None) => {
                // No match at src. Push current character and advance.
                if src < subject.len() {
                    result.push(subject[src]);
                    src += 1;
                } else {
                    break;
                }
            }
        }
        if anchor {
            break;
        }
    }

    // Append remaining text
    result.extend_from_slice(&subject[src..]);

    Ok((result, count))
}

fn gsub_value_to_string(
    val: TValue,
    gc: &selune_core::gc::GcHeap,
    strings: &selune_core::string::StringInterner,
) -> Result<Vec<u8>, LuaError> {
    if let Some(sid) = val.as_string_id() {
        Ok(strings.get_bytes(sid).to_vec())
    } else if let Some(i) = val.as_full_integer(gc) {
        Ok(format!("{}", i).into_bytes())
    } else if let Some(f) = val.as_float() {
        Ok(format!("{}", f).into_bytes())
    } else {
        let type_name = selune_core::object::lua_type_name(val, gc);
        Err(LuaError::Runtime(format!(
            "invalid replacement value (a {})",
            type_name
        )))
    }
}

/// coroutine.resume(co, ...) — resume a suspended coroutine.
fn do_coroutine_resume(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    use crate::vm::CoroutineStatus;

    let co_val = args.first().copied().unwrap_or(TValue::nil());
    let resume_args = if args.len() > 1 { &args[1..] } else { &[] };

    let co_table_idx = co_val.as_table_idx().ok_or_else(|| {
        let type_name = selune_core::object::lua_type_name(co_val, &vm.gc);
        LuaError::Runtime(format!(
            "bad argument #1 to 'resume' (coroutine expected, got {})",
            type_name
        ))
    })?;

    // Verify this is actually a thread (has thread metatable)
    let is_thread = vm
        .gc
        .thread_metatable
        .is_some_and(|mt| vm.gc.get_table(co_table_idx).metatable == Some(mt));
    if !is_thread {
        return Err(LuaError::Runtime(
            "bad argument #1 to 'resume' (coroutine expected, got table)".to_string(),
        ));
    }

    // Check if this is the main thread handle
    let coro_id_val = vm.gc.get_table(co_table_idx).raw_geti(1);
    let mut coro_id = coro_id_val.as_integer().unwrap_or(-1);

    if coro_id == -2 {
        // Main thread — cannot resume
        let msg_sid = vm
            .strings
            .intern_or_create(b"cannot resume non-suspended coroutine");
        return Ok(vec![
            TValue::from_bool(false),
            TValue::from_string_id(msg_sid),
        ]);
    }

    // Check if this is the currently running coroutine
    if let Some(running_handle) = vm.running_coro_handle {
        if running_handle == co_table_idx {
            let msg_sid = vm
                .strings
                .intern_or_create(b"cannot resume non-suspended coroutine");
            return Ok(vec![
                TValue::from_bool(false),
                TValue::from_string_id(msg_sid),
            ]);
        }
    }

    if coro_id == -1 {
        // First resume: allocate coroutine from the function
        let func = vm.gc.get_table(co_table_idx).raw_geti(2);
        if !func.is_function() {
            return Err(LuaError::Runtime(
                "cannot resume dead coroutine".to_string(),
            ));
        }
        coro_id = vm.create_coroutine(func) as i64;
        vm.gc
            .get_table_mut(co_table_idx)
            .raw_seti(1, TValue::from_integer(coro_id));
    }

    let coro_idx = coro_id as usize;
    if coro_idx >= vm.coroutines.len() {
        return Err(LuaError::Runtime(
            "cannot resume dead coroutine".to_string(),
        ));
    }

    // Check status
    let status = vm.coroutines[coro_idx].status;
    if status != CoroutineStatus::Suspended {
        let msg = if status == CoroutineStatus::Dead {
            "cannot resume dead coroutine"
        } else {
            "cannot resume non-suspended coroutine"
        };
        let msg_sid = vm.strings.intern_or_create(msg.as_bytes());
        return Ok(vec![
            TValue::from_bool(false),
            TValue::from_string_id(msg_sid),
        ]);
    }

    // Save current (caller) state
    let prev_running_coro = vm.running_coro;
    let prev_running_coro_handle = vm.running_coro_handle;
    // Determine the caller's thread ID for upvalue remapping
    let caller_thread_id = prev_running_coro.unwrap_or(usize::MAX);
    // Remap caller's open upvalues so they remain accessible from the coroutine
    vm.remap_open_upvals_to_thread(caller_thread_id);

    // Save caller state by swapping VM state into a LuaThread on the caller stack.
    // We push an empty LuaThread, then swap each Vec field individually to avoid
    // the borrow checker issue of &mut vm + &mut vm.coro_caller_stack.
    {
        let mut caller = crate::vm::LuaThread {
            stack: Vec::new(),
            call_stack: Vec::new(),
            stack_top: 0,
            open_upvals: Vec::new(),
            status: CoroutineStatus::Normal,
            thread_id: caller_thread_id,
            hook_func: TValue::nil(),
            hook_mask: 0,
            hook_count: 0,
            hook_counter: 0,
            hooks_active: false,
            hook_last_line: -1,
            hook_old_pc: 0,
        };
        vm.save_running_state_swap(&mut caller);
        vm.coro_caller_stack.push(caller);
    }

    // Swap coroutine state into VM (coroutine slot gets the empty Vecs)
    vm.restore_coro_into_running(coro_idx);
    vm.running_coro = Some(coro_idx);
    vm.running_coro_handle = Some(co_table_idx);
    vm.coroutines[coro_idx].status = CoroutineStatus::Running;

    // Restore coroutine's remapped upvalues back to Open
    vm.restore_open_upvals_from_thread(coro_idx);

    // Update handle table status
    let running_sid = vm.strings.intern(b"running");
    vm.gc
        .get_table_mut(co_table_idx)
        .raw_seti(3, TValue::from_string_id(running_sid));

    // Update caller handle status to "normal"
    let normal_sid = vm.strings.intern(b"normal");
    if let Some(prev_handle) = prev_running_coro_handle {
        // Caller is a coroutine — set its handle to "normal"
        vm.gc
            .get_table_mut(prev_handle)
            .raw_seti(3, TValue::from_string_id(normal_sid));
    } else if let Some(main_handle) = vm.main_thread_handle {
        // Caller is main thread
        vm.gc
            .get_table_mut(main_handle)
            .raw_seti(3, TValue::from_string_id(normal_sid));
    }

    // If the coroutine has never run (call_stack is empty), set up the initial call
    let result = if vm.call_stack.is_empty() {
        // First resume: set up call frame for the function
        let func_val = vm.stack[0]; // function is at R[0]

        // Place resume args starting at R[1]
        let base = 1;
        vm.ensure_stack(base, resume_args.len() + 64);
        for (i, &arg) in resume_args.iter().enumerate() {
            vm.stack[base + i] = arg;
        }

        // Call the function
        call_function(vm, func_val, resume_args)
    } else {
        // Subsequent resume: return the resume args as yield results
        // The yielded coroutine is waiting for call_function to return,
        // so we return the resume args as the "result" of yield.
        // But wait — we need to re-enter the dispatch loop.
        // The coroutine was suspended inside execute_from which returned Err(Yield).
        // The call_stack is still set up. We need to restart execute_from.
        //
        // Actually, the yield was propagated as Err(Yield) through call_function,
        // which was called from the dispatch loop. The dispatch loop returned
        // the error up to execute_from, which returned it to do_coroutine_resume.
        //
        // On subsequent resume, we need to simulate call_function returning
        // Ok(resume_args). The call_stack still has the frame where yield was called.
        //
        // The simplest approach: the entry_depth for execute_from should be 0
        // (resume until coroutine finishes). But the coroutine was mid-execution
        // when it yielded. The Yield error unwound through execute_from.
        //
        // So the coroutine's call_stack has the frames UP TO the function that
        // called yield. When we resume, we need to re-enter execute_from with
        // the correct entry_depth and first provide the resume args as the
        // "return values" of the yield call.
        //
        // Let me think about this differently:
        // When yield is called, it returns Err(Yield(values)) from call_function.
        // This error propagates up through the dispatch loop (execute_from) and
        // back to do_coroutine_resume, which catches it.
        //
        // The coroutine's state at that point: the dispatch loop was in the
        // middle of processing a Call opcode that invoked yield. The call_stack
        // and pc are saved. But the Call opcode handler already returned an error
        // and didn't place results on the stack.
        //
        // On resume, we need to:
        // 1. Place the resume_args where the yield call's results would go
        // 2. Continue execution from where we left off
        //
        // The issue is that the Call opcode that called yield has already been
        // "processed" (the error unwound out of the opcode handler). The pc
        // was incremented past the Call opcode. So we can just put the resume
        // args on the stack at the right place and re-enter execute_from.
        //
        // But where do the results go? The Call opcode that invoked yield
        // would have placed results at (base + a) where a was the Call's A field.
        // Since the error unwound, those results were never placed.
        //
        // We need a different approach. Instead of having yield return an error
        // that unwinds out of execute_from, we should have yield set a flag
        // and return "results" that get placed by the Call opcode handler.
        //
        // Actually, the simplest approach that works with our architecture:
        // When yield is called from within the coroutine, the Err(Yield) propagates
        // up and unwinds the call stack. But we save the coroutine state BEFORE
        // the unwind happens.
        //
        // No wait — Err(Yield) is returned from call_function, which is called
        // from the Call opcode handler in execute_from. That error propagates up
        // through execute_from to here in do_coroutine_resume. But by that time,
        // the coroutine's state (stack, call_stack) has already been modified by
        // the error propagation.
        //
        // The key insight: Yield should NOT unwind. It should be caught at the
        // dispatch loop level (in execute_from) and cause a clean return without
        // unwinding. But that's what it does — `?` returns the error immediately
        // from the match arm in the dispatch loop.
        //
        // Let me check: when `call_function` returns `Err(Yield(values))`,
        // the `?` in the dispatch loop causes execute_from to return `Err(Yield(values))`.
        // The call_stack is NOT unwound (no truncation happens since the error
        // propagates through the normal control flow).
        //
        // But wait — the Call opcode handler does: `call_function(vm, ...)? ;`
        // With `?`, if the result is Err, it returns immediately from execute_from.
        // The current call frame's pc has already been incremented to point AFTER
        // the Call instruction. So when we resume, we need to place the resume
        // args at the Call result position and continue from there.
        //
        // Actually the Call opcode handler in the redirect-to-call_function branch:
        // ```
        // let results = call_function(vm, func_val, &args)?;
        // let result_base = base + a;
        // ```
        // If call_function returns Err(Yield), the `?` means we skip placing results.
        // On resume, we need to re-enter execute_from. The pc already points past
        // the Call opcode. We just need to place resume args at (base + a).
        //
        // But we don't know what (base + a) was! We lost that information when
        // the error propagated out.
        //
        // Solution: Save the result placement info when yield occurs.
        // We can store it in the coroutine's state.
        //
        // OR: simpler solution — don't use `?` for Yield. Instead, catch Yield
        // in the dispatch loop's Call handler and handle it specially.
        //
        // Let me take the simplest approach: on yield, we save the coroutine
        // state (including current pc, which is already past the Call).
        // On resume, we place resume args at the top of the coroutine's stack
        // and let execute_from continue. The trick is knowing WHERE to place them.
        //
        // For simplicity: resume args are placed at stack_top, and we mark
        // num_results for the yielded call frame. But this is getting complex.
        //
        // SIMPLEST APPROACH: Use a different strategy entirely.
        // Instead of having yield unwind via Err, have the coroutine's execute_from
        // return normally with the yield values. The resume handler catches this
        // and saves state.
        //
        // Actually, the simplest working approach:
        // 1. First resume: call the function via call_function
        // 2. On yield: Err(Yield) propagates up to here
        //    - Save coroutine state (call_stack is still intact because ? just returns)
        //    - Swap back to caller
        // 3. Subsequent resume: use execute_from directly to continue execution
        //    - Place resume args on stack as if yield returned them
        //    - Call execute_from with the current entry depth
        //
        // But for step 3, we need to know WHERE yield was called from.
        // The Call opcode handler that called yield is the last thing that ran.
        // After the `?`, the pc is already past that Call opcode.
        //
        // Actually wait — let me look at the redirect path more carefully.
        // For the redirect path (coro_yield_idx goes through call_function):
        //
        // In the inline Call handler:
        //   let results = call_function(vm, func_val, &args)?;
        //   let result_base = base + a;
        //   // place results at result_base
        //
        // If call_function returns Err(Yield), the `?` makes execute_from return
        // Err(Yield). The call_stack is intact. The current frame's pc is already
        // past the Call instruction (it was incremented when we decoded the instruction).
        //
        // On resume, we need to:
        //   1. Place resume args at result_base (base + a)
        //   2. Continue with execute_from
        //
        // But we don't know what `a` was. We need to look at the previous instruction.
        //
        // Alternative: save `result_base` and `num_results` in the coroutine state
        // when yield occurs. Let me add fields to LuaThread for this.

        // For now: look at the instruction BEFORE current pc to find the Call that yielded
        let ci = vm.call_stack.last().unwrap();
        let proto_idx = ci.proto_idx;
        let base = ci.base;
        let pc = ci.pc; // already incremented past the Call

        // The previous instruction should be the Call that triggered yield
        let prev_pc = pc.saturating_sub(1);
        let prev_inst = vm.protos[proto_idx].code[prev_pc];
        let prev_op = prev_inst.opcode();
        let prev_a = prev_inst.a() as usize;
        let (result_base, num_results) = if matches!(prev_op, OpCode::Call) {
            let c = prev_inst.c() as i32;
            let nr = if c == 0 { -1 } else { c - 1 };
            (base + prev_a, nr)
        } else {
            (base + prev_a, -1)
        };

        // Also fix up the yielded frame's func_stack_idx if the caller instruction
        // was TForCall — the caller expects results at R[A+4], not at func_stack_idx.
        if vm.call_stack.len() >= 2 {
            let caller_ci_idx = vm.call_stack.len() - 2;
            let caller_ci = &vm.call_stack[caller_ci_idx];
            if caller_ci.is_lua() {
                let caller_proto = &vm.protos[caller_ci.proto_idx];
                let caller_pc = caller_ci.pc.saturating_sub(1);
                if caller_pc < caller_proto.code.len() {
                    let caller_inst = caller_proto.code[caller_pc];
                    if matches!(caller_inst.opcode(), OpCode::TForCall) {
                        let caller_a = caller_inst.a() as usize;
                        let caller_c = caller_inst.c() as usize;
                        let caller_base = caller_ci.base;
                        // Fix the yielded frame's return placement to match TForCall's expectations
                        let last_idx = vm.call_stack.len() - 1;
                        vm.call_stack[last_idx].func_stack_idx = caller_base + caller_a + 4;
                        vm.call_stack[last_idx].num_results = caller_c as i32;
                    }
                }
            }
        }

        let resume_result: Vec<TValue> = resume_args.to_vec();

        // Place resume args as if they were the yield's return values
        let result_count = if num_results < 0 {
            resume_result.len()
        } else {
            num_results as usize
        };
        vm.ensure_stack(result_base, result_count + 1);
        for i in 0..result_count {
            vm.stack[result_base + i] = resume_result.get(i).copied().unwrap_or(TValue::nil());
        }
        if num_results < 0 {
            vm.stack_top = result_base + resume_result.len();
        }

        // Continue execution — loop to handle pcall/xpcall yield protection
        let mut exec_result = execute(vm, 0);

        // When execution errors, check for PcallYield/XpcallYield frames that
        // should catch the error (pcall protection survives yield/resume).
        while let Err(ref e) = exec_result {
            if matches!(e, LuaError::Yield(_)) {
                break; // yield propagates normally
            }
            // Find the deepest frame with PcallYield/XpcallYield status
            let pcall_frame = vm
                .call_stack
                .iter()
                .enumerate()
                .rev()
                .find(|(_, ci)| {
                    matches!(
                        ci.call_status,
                        CallStatus::PcallYield { .. } | CallStatus::XpcallYield { .. }
                    )
                })
                .map(|(idx, ci)| {
                    let (rb, nr, h) = match &ci.call_status {
                        CallStatus::PcallYield {
                            result_base,
                            num_results,
                        } => (*result_base, *num_results, None),
                        CallStatus::XpcallYield {
                            result_base,
                            num_results,
                            handler,
                        } => (*result_base, *num_results, Some(*handler)),
                        _ => unreachable!(),
                    };
                    (idx, rb, nr, h)
                });

            if let Some((pcall_ci_idx, result_base, pcall_num_results, xpcall_handler)) =
                pcall_frame
            {
                // Close TBC variables in frames from pcall frame upward (inclusive)
                let err_val = exec_result
                    .as_ref()
                    .err()
                    .map(|e| e.to_tvalue(&mut vm.strings));
                let final_err = unwind_tbc(vm, pcall_ci_idx, err_val);

                // Pop all frames above AND including the pcall frame.
                // Also pop the pcall/xpcall native frame below it if present
                // (pushed by call_function when processing pcall).
                let mut truncate_to = pcall_ci_idx;
                if truncate_to > 0 && !vm.call_stack[truncate_to - 1].is_lua() {
                    truncate_to -= 1;
                }
                vm.call_stack.truncate(truncate_to);

                let err_tval = final_err.unwrap_or_else(|| {
                    exec_result
                        .as_ref()
                        .err()
                        .unwrap()
                        .to_tvalue(&mut vm.strings)
                });

                // For xpcall, call the error handler to transform the error
                let result_val = if let Some(handler) = xpcall_handler {
                    match call_function(vm, handler, &[err_tval]) {
                        Ok(hr) => hr.first().copied().unwrap_or(TValue::nil()),
                        Err(_) => err_tval,
                    }
                } else {
                    err_tval
                };

                let all = vec![TValue::from_bool(false), result_val];
                let result_count = if pcall_num_results < 0 {
                    all.len()
                } else {
                    pcall_num_results as usize
                };
                vm.ensure_stack(result_base, result_count + 1);
                for i in 0..result_count {
                    vm.stack[result_base + i] = all.get(i).copied().unwrap_or(TValue::nil());
                }
                if pcall_num_results < 0 {
                    vm.stack_top = result_base + all.len();
                }

                // Continue execution from after the pcall frame
                if vm.call_stack.is_empty() {
                    // pcall was the outermost frame — return its result
                    exec_result = Ok(all);
                    break;
                }
                exec_result = execute(vm, 0);
                // Loop again in case there are more errors and more pcall frames
            } else {
                break; // No pcall frame to catch the error
            }
        }

        exec_result
    };

    // Execution finished (either returned or errored or yielded again)
    // Restore caller state
    let mut caller_state = vm.coro_caller_stack.pop().unwrap();

    // Helper: restore caller status to "running"
    let restore_caller_status = |vm: &mut Vm| {
        let running_s = vm.strings.intern(b"running");
        if let Some(prev_handle) = prev_running_coro_handle {
            vm.gc
                .get_table_mut(prev_handle)
                .raw_seti(3, TValue::from_string_id(running_s));
        } else if let Some(main_handle) = vm.main_thread_handle {
            vm.gc
                .get_table_mut(main_handle)
                .raw_seti(3, TValue::from_string_id(running_s));
        }
    };

    match &result {
        Ok(values) => {
            // Coroutine finished normally
            vm.remap_open_upvals_to_thread(coro_idx);
            vm.save_coro_state(coro_idx);
            // Clear call_stack for dead coroutine so traceback shows no frames
            vm.coroutines[coro_idx].call_stack.clear();
            vm.coroutines[coro_idx].status = CoroutineStatus::Dead;
            let dead_sid = vm.strings.intern(b"dead");
            vm.gc
                .get_table_mut(co_table_idx)
                .raw_seti(3, TValue::from_string_id(dead_sid));

            vm.restore_running_state_swap(&mut caller_state);
            vm.running_coro = prev_running_coro;
            vm.running_coro_handle = prev_running_coro_handle;
            vm.restore_open_upvals_from_thread(caller_thread_id);
            restore_caller_status(vm);

            let mut all = vec![TValue::from_bool(true)];
            all.extend(values.iter().copied());
            Ok(all)
        }
        Err(LuaError::Yield(yield_values)) => {
            // Coroutine yielded
            let yield_values = yield_values.clone();
            // Remap coroutine's open upvalues so they can be accessed from other threads
            vm.remap_open_upvals_to_thread(coro_idx);
            vm.save_coro_state(coro_idx);
            vm.coroutines[coro_idx].status = CoroutineStatus::Suspended;
            let suspended_sid = vm.strings.intern(b"suspended");
            vm.gc
                .get_table_mut(co_table_idx)
                .raw_seti(3, TValue::from_string_id(suspended_sid));

            vm.restore_running_state_swap(&mut caller_state);
            vm.running_coro = prev_running_coro;
            vm.running_coro_handle = prev_running_coro_handle;
            vm.restore_open_upvals_from_thread(caller_thread_id);
            restore_caller_status(vm);

            let mut all = vec![TValue::from_bool(true)];
            all.extend(yield_values);
            Ok(all)
        }
        Err(e) => {
            // Coroutine errored
            let err_val = e.to_tvalue(&mut vm.strings);
            vm.remap_open_upvals_to_thread(coro_idx);
            vm.save_coro_state(coro_idx);
            vm.coroutines[coro_idx].status = CoroutineStatus::Dead;
            let dead_sid = vm.strings.intern(b"dead");
            vm.gc
                .get_table_mut(co_table_idx)
                .raw_seti(3, TValue::from_string_id(dead_sid));
            // Store error in slot [4] for coroutine.close to retrieve
            vm.gc.get_table_mut(co_table_idx).raw_seti(4, err_val);

            vm.restore_running_state_swap(&mut caller_state);
            vm.running_coro = prev_running_coro;
            vm.running_coro_handle = prev_running_coro_handle;
            vm.restore_open_upvals_from_thread(caller_thread_id);
            restore_caller_status(vm);

            Ok(vec![TValue::from_bool(false), err_val])
        }
    }
}

/// Internal resume for coroutine.wrap'd function.
/// Args: (wrapper_table, ...) where wrapper_table[1] = coroutine handle.
fn do_coroutine_wrap_resume(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    // First arg is the wrapper table (passed as __call self)
    let wrapper_val = args.first().copied().unwrap_or(TValue::nil());
    let wrapper_idx = wrapper_val
        .as_table_idx()
        .ok_or_else(|| LuaError::Runtime("cannot resume dead coroutine".to_string()))?;

    // Get coroutine handle from wrapper[1]
    let co_handle = vm.gc.get_table(wrapper_idx).raw_geti(1);
    let mut resume_args = vec![co_handle];
    if args.len() > 1 {
        resume_args.extend_from_slice(&args[1..]);
    }

    // Call resume and unwrap the result (wrap raises errors instead of returning false)
    let result = do_coroutine_resume(vm, &resume_args)?;

    // result[0] = true/false, result[1..] = values or error
    let success = result.first().and_then(|v| v.as_bool()).unwrap_or(false);
    if success {
        Ok(result[1..].to_vec())
    } else {
        let err = result.get(1).copied().unwrap_or(TValue::nil());
        if let Some(sid) = err.as_string_id() {
            let msg = String::from_utf8_lossy(vm.strings.get_bytes(sid)).into_owned();
            Err(LuaError::Runtime(msg))
        } else {
            Err(LuaError::LuaValue(err))
        }
    }
}

pub fn call_function(vm: &mut Vm, func: TValue, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    // Resolve __call metamethods iteratively to avoid Rust stack overflow
    let mut current_func = func;
    let mut owned_args: Option<Vec<TValue>> = None;
    loop {
        let effective_args: &[TValue] = match &owned_args {
            Some(v) => v.as_slice(),
            None => args,
        };
        if current_func.as_closure_idx().is_some() || current_func.as_native_idx().is_some() {
            return call_function_resolved(vm, current_func, effective_args);
        } else {
            // Try __call metamethod
            let mm_name = vm.mm_names.as_ref().unwrap().call;
            if let Some(mm) = crate::metamethod::get_metamethod(current_func, mm_name, &vm.gc) {
                // Prepend the original value as first arg
                let mut new_args = vec![current_func];
                new_args.extend_from_slice(effective_args);
                current_func = mm;
                owned_args = Some(new_args);
                // Continue loop to resolve next __call level
            } else {
                return Err(runtime_error(
                    vm,
                    &format!(
                        "attempt to call a {} value",
                        obj_type_name(current_func, vm)
                    ),
                ));
            }
        }
    }
}

fn call_function_resolved(
    vm: &mut Vm,
    func: TValue,
    args: &[TValue],
) -> Result<Vec<TValue>, LuaError> {
    vm.c_stack_depth += 1;
    let result = call_function_inner(vm, func, args);
    vm.c_stack_depth -= 1;
    result
}

fn call_function_inner(
    vm: &mut Vm,
    func: TValue,
    args: &[TValue],
) -> Result<Vec<TValue>, LuaError> {
    if vm.c_stack_depth >= vm.max_c_stack_depth {
        return Err(LuaError::StackOverflow);
    }
    if let Some(closure_idx) = func.as_closure_idx() {
        // Lua closure call
        let closure = vm.gc.get_closure(closure_idx);
        let child_proto_idx = closure.proto_idx;
        let child_proto = &vm.protos[child_proto_idx];
        let num_params = child_proto.num_params as usize;
        let is_vararg = child_proto.is_vararg;
        let max_stack = child_proto.max_stack_size as usize;

        if vm.call_stack.len() >= vm.max_call_depth {
            return Err(LuaError::StackOverflow);
        }

        // Place func and args above current stack_top
        let func_pos = vm.stack_top;
        let new_base = func_pos + 1;
        let needed = new_base + args.len() + max_stack + num_params + 1;
        vm.ensure_stack(0, needed);

        vm.stack[func_pos] = func;
        for (i, &arg) in args.iter().enumerate() {
            vm.stack[new_base + i] = arg;
        }

        let saved_call_depth = vm.call_stack.len();
        let entry_depth = saved_call_depth + 1;

        // --- JIT fast path for call_function_inner ---
        if vm.jit_enabled && !is_vararg {
            // Increment call count and trigger compilation if needed
            if child_proto_idx < vm.jit_call_counts.len() {
                vm.jit_call_counts[child_proto_idx] += 1;
                if vm.jit_call_counts[child_proto_idx] == vm.jit_threshold
                    && !vm.jit_functions.contains_key(&child_proto_idx)
                {
                    if let Some(cb) = vm.jit_compile_callback {
                        cb(vm, child_proto_idx);
                    }
                }
            }

            if let Some(&jit_fn) = vm.jit_functions.get(&child_proto_idx) {
                vm.ensure_stack(new_base, max_stack + 1);

                for i in args.len()..num_params {
                    vm.stack[new_base + i] = TValue::nil();
                }

                let saved_top = vm.stack_top;

                // Push CallInfo so runtime helpers can find the closure
                let mut ci = CallInfo::new(new_base, child_proto_idx);
                ci.num_results = -1;
                ci.closure_idx = Some(closure_idx);
                ci.func_stack_idx = func_pos;
                ci.ftransfer = 1;
                ci.ntransfer = num_params as u16;
                ci.saved_hook_line = vm.hook_last_line;
                vm.call_stack.push(ci);

                let result = unsafe { jit_fn(vm as *mut Vm, new_base) };

                if result >= 0 {
                    let nresults_actual = result as usize;
                    // Copy results to a stack-local buffer to avoid overlap issues
                    let mut results_buf = [TValue::nil(); 16];
                    let n = nresults_actual.min(16);
                    for i in 0..n {
                        results_buf[i] = vm.stack[new_base + i];
                    }
                    vm.close_upvalues(new_base);
                    vm.call_stack.pop();
                    vm.stack_top = saved_top;
                    return Ok(results_buf[..n].to_vec());
                } else {
                    // SIDE_EXIT — pop JIT frame, fall through to interpreter
                    vm.call_stack.pop();
                    let count = vm.jit_side_exit_counts
                        .entry(child_proto_idx)
                        .or_insert(0);
                    *count += 1;
                    if *count >= 3 {
                        vm.jit_functions.remove(&child_proto_idx);
                    }
                }
            }
        }

        if is_vararg {
            let num_args = args.len();
            let actual_base = new_base + num_args;
            vm.ensure_stack(actual_base, max_stack + 1);

            for i in 0..num_params.min(num_args) {
                vm.stack[actual_base + i] = vm.stack[new_base + i];
            }
            for i in num_args..num_params {
                vm.stack[actual_base + i] = TValue::nil();
            }

            let saved_top = vm.stack_top;
            vm.stack_top = actual_base + max_stack;

            let mut ci = CallInfo::new(actual_base, child_proto_idx);
            ci.num_results = -1;
            ci.closure_idx = Some(closure_idx);
            ci.func_stack_idx = func_pos;
            ci.vararg_base = Some(new_base);
            ci.ftransfer = 1;
            ci.ntransfer = num_params as u16;
            if vm.pending_hook_call {
                ci.set_is_hook_call(true);
                vm.pending_hook_call = false;
            }
            if vm.in_tbc_close > 0 {
                ci.set_is_tbc_close(true);
            }
            ci.saved_hook_line = vm.hook_last_line;
            vm.call_stack.push(ci);
            // Reset hook tracking and fire call hook
            let saved_hook_line = vm.hook_last_line;
            let saved_hook_old_pc = vm.hook_old_pc;
            if vm.hooks_active {
                vm.hook_last_line = -1;
                vm.hook_old_pc = 0;
                if !vm.in_hook && vm.hook_mask & HOOK_CALL != 0 {
                    let _ = fire_hook(vm, "call", -1, entry_depth);
                }
            }

            let mut result = execute_from(vm, entry_depth);
            // Restore hook state after call returns
            if vm.hooks_active {
                vm.hook_last_line = saved_hook_line;
                vm.hook_old_pc = saved_hook_old_pc;
            }
            // For Yield: do NOT clean up — coroutine state must be preserved
            if matches!(&result, Err(LuaError::Yield(_))) {
                return result;
            }
            if result.is_err() {
                // Close TBC variables in all unwinding frames; error may be replaced
                let err_val = result.as_ref().err().map(|e| e.to_tvalue(&mut vm.strings));
                if let Some(final_err) = unwind_tbc(vm, saved_call_depth, err_val) {
                    result = Err(LuaError::LuaValue(final_err));
                }
            }
            vm.call_stack.truncate(saved_call_depth);
            vm.stack_top = saved_top;
            result
        } else {
            vm.ensure_stack(new_base, max_stack + 1);

            for i in args.len()..num_params {
                vm.stack[new_base + i] = TValue::nil();
            }

            let saved_top = vm.stack_top;
            vm.stack_top = new_base + max_stack;

            let mut ci = CallInfo::new(new_base, child_proto_idx);
            ci.num_results = -1;
            ci.closure_idx = Some(closure_idx);
            ci.func_stack_idx = func_pos;
            ci.ftransfer = 1;
            ci.ntransfer = num_params as u16;
            if vm.pending_hook_call {
                ci.set_is_hook_call(true);
                vm.pending_hook_call = false;
            }
            if vm.in_tbc_close > 0 {
                ci.set_is_tbc_close(true);
            }
            ci.saved_hook_line = vm.hook_last_line;
            vm.call_stack.push(ci);
            // Reset hook tracking and fire call hook
            let saved_hook_line2 = vm.hook_last_line;
            let saved_hook_old_pc2 = vm.hook_old_pc;
            if vm.hooks_active {
                vm.hook_last_line = -1;
                vm.hook_old_pc = 0;
                if !vm.in_hook && vm.hook_mask & HOOK_CALL != 0 {
                    let _ = fire_hook(vm, "call", -1, entry_depth);
                }
            }

            let mut result = execute_from(vm, entry_depth);
            // Restore hook state after call returns
            if vm.hooks_active {
                vm.hook_last_line = saved_hook_line2;
                vm.hook_old_pc = saved_hook_old_pc2;
            }
            // For Yield: do NOT clean up — coroutine state must be preserved
            if matches!(&result, Err(LuaError::Yield(_))) {
                return result;
            }
            if result.is_err() {
                // Close TBC variables in all unwinding frames; error may be replaced
                let err_val = result.as_ref().err().map(|e| e.to_tvalue(&mut vm.strings));
                if let Some(final_err) = unwind_tbc(vm, saved_call_depth, err_val) {
                    result = Err(LuaError::LuaValue(final_err));
                }
            }
            vm.call_stack.truncate(saved_call_depth);
            vm.stack_top = saved_top;
            result
        }
    } else if let Some(native_idx) = func.as_native_idx() {
        // Check for pcall/xpcall special dispatch
        let is_pcall = vm.pcall_idx == Some(native_idx);
        let is_xpcall = vm.xpcall_idx == Some(native_idx);

        if is_pcall {
            let pcall_func = args.first().copied().unwrap_or(TValue::nil());
            let pcall_args = if args.len() > 1 { &args[1..] } else { &[] };
            // Push native frame for pcall so it appears in tracebacks
            let func_pos = vm.stack_top;
            vm.ensure_stack(func_pos + 1, 0);
            vm.stack[func_pos] = func;
            let mut pcall_ci = CallInfo::new(func_pos, usize::MAX);
            pcall_ci.set_is_lua(false);
            pcall_ci.func_stack_idx = func_pos;
            vm.call_stack.push(pcall_ci);
            let callee_frame_idx = vm.call_stack.len();
            match call_function(vm, pcall_func, pcall_args) {
                Ok(results) => {
                    vm.call_stack.pop(); // pop pcall frame
                    let mut all = vec![TValue::from_bool(true)];
                    all.extend(results);
                    Ok(all)
                }
                Err(LuaError::Yield(vals)) => {
                    // Mark the direct callee frame with PcallYield so resume
                    // knows to wrap results. The func_stack_idx of the callee
                    // frame serves as the result_base for the pcall.
                    // Don't pop pcall frame — it stays for yield continuation
                    if callee_frame_idx < vm.call_stack.len() {
                        let fsi = vm.call_stack[callee_frame_idx].func_stack_idx;
                        vm.call_stack[callee_frame_idx].call_status = CallStatus::PcallYield {
                            result_base: fsi,
                            num_results: -1,
                        };
                    }
                    Err(LuaError::Yield(vals))
                }
                Err(e) => {
                    vm.call_stack.pop(); // pop pcall frame
                    let err_val = e.to_tvalue(&mut vm.strings);
                    Ok(vec![TValue::from_bool(false), err_val])
                }
            }
        } else if is_xpcall {
            let xpcall_func = args.first().copied().unwrap_or(TValue::nil());
            let handler = args.get(1).copied().unwrap_or(TValue::nil());
            let xpcall_args = if args.len() > 2 { &args[2..] } else { &[] };
            // Push native frame for xpcall so it appears in tracebacks
            let func_pos = vm.stack_top;
            vm.ensure_stack(func_pos + 1, 0);
            vm.stack[func_pos] = func;
            let mut xpcall_ci = CallInfo::new(func_pos, usize::MAX);
            xpcall_ci.set_is_lua(false);
            xpcall_ci.func_stack_idx = func_pos;
            vm.call_stack.push(xpcall_ci);
            let callee_frame_idx = vm.call_stack.len();
            match call_function(vm, xpcall_func, xpcall_args) {
                Ok(results) => {
                    vm.call_stack.pop(); // pop xpcall frame
                    let mut all = vec![TValue::from_bool(true)];
                    all.extend(results);
                    Ok(all)
                }
                Err(LuaError::Yield(vals)) => {
                    // Don't pop xpcall frame — it stays for yield continuation
                    if callee_frame_idx < vm.call_stack.len() {
                        let fsi = vm.call_stack[callee_frame_idx].func_stack_idx;
                        vm.call_stack[callee_frame_idx].call_status = CallStatus::XpcallYield {
                            result_base: fsi,
                            num_results: -1,
                            handler,
                        };
                    }
                    Err(LuaError::Yield(vals))
                }
                Err(e) => {
                    vm.call_stack.pop(); // pop xpcall frame
                    let err_val = e.to_tvalue(&mut vm.strings);
                    match call_function(vm, handler, &[err_val]) {
                        Ok(handler_results) => {
                            let mut all = vec![TValue::from_bool(false)];
                            all.extend(handler_results);
                            Ok(all)
                        }
                        Err(_handler_err) => {
                            let msg_sid = vm.strings.intern(b"error in error handling");
                            let handler_err_val = TValue::from_string_id(msg_sid);
                            Ok(vec![TValue::from_bool(false), handler_err_val])
                        }
                    }
                }
            }
        } else if vm.table_sort_idx == Some(native_idx) {
            // table.sort(t [,comp]) — needs full VM access for Lua comparator
            let table_val = args.first().copied().unwrap_or(TValue::nil());
            let sort_name = push_global_func_name(vm, func).unwrap_or_else(|| "sort".to_string());
            let table_idx = table_val.as_table_idx().ok_or_else(|| {
                runtime_error(
                    vm,
                    &format!("bad argument #1 to '{}' (table expected)", sort_name),
                )
            })?;
            let comp = args.get(1).copied().filter(|v| !v.is_nil());
            do_table_sort(vm, table_idx, comp)?;
            Ok(vec![])
        } else if vm.table_move_idx == Some(native_idx) {
            do_table_move(vm, args)
        } else if vm.string_gsub_idx == Some(native_idx) {
            // string.gsub(s, pattern, repl [, n])
            let s_val = args.first().copied().unwrap_or(TValue::nil());
            let s_sid = s_val.as_string_id().ok_or_else(|| {
                LuaError::Runtime("bad argument #1 to 'gsub' (string expected)".to_string())
            })?;
            let subject = vm.strings.get_bytes(s_sid).to_vec();
            let p_val = args.get(1).copied().unwrap_or(TValue::nil());
            let p_sid = p_val.as_string_id().ok_or_else(|| {
                LuaError::Runtime("bad argument #2 to 'gsub' (string expected)".to_string())
            })?;
            let pat = vm.strings.get_bytes(p_sid).to_vec();
            let repl = args.get(2).copied().unwrap_or(TValue::nil());
            let max_n = args.get(3).and_then(|v| v.as_full_integer(&vm.gc));
            let (result_bytes, count) = do_string_gsub(vm, &subject, &pat, repl, max_n)?;
            let result_sid = vm.strings.intern_or_create(&result_bytes);
            Ok(vec![
                TValue::from_string_id(result_sid),
                TValue::from_full_integer(count, &mut vm.gc),
            ])
        } else if vm.coro_resume_idx == Some(native_idx) {
            do_coroutine_resume(vm, args)
        } else if vm.coro_yield_idx == Some(native_idx) {
            if vm.running_coro.is_none() {
                Err(runtime_error(
                    vm,
                    "attempt to yield from outside a coroutine",
                ))
            } else {
                Err(LuaError::Yield(args.to_vec()))
            }
        } else if vm.coro_wrap_idx == Some(native_idx) {
            // coroutine.wrap(f): create handle + wrapper with __call
            let func = args.first().copied().unwrap_or(TValue::nil());
            if !func.is_function() {
                return Err(LuaError::Runtime(
                    "bad argument #1 to 'wrap' (function expected)".to_string(),
                ));
            }
            // Create coroutine handle
            let handle = vm.gc.alloc_table(4, 0);
            vm.gc
                .get_table_mut(handle)
                .raw_seti(1, TValue::from_integer(-1));
            vm.gc.get_table_mut(handle).raw_seti(2, func);
            let suspended_sid = vm.strings.intern(b"suspended");
            vm.gc
                .get_table_mut(handle)
                .raw_seti(3, TValue::from_string_id(suspended_sid));
            // Set thread metatable so type() returns "thread"
            vm.gc.get_table_mut(handle).metatable = vm.gc.thread_metatable;
            // Create wrapper table with __call metamethod
            let wrapper = vm.gc.alloc_table(4, 4);
            vm.gc
                .get_table_mut(wrapper)
                .raw_seti(1, TValue::from_table(handle));
            // Set metatable with __call = wrap_resume
            let mt = vm.gc.alloc_table(0, 4);
            let call_name = vm.strings.intern(b"__call");
            let wrap_resume_idx = vm.coro_wrap_resume_idx.unwrap();
            let wrap_resume_val = TValue::from_native(wrap_resume_idx);
            vm.gc
                .get_table_mut(mt)
                .raw_set_str(call_name, wrap_resume_val);
            vm.gc.get_table_mut(wrapper).metatable = Some(mt);
            Ok(vec![TValue::from_table(wrapper)])
        } else if vm.coro_wrap_resume_idx == Some(native_idx) {
            do_coroutine_wrap_resume(vm, args)
        } else if vm.collectgarbage_idx == Some(native_idx) {
            do_collectgarbage(vm, args)
        } else if vm.tostring_idx == Some(native_idx) {
            do_tostring(vm, args)
        } else if vm.load_idx == Some(native_idx) {
            do_load(vm, args)
        } else if vm.dofile_idx == Some(native_idx) {
            do_dofile(vm, args)
        } else if vm.loadfile_idx == Some(native_idx) {
            do_loadfile(vm, args)
        } else if vm.require_idx == Some(native_idx) {
            do_require(vm, args)
        } else if vm.error_idx == Some(native_idx) {
            do_error(vm, args)
        } else if vm.debug_getupvalue_idx == Some(native_idx) {
            do_debug_getupvalue(vm, args)
        } else if vm.debug_setupvalue_idx == Some(native_idx) {
            do_debug_setupvalue(vm, args)
        } else if vm.debug_getinfo_idx == Some(native_idx) {
            do_debug_getinfo(vm, args)
        } else if vm.debug_traceback_idx == Some(native_idx) {
            do_debug_traceback(vm, args)
        } else if vm.debug_sethook_idx == Some(native_idx) {
            do_debug_sethook(vm, args)
        } else if vm.debug_gethook_idx == Some(native_idx) {
            do_debug_gethook(vm, args)
        } else if vm.debug_getlocal_idx == Some(native_idx) {
            do_debug_getlocal(vm, args)
        } else if vm.debug_setlocal_idx == Some(native_idx) {
            do_debug_setlocal(vm, args)
        } else if vm.debug_getregistry_idx == Some(native_idx) {
            do_debug_getregistry(vm)
        } else if vm.coro_running_idx == Some(native_idx) {
            do_coro_running(vm)
        } else if vm.coro_isyieldable_idx == Some(native_idx) {
            do_coro_isyieldable(vm, args)
        } else if vm.coro_close_idx == Some(native_idx) {
            do_coro_close(vm, args)
        } else if vm.string_format_idx == Some(native_idx) {
            do_string_format(vm, args)
        } else if vm.string_dump_idx == Some(native_idx) {
            do_string_dump(vm, args)
        } else if vm.pairs_idx == Some(native_idx) {
            do_pairs(vm, args)
        } else if vm.ipairs_iter_idx == Some(native_idx) {
            do_ipairs_iter(vm, args)
        } else if vm.table_insert_idx == Some(native_idx) {
            do_table_insert(vm, args)
        } else if vm.table_remove_idx == Some(native_idx) {
            do_table_remove(vm, args)
        } else if vm.table_concat_idx == Some(native_idx) {
            do_table_concat(vm, args)
        } else if vm.table_unpack_idx == Some(native_idx) {
            do_table_unpack(vm, args)
        } else if vm.warn_idx == Some(native_idx) {
            do_warn(vm, args)
        } else {
            // Normal native function call
            let native_ref = vm.gc.get_native(native_idx);
            let native_fn = native_ref.func;
            let native_upvalue = native_ref.upvalue;
            let args_vec = args.to_vec();
            let mut ctx = NativeContext {
                args: &args_vec,
                gc: &mut vm.gc,
                strings: &mut vm.strings,
                upvalue: native_upvalue,
            };
            match native_fn(&mut ctx) {
                Ok(r) => Ok(r),
                Err(e) => {
                    let mut err = map_native_error(e);
                    err = qualify_func_name_in_error(
                        vm,
                        vm.call_stack.len().saturating_sub(1),
                        func,
                        err,
                    );
                    Err(add_error_prefix(vm, err))
                }
            }
        }
    } else {
        // __call should have been resolved by call_function wrapper
        Err(LuaError::Runtime(format!(
            "attempt to call a {} value",
            obj_type_name(func, vm)
        )))
    }
}

/// Handle `collectgarbage(opt [, arg])` with full VM access.
fn do_collectgarbage(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    // Default option is "collect"
    let opt = if let Some(val) = args.first() {
        if let Some(sid) = val.as_string_id() {
            String::from_utf8_lossy(vm.strings.get_bytes(sid)).into_owned()
        } else if val.is_nil() {
            "collect".to_string()
        } else {
            return Err(LuaError::Runtime(
                "bad argument #1 to 'collectgarbage' (string expected)".to_string(),
            ));
        }
    } else {
        "collect".to_string()
    };

    match opt.as_str() {
        "collect" => {
            if vm.in_gc {
                // GC is not reentrant — return false to indicate no collection happened
                Ok(vec![TValue::from_bool(false)])
            } else {
                vm.gc_collect();
                Ok(vec![TValue::from_integer(0)])
            }
        }
        "count" => {
            let kb = vm.gc.gc_memory_kb();
            let bytes_frac = (vm.gc.gc_memory_bytes() % 1024) as f64;
            Ok(vec![TValue::from_float(kb), TValue::from_float(bytes_frac)])
        }
        "stop" => {
            vm.gc.gc_state.enabled = false;
            Ok(vec![TValue::from_integer(0)])
        }
        "restart" => {
            vm.gc.gc_state.enabled = true;
            Ok(vec![TValue::from_integer(0)])
        }
        "step" => {
            if vm.in_gc {
                Ok(vec![TValue::from_bool(false)])
            } else {
                vm.gc_collect();
                Ok(vec![TValue::from_bool(true)])
            }
        }
        "isrunning" => Ok(vec![TValue::from_bool(vm.gc.gc_state.enabled)]),
        "setpause" => {
            let old = vm.gc.gc_state.pause;
            if let Some(arg) = args.get(1) {
                if let Some(n) = arg.as_integer() {
                    vm.gc.gc_state.pause = n as u32;
                } else if let Some(f) = arg.as_float() {
                    vm.gc.gc_state.pause = f as u32;
                }
            }
            Ok(vec![TValue::from_integer(old as i64)])
        }
        "setstepmul" => {
            let old = vm.gc.gc_state.step_mul;
            if let Some(arg) = args.get(1) {
                if let Some(n) = arg.as_integer() {
                    vm.gc.gc_state.step_mul = n as u32;
                } else if let Some(f) = arg.as_float() {
                    vm.gc.gc_state.step_mul = f as u32;
                }
            }
            Ok(vec![TValue::from_integer(old as i64)])
        }
        "incremental" => {
            let old_mode = vm.gc.gc_state.gc_mode;
            vm.gc.gc_state.gc_mode = 0;
            let mode_str = if old_mode == 1 {
                "generational"
            } else {
                "incremental"
            };
            let sid = vm.strings.intern(mode_str.as_bytes());
            Ok(vec![TValue::from_string_id(sid)])
        }
        "generational" => {
            let old_mode = vm.gc.gc_state.gc_mode;
            vm.gc.gc_state.gc_mode = 1;
            let mode_str = if old_mode == 1 {
                "generational"
            } else {
                "incremental"
            };
            let sid = vm.strings.intern(mode_str.as_bytes());
            Ok(vec![TValue::from_string_id(sid)])
        }
        _ => Err(LuaError::Runtime(format!(
            "bad argument #1 to 'collectgarbage' (invalid option '{opt}')"
        ))),
    }
}

/// Handle `tostring(val)` with full VM access for __tostring metamethod.
fn do_tostring(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    if args.is_empty() {
        return Err(LuaError::Runtime(
            "bad argument #1 to 'tostring' (value expected)".to_string(),
        ));
    }
    let val = args[0];
    // Check for __tostring metamethod
    let mm_name = vm.mm_names.as_ref().unwrap().tostring;
    if let Some(mm) = crate::metamethod::get_metamethod(val, mm_name, &vm.gc) {
        let results = call_function(vm, mm, &[val])?;
        let result = results.first().copied().unwrap_or(TValue::nil());
        // Lua 5.4: __tostring must return a string
        if !result.is_string() {
            return Err(LuaError::Runtime(
                "'__tostring' must return a string".to_string(),
            ));
        }
        Ok(vec![result])
    } else {
        // Check for __name in metatable (type name override)
        let mt = if let Some(tbl_idx) = val.as_table_idx() {
            vm.gc.get_table(tbl_idx).metatable
        } else if let Some(ud_idx) = val.as_userdata_idx() {
            vm.gc.get_userdata(ud_idx).metatable
        } else {
            None
        };
        if let Some(mt_idx) = mt {
            let name_key = vm.strings.intern(b"__name");
            let name_val = vm.gc.get_table(mt_idx).raw_get_str(name_key);
            if let Some(name_sid) = name_val.as_string_id() {
                let name_bytes = vm.strings.get_bytes(name_sid).to_vec();
                let ptr = val.gc_index().unwrap_or(0);
                let s = format!("{}: 0x{:x}", String::from_utf8_lossy(&name_bytes), ptr);
                let sid = vm.strings.intern_or_create(s.as_bytes());
                return Ok(vec![TValue::from_string_id(sid)]);
            }
        }
        // Default tostring behavior
        let s = crate::vm::format_value(val, &vm.gc, &vm.strings);
        let sid = vm.strings.intern_or_create(s.as_bytes());
        Ok(vec![TValue::from_string_id(sid)])
    }
}

/// Handle `load(chunk [, chunkname [, mode [, env]]])`.
/// If chunk is a string, compile it. If it's a function, call it repeatedly to build source.
/// Returns the compiled function on success, or (nil, errmsg) on failure.
fn do_load(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    let chunk = args.first().copied().unwrap_or(TValue::nil());
    let chunkname = args.get(1).copied().unwrap_or(TValue::nil());
    let mode = args.get(2).copied().unwrap_or(TValue::nil());
    let env = args.get(3).copied();

    // Parse mode string (default "bt" = both binary and text)
    let mode_str = if let Some(sid) = mode.as_string_id() {
        String::from_utf8_lossy(vm.strings.get_bytes(sid)).into_owned()
    } else {
        "bt".to_string()
    };

    // Get chunk name
    let name = if let Some(sid) = chunkname.as_string_id() {
        String::from_utf8_lossy(vm.strings.get_bytes(sid)).into_owned()
    } else if let Some(sid) = chunk.as_string_id() {
        // Use the source string itself (Lua 5.4 behavior: source becomes [string "..."])
        String::from_utf8_lossy(vm.strings.get_bytes(sid)).into_owned()
    } else {
        "=(load)".to_string()
    };

    // Get source bytes
    let source = if let Some(sid) = chunk.as_string_id() {
        vm.strings.get_bytes(sid).to_vec()
    } else if chunk.is_function() {
        // Function reader: call chunk() repeatedly, concatenate results
        let mut parts = Vec::new();
        loop {
            let result = match call_function(vm, chunk, &[]) {
                Ok(r) => r,
                Err(e) => {
                    let err_val = e.to_tvalue(&mut vm.strings);
                    let msg_str = if let Some(sid) = err_val.as_string_id() {
                        String::from_utf8_lossy(vm.strings.get_bytes(sid)).into_owned()
                    } else {
                        format!("{:?}", e)
                    };
                    let msg = vm.strings.intern_or_create(msg_str.as_bytes());
                    return Ok(vec![TValue::nil(), TValue::from_string_id(msg)]);
                }
            };
            let part = result.first().copied().unwrap_or(TValue::nil());
            if part.is_nil() {
                break;
            }
            if let Some(sid) = part.as_string_id() {
                let bytes = vm.strings.get_bytes(sid).to_vec();
                if bytes.is_empty() {
                    break;
                }
                parts.extend_from_slice(&bytes);
            } else {
                let msg = vm
                    .strings
                    .intern_or_create(b"reader function must return a string");
                return Ok(vec![TValue::nil(), TValue::from_string_id(msg)]);
            }
        }
        parts
    } else {
        let tname = obj_type_name(chunk, vm);
        let msg = vm.strings.intern_or_create(
            format!("bad argument #1 to 'load' (value expected, got {})", tname).as_bytes(),
        );
        return Ok(vec![TValue::nil(), TValue::from_string_id(msg)]);
    };

    // Check mode against actual source content
    let is_binary = source.first() == Some(&0x1b); // Lua binary signature starts with \x1b
    if is_binary && !mode_str.contains('b') {
        let name_prefix = if name.starts_with('=') || name.starts_with('@') {
            &name[1..]
        } else {
            &name
        };
        let msg_str = format!(
            "{}:  attempt to load a binary chunk (mode is '{}')",
            name_prefix, mode_str
        );
        let msg = vm.strings.intern_or_create(msg_str.as_bytes());
        return Ok(vec![TValue::nil(), TValue::from_string_id(msg)]);
    }
    if !is_binary && !mode_str.contains('t') {
        let name_prefix = if name.starts_with('=') || name.starts_with('@') {
            &name[1..]
        } else {
            &name
        };
        let msg_str = format!(
            "{}:  attempt to load a text chunk (mode is '{}')",
            name_prefix, mode_str
        );
        let msg = vm.strings.intern_or_create(msg_str.as_bytes());
        return Ok(vec![TValue::nil(), TValue::from_string_id(msg)]);
    }

    // Compile
    if is_binary {
        // Try to load binary chunk
        match vm.load_binary_chunk(&source, &name, env) {
            Ok(closure_val) => Ok(vec![closure_val]),
            Err(err_msg) => {
                let msg = vm.strings.intern_or_create(err_msg.as_bytes());
                Ok(vec![TValue::nil(), TValue::from_string_id(msg)])
            }
        }
    } else {
        match vm.load_chunk(&source, &name, env) {
            Ok(closure_val) => Ok(vec![closure_val]),
            Err(err_msg) => {
                let msg = vm.strings.intern_or_create(err_msg.as_bytes());
                Ok(vec![TValue::nil(), TValue::from_string_id(msg)])
            }
        }
    }
}

/// Handle `dofile([filename])`.
/// Reads file, compiles it, and executes it. Returns the chunk's results.
fn do_dofile(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    let filename = args.first().copied().unwrap_or(TValue::nil());

    let source = if filename.is_nil() {
        // Read from stdin
        use std::io::Read;
        let mut buf = Vec::new();
        std::io::stdin()
            .read_to_end(&mut buf)
            .map_err(|e| LuaError::Runtime(format!("cannot read stdin: {e}")))?;
        buf
    } else {
        let sid = filename.as_string_id().ok_or_else(|| {
            LuaError::Runtime("bad argument #1 to 'dofile' (string expected)".to_string())
        })?;
        let path = String::from_utf8_lossy(vm.strings.get_bytes(sid)).into_owned();
        std::fs::read(&path).map_err(|e| LuaError::Runtime(format!("cannot open {path}: {e}")))?
    };

    let name = if let Some(sid) = filename.as_string_id() {
        let path_str = String::from_utf8_lossy(vm.strings.get_bytes(sid)).into_owned();
        format!("@{path_str}")
    } else {
        "=stdin".to_string()
    };

    // Replace BOM and shebang with whitespace to preserve line numbers
    let mut compile_source = source;
    {
        let mut pos = 0;
        if compile_source.starts_with(b"\xEF\xBB\xBF") {
            compile_source[0] = b' ';
            compile_source[1] = b' ';
            compile_source[2] = b' ';
            pos = 3;
        }
        if pos < compile_source.len() && compile_source[pos] == b'#' {
            while pos < compile_source.len() && compile_source[pos] != b'\n' {
                compile_source[pos] = b' ';
                pos += 1;
            }
        }
    }

    let closure_val = vm
        .load_chunk(&compile_source, &name, None)
        .map_err(LuaError::Runtime)?;

    // Execute the loaded chunk
    call_function(vm, closure_val, &[])
}

/// Handle `loadfile([filename [, mode [, env]]])`.
/// Reads file, compiles it, returns the function (does not execute).
fn do_loadfile(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    let filename = args.first().copied().unwrap_or(TValue::nil());
    let mode = args.get(1).copied().unwrap_or(TValue::nil());
    let env = args.get(2).copied();

    // Parse mode string
    let mode_str = if let Some(sid) = mode.as_string_id() {
        String::from_utf8_lossy(vm.strings.get_bytes(sid)).into_owned()
    } else {
        "bt".to_string() // default: both binary and text
    };

    let mut source = if filename.is_nil() {
        use std::io::Read;
        let mut buf = Vec::new();
        std::io::stdin()
            .read_to_end(&mut buf)
            .map_err(|e| LuaError::Runtime(format!("cannot read stdin: {e}")))?;
        buf
    } else {
        let sid = filename.as_string_id().ok_or_else(|| {
            LuaError::Runtime("bad argument #1 to 'loadfile' (string expected)".to_string())
        })?;
        let path = String::from_utf8_lossy(vm.strings.get_bytes(sid)).into_owned();
        match std::fs::read(&path) {
            Ok(data) => data,
            Err(e) => {
                let msg = vm
                    .strings
                    .intern_or_create(format!("cannot open {path}: {e}").as_bytes());
                return Ok(vec![TValue::nil(), TValue::from_string_id(msg)]);
            }
        }
    };

    // Check mode vs source type (skip BOM/shebang for binary detection)
    let mut skip = 0;
    if source.starts_with(b"\xEF\xBB\xBF") {
        skip = 3;
    }
    if skip < source.len() && source[skip] == b'#' {
        while skip < source.len() && source[skip] != b'\n' {
            skip += 1;
        }
        if skip < source.len() {
            skip += 1;
        }
    }
    let is_binary = !source[skip..].is_empty() && source[skip] == 0x1b;
    if is_binary && !mode_str.contains('b') {
        let msg = vm
            .strings
            .intern_or_create(b"attempt to load a binary chunk (mode is 't')");
        return Ok(vec![TValue::nil(), TValue::from_string_id(msg)]);
    }
    if !is_binary && !mode_str.contains('t') {
        let msg = vm
            .strings
            .intern_or_create(b"attempt to load a text chunk (mode is 'b')");
        return Ok(vec![TValue::nil(), TValue::from_string_id(msg)]);
    }

    let name = if let Some(sid) = filename.as_string_id() {
        let path_str = String::from_utf8_lossy(vm.strings.get_bytes(sid)).into_owned();
        format!("@{path_str}")
    } else {
        "=stdin".to_string()
    };

    // For text chunks: replace BOM and shebang with whitespace to preserve line numbers
    // For binary chunks: strip BOM/shebang prefix (binary doesn't need line numbers)
    let compile_source: &[u8] = if is_binary {
        &source[skip..]
    } else {
        let mut pos = 0;
        if source.starts_with(b"\xEF\xBB\xBF") {
            source[0] = b' ';
            source[1] = b' ';
            source[2] = b' ';
            pos = 3;
        }
        if pos < source.len() && source[pos] == b'#' {
            while pos < source.len() && source[pos] != b'\n' {
                source[pos] = b' ';
                pos += 1;
            }
        }
        &source
    };

    match vm.load_chunk(compile_source, &name, env) {
        Ok(closure_val) => Ok(vec![closure_val]),
        Err(err_msg) => {
            let msg = vm.strings.intern_or_create(err_msg.as_bytes());
            Ok(vec![TValue::nil(), TValue::from_string_id(msg)])
        }
    }
}

/// Handle `require(modname)`.
/// Checks package.loaded, package.preload, then searches package.path for Lua files.
fn do_require(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    let modname_val = args.first().copied().unwrap_or(TValue::nil());
    let modname_sid = modname_val.as_string_id().ok_or_else(|| {
        LuaError::Runtime("bad argument #1 to 'require' (string expected)".to_string())
    })?;
    let modname = String::from_utf8_lossy(vm.strings.get_bytes(modname_sid)).into_owned();

    // 1. Check package.loaded[modname]
    let loaded_idx = vm
        .package_loaded_idx
        .ok_or_else(|| LuaError::Runtime("package.loaded not initialized".to_string()))?;
    let cached = vm.gc.get_table(loaded_idx).raw_get_str(modname_sid);
    if !cached.is_nil() {
        return Ok(vec![cached]);
    }

    // 2. Check package.preload[modname]
    let preload_idx = vm
        .package_preload_idx
        .ok_or_else(|| LuaError::Runtime("package.preload not initialized".to_string()))?;
    let preload_func = vm.gc.get_table(preload_idx).raw_get_str(modname_sid);
    if !preload_func.is_nil() {
        // Set package.loaded[modname] = true (sentinel to prevent circular require)
        vm.gc
            .get_table_mut(loaded_idx)
            .raw_set_str(modname_sid, TValue::from_bool(true));

        // Call the preload function with modname as argument
        let result = call_function(vm, preload_func, &[modname_val])?;
        let module = result.first().copied().unwrap_or(TValue::nil());

        // If the loader returned a non-nil value, store it in package.loaded
        if !module.is_nil() {
            vm.gc
                .get_table_mut(loaded_idx)
                .raw_set_str(modname_sid, module);
            return Ok(vec![module]);
        }

        // Otherwise check if the loader set package.loaded[modname] to something
        let final_val = vm.gc.get_table(loaded_idx).raw_get_str(modname_sid);
        return Ok(vec![final_val]);
    }

    // 3. Search for a Lua file using package.path
    let env_idx = vm
        .env_idx
        .ok_or_else(|| LuaError::Runtime("_ENV not available".to_string()))?;
    let pkg_key = vm.strings.intern(b"package");
    let pkg_tval = vm.gc.get_table(env_idx).raw_get_str(pkg_key);
    let pkg_table_idx = pkg_tval
        .as_table_idx()
        .ok_or_else(|| LuaError::Runtime("package table not found".to_string()))?;
    let path_key = vm.strings.intern(b"path");
    let path_val = vm.gc.get_table(pkg_table_idx).raw_get_str(path_key);
    let path_str = if let Some(sid) = path_val.as_string_id() {
        String::from_utf8_lossy(vm.strings.get_bytes(sid)).into_owned()
    } else {
        return Err(LuaError::Runtime(
            "'package.path' must be a string".to_string(),
        ));
    };

    if let Some(filepath) = selune_stdlib::package_lib::search_lua_file(&modname, &path_str) {
        // Set package.loaded[modname] = true (sentinel to prevent circular require)
        vm.gc
            .get_table_mut(loaded_idx)
            .raw_set_str(modname_sid, TValue::from_bool(true));

        // Read and compile the file
        let source = std::fs::read(&filepath)
            .map_err(|e| LuaError::Runtime(format!("cannot open {}: {}", filepath, e)))?;
        let name = format!("@{}", filepath);
        let closure_val = vm.load_chunk(&source, &name, None).map_err(|e| {
            LuaError::Runtime(format!(
                "error loading module '{}' from file '{}':\n\t{}",
                modname, filepath, e
            ))
        })?;

        // Execute the loaded chunk with modname and filepath as arguments
        let filepath_sid = vm.strings.intern_or_create(filepath.as_bytes());
        let filepath_val = TValue::from_string_id(filepath_sid);
        let result = call_function(vm, closure_val, &[modname_val, filepath_val])?;
        let module = result.first().copied().unwrap_or(TValue::nil());

        // If the loader returned a non-nil value, store it in package.loaded
        if !module.is_nil() {
            vm.gc
                .get_table_mut(loaded_idx)
                .raw_set_str(modname_sid, module);
            return Ok(vec![module]);
        }

        // Check if the module set package.loaded[modname] itself
        let final_val = vm.gc.get_table(loaded_idx).raw_get_str(modname_sid);
        return Ok(vec![final_val]);
    }

    // 4. Module not found - build error message
    let modname_path = modname.replace('.', "/");
    let mut tried = String::new();

    // First: preload check
    tried.push_str(&format!("\n\tno field package.preload['{}']", modname));

    // Then: package.path entries
    for template in path_str.split(';') {
        let filepath = template.replace('?', &modname_path);
        tried.push_str(&format!("\n\tno file '{}'", filepath));
    }

    // Then: package.cpath entries
    let cpath_key = vm.strings.intern(b"cpath");
    let cpath_val = vm.gc.get_table(pkg_table_idx).raw_get_str(cpath_key);
    if let Some(cpath_sid) = cpath_val.as_string_id() {
        let cpath_str = String::from_utf8_lossy(vm.strings.get_bytes(cpath_sid)).into_owned();
        for template in cpath_str.split(';') {
            if !template.is_empty() {
                let filepath = template.replace('?', &modname_path);
                tried.push_str(&format!("\n\tno file '{}'", filepath));
            }
        }
    }

    Err(LuaError::Runtime(format!(
        "module '{}' not found:{}",
        modname, tried
    )))
}

/// Handle `error(msg [, level])`.
/// Raises an error with the given message, optionally adding source:line prefix.
fn do_error(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    let msg = args.first().copied().unwrap_or(TValue::nil());
    let _level = args
        .get(1)
        .and_then(|v| v.as_full_integer(&vm.gc))
        .unwrap_or(1);

    // If msg is a string and level > 0, add source:line prefix
    if let Some(sid) = msg.as_string_id() {
        let s = String::from_utf8_lossy(vm.strings.get_bytes(sid)).into_owned();
        if _level > 0 {
            let prefix = get_error_prefix(vm, (_level - 1) as usize);
            let full = format!("{}{}", prefix, s);
            Err(LuaError::Runtime(full))
        } else {
            Err(LuaError::Runtime(s))
        }
    } else {
        // Non-string errors are raised as-is (no prefix)
        Err(LuaError::LuaValue(msg))
    }
}

/// Handle `debug.getupvalue(f, up)`.
/// Returns name, value for upvalue #up of function f, or nil if out of range.
/// Needs VM access to look up upvalue names from Proto.
fn do_debug_getupvalue(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    let func = args.first().copied().unwrap_or(TValue::nil());
    let n_val = args.get(1).copied().unwrap_or(TValue::nil());
    let n = n_val.as_full_integer(&vm.gc).unwrap_or(0) as usize;

    if let Some(cl_idx) = func.as_closure_idx() {
        let closure = vm.gc.get_closure(cl_idx);
        if n < 1 || n > closure.upvalues.len() {
            return Ok(vec![TValue::nil()]);
        }
        let idx = n - 1;
        let proto_idx = closure.proto_idx;
        let uv_gc_idx = closure.upvalues[idx];

        // Get upvalue name from proto
        let name = if proto_idx < vm.protos.len() {
            let proto = &vm.protos[proto_idx];
            if idx < proto.upvalues.len() {
                proto.upvalues[idx].name.map(|sid| {
                    let bytes = vm.strings.get_bytes(sid);
                    String::from_utf8_lossy(bytes).into_owned()
                })
            } else {
                None
            }
        } else {
            None
        };
        let name_str = name.unwrap_or_else(|| "(no name)".to_string());

        // Get upvalue value
        let uv = vm.gc.get_upval(uv_gc_idx);
        let val = match uv.location {
            selune_core::gc::UpValLocation::Closed(v) => v,
            selune_core::gc::UpValLocation::Open(stack_idx) => vm.stack[stack_idx],
            selune_core::gc::UpValLocation::OpenInThread(_, _) => TValue::nil(),
        };

        let name_sid = vm.strings.intern_or_create(name_str.as_bytes());
        Ok(vec![TValue::from_string_id(name_sid), val])
    } else if let Some(native_idx) = func.as_native_idx() {
        // C/native functions: upvalue name is always "" (empty string)
        // Our natives have a single optional upvalue
        let native = vm.gc.get_native(native_idx);
        let uv = native.upvalue;
        if n == 1 && !uv.is_nil() {
            let empty = vm.strings.intern_or_create(b"");
            Ok(vec![TValue::from_string_id(empty), uv])
        } else {
            Ok(vec![TValue::nil()])
        }
    } else {
        Ok(vec![TValue::nil()])
    }
}

/// Handle `debug.setupvalue(f, up, value)`.
/// Sets upvalue #up of function f to value. Returns name or nil.
fn do_debug_setupvalue(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    let func = args.first().copied().unwrap_or(TValue::nil());
    let n_val = args.get(1).copied().unwrap_or(TValue::nil());
    let new_val = args.get(2).copied().unwrap_or(TValue::nil());
    let n = n_val.as_full_integer(&vm.gc).unwrap_or(0) as usize;

    if let Some(cl_idx) = func.as_closure_idx() {
        let closure = vm.gc.get_closure(cl_idx);
        if n < 1 || n > closure.upvalues.len() {
            return Ok(vec![TValue::nil()]);
        }
        let idx = n - 1;
        let proto_idx = closure.proto_idx;
        let uv_gc_idx = closure.upvalues[idx];

        // Get upvalue name from proto
        let name = if proto_idx < vm.protos.len() {
            let proto = &vm.protos[proto_idx];
            if idx < proto.upvalues.len() {
                proto.upvalues[idx].name.map(|sid| {
                    let bytes = vm.strings.get_bytes(sid);
                    String::from_utf8_lossy(bytes).into_owned()
                })
            } else {
                None
            }
        } else {
            None
        };
        let name_str = name.unwrap_or_else(|| "(no name)".to_string());

        // Set upvalue value
        let uv = vm.gc.get_upval_mut(uv_gc_idx);
        match &mut uv.location {
            selune_core::gc::UpValLocation::Closed(ref mut v) => *v = new_val,
            selune_core::gc::UpValLocation::Open(stack_idx) => {
                let si = *stack_idx;
                vm.stack[si] = new_val;
            }
            selune_core::gc::UpValLocation::OpenInThread(_, _) => {}
        }

        let name_sid = vm.strings.intern_or_create(name_str.as_bytes());
        Ok(vec![TValue::from_string_id(name_sid)])
    } else {
        Ok(vec![TValue::nil()])
    }
}

/// Handle `debug.getinfo(f [, what])` with full VM access.
/// Handle `table.move(a1, f, e, t [, a2])` with VM access for metamethods.
fn do_table_move(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    let a1_val = args.first().copied().unwrap_or(TValue::nil());
    let a1_idx = a1_val.as_table_idx().ok_or_else(|| {
        LuaError::Runtime("bad argument #1 to 'move' (table expected)".to_string())
    })?;

    let f = args
        .get(1)
        .copied()
        .unwrap_or(TValue::nil())
        .as_full_integer(&vm.gc)
        .ok_or_else(|| {
            LuaError::Runtime("bad argument #2 to 'move' (number expected)".to_string())
        })?;
    let e = args
        .get(2)
        .copied()
        .unwrap_or(TValue::nil())
        .as_full_integer(&vm.gc)
        .ok_or_else(|| {
            LuaError::Runtime("bad argument #3 to 'move' (number expected)".to_string())
        })?;
    let t = args
        .get(3)
        .copied()
        .unwrap_or(TValue::nil())
        .as_full_integer(&vm.gc)
        .ok_or_else(|| {
            LuaError::Runtime("bad argument #4 to 'move' (number expected)".to_string())
        })?;

    let a2_val = if let Some(v) = args.get(4) {
        if v.is_nil() {
            a1_val
        } else {
            *v
        }
    } else {
        a1_val
    };
    let a2_idx = a2_val.as_table_idx().ok_or_else(|| {
        LuaError::Runtime("bad argument #5 to 'move' (table expected)".to_string())
    })?;

    if f > e {
        return Ok(vec![a2_val]);
    }

    // PUC Lua checks: luaL_argcheck(L, f > 0 || e < LUA_MAXINTEGER + f, 3, "too many elements to move")
    if f <= 0 && e >= i64::MAX.wrapping_add(f) {
        return Err(LuaError::Runtime("too many elements to move".to_string()));
    }
    let n = (e as i128) - (f as i128) + 1; // number of elements
                                           // PUC Lua check: luaL_argcheck(L, t <= LUA_MAXINTEGER - n + 1, 4, "destination wrap around")
    let max_t = (i64::MAX as i128) - n + 1;
    if (t as i128) > max_t {
        return Err(LuaError::Runtime("destination wrap around".to_string()));
    }

    // Copy elements using metamethod-aware access (table_index/table_newindex)
    // Forward when non-overlapping or destination before source
    if t <= f || t > e || a1_idx != a2_idx {
        // Forward copy
        let mut i = f;
        loop {
            let key = TValue::from_full_integer(i, &mut vm.gc);
            let v = table_index(vm, a1_val, key)?;
            let dest_key = TValue::from_full_integer(t + (i - f), &mut vm.gc);
            table_newindex(vm, a2_val, dest_key, v)?;
            if i == e {
                break;
            }
            i += 1;
        }
    } else {
        // Backward copy (overlapping, destination after source)
        let mut i = e;
        loop {
            let key = TValue::from_full_integer(i, &mut vm.gc);
            let v = table_index(vm, a1_val, key)?;
            let dest_key = TValue::from_full_integer(t + (i - f), &mut vm.gc);
            table_newindex(vm, a2_val, dest_key, v)?;
            if i == f {
                break;
            }
            i -= 1;
        }
    }

    Ok(vec![a2_val])
}

/// Detect if the first argument is a thread (coroutine handle).
/// Returns Some(Some(coro_id)) if it is a thread with valid coro,
/// Some(None) if it is a thread but not yet allocated,
/// None if it is not a thread.
fn detect_thread_arg(vm: &Vm, arg: TValue) -> Option<Option<usize>> {
    let tbl_idx = arg.as_table_idx()?;
    let thread_mt = vm.gc.thread_metatable?;
    if vm.gc.get_table(tbl_idx).metatable == Some(thread_mt) {
        let id_val = vm.gc.get_table(tbl_idx).raw_geti(1);
        let cid = id_val.as_integer().unwrap_or(-2);
        if cid >= 0 {
            return Some(Some(cid as usize));
        }
        // Thread handle exists but coroutine not yet allocated (cid == -1)
        return Some(None);
    }
    None
}

fn do_debug_getinfo(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    // Detect optional thread argument: debug.getinfo([thread,] f [, what])
    let first = args.first().copied().unwrap_or(TValue::nil());
    let thread_info = detect_thread_arg(vm, first);
    let is_thread = thread_info.is_some();
    let coro_id = thread_info.flatten();
    let (arg1, what_arg) = if is_thread {
        (
            args.get(1).copied().unwrap_or(TValue::nil()),
            args.get(2).copied().unwrap_or(TValue::nil()),
        )
    } else {
        (first, args.get(1).copied().unwrap_or(TValue::nil()))
    };

    // Parse the 'what' filter string (default: all common fields)
    let what_str = if let Some(sid) = what_arg.as_string_id() {
        String::from_utf8_lossy(vm.strings.get_bytes(sid)).into_owned()
    } else {
        "flnStu".to_string()
    };

    // Validate what string — only valid characters allowed
    let valid_chars = b"SflnLurtpb>";
    let check_str = what_str.strip_prefix('>').unwrap_or(&what_str);
    for c in check_str.bytes() {
        if !valid_chars.contains(&c) {
            return Err(add_error_prefix(
                vm,
                LuaError::Runtime(format!(
                    "bad argument #2 to 'getinfo' (invalid option '{}')",
                    c as char
                )),
            ));
        }
    }

    let has_push = what_str.starts_with('>');

    // Determine if arg1 is a level (integer) or a function
    let tbl = vm.gc.alloc_table(0, 12);
    let mut queried_frame_idx: Option<usize> = None;
    // Track which call_stack we're querying for 'r', 't', 'n' flags
    let mut queried_coro: Option<usize> = None;

    if let Some(n) = arg1.as_full_integer(&vm.gc) {
        // ">" is invalid for level-based queries
        if has_push {
            return Err(add_error_prefix(
                vm,
                LuaError::Runtime("bad argument #2 to 'getinfo' (invalid option '>')".to_string()),
            ));
        }
        // Level-based query
        if n < 0 {
            return Ok(vec![TValue::nil()]);
        }
        let level = n as usize;

        if let Some(cid) = coro_id {
            // Querying a coroutine's call stack
            if cid >= vm.coroutines.len() {
                return Ok(vec![TValue::nil()]);
            }
            if level == 0 {
                // Level 0 for coroutine = the yield point (C function)
                fill_native_info(vm, tbl, None);
                return Ok(vec![TValue::from_table(tbl)]);
            }
            let coro_stack_len = vm.coroutines[cid].call_stack.len();
            if level > coro_stack_len {
                return Ok(vec![TValue::nil()]);
            }
            let frame_idx = coro_stack_len - level;
            queried_frame_idx = Some(frame_idx);
            queried_coro = Some(cid);

            let frame = &vm.coroutines[cid].call_stack[frame_idx];
            if !frame.is_lua() {
                let fsi = frame.func_stack_idx;
                let func_val_for_info = vm.coroutines[cid]
                    .stack
                    .get(fsi)
                    .copied()
                    .unwrap_or(TValue::nil());
                fill_native_info(vm, tbl, func_val_for_info.as_native_idx());
                if what_str.contains('f') {
                    let func_val = vm.coroutines[cid]
                        .stack
                        .get(fsi)
                        .copied()
                        .unwrap_or(TValue::nil());
                    if !func_val.is_nil() {
                        let func_key = vm.strings.intern(b"func");
                        vm.gc.get_table_mut(tbl).raw_set_str(func_key, func_val);
                    }
                }
                let what_check = what_str.strip_prefix('>').unwrap_or(&what_str);
                if what_check.contains('r') {
                    let frame = &vm.coroutines[cid].call_stack[frame_idx];
                    let ft_key = vm.strings.intern(b"ftransfer");
                    let nt_key = vm.strings.intern(b"ntransfer");
                    vm.gc
                        .get_table_mut(tbl)
                        .raw_set_str(ft_key, TValue::from_integer(frame.ftransfer as i64));
                    vm.gc
                        .get_table_mut(tbl)
                        .raw_set_str(nt_key, TValue::from_integer(frame.ntransfer as i64));
                }
                if what_check.contains('t') {
                    let frame = &vm.coroutines[cid].call_stack[frame_idx];
                    let tc_key = vm.strings.intern(b"istailcall");
                    vm.gc
                        .get_table_mut(tbl)
                        .raw_set_str(tc_key, TValue::from_bool(frame.is_tail_call()));
                }
                return Ok(vec![TValue::from_table(tbl)]);
            }

            let frame = &vm.coroutines[cid].call_stack[frame_idx];
            let proto_idx = frame.proto_idx;
            let pc = if frame.pc > 0 { frame.pc - 1 } else { 0 };
            let func_val = frame.closure_idx.map(TValue::from_closure);

            fill_lua_info(vm, tbl, proto_idx, Some(pc), func_val, &what_str);

            // 'n' — function name from caller's context (use coroutine's call stack)
            if what_str.contains('n') {
                let coro_cs = vm.coroutines[cid].call_stack.clone();
                fill_func_name_from_stack(vm, tbl, frame_idx, &coro_cs);
            }
        } else {
            // Querying the current thread
            if level == 0 {
                // Level 0 = getinfo itself (C function)
                fill_native_info(vm, tbl, None);
                return Ok(vec![TValue::from_table(tbl)]);
            }
            // call_stack[last] = the Lua frame that called getinfo (level 1)
            let stack_len = vm.call_stack.len();
            if level > stack_len {
                return Ok(vec![TValue::nil()]);
            }
            let frame_idx = stack_len - level;
            queried_frame_idx = Some(frame_idx);

            if !vm.call_stack[frame_idx].is_lua() {
                let fsi = vm.call_stack[frame_idx].func_stack_idx;
                let func_val_for_info = vm.stack.get(fsi).copied().unwrap_or(TValue::nil());
                fill_native_info(vm, tbl, func_val_for_info.as_native_idx());
                // Set func field for 'f' flag
                if what_str.contains('f') {
                    let func_val = vm.stack.get(fsi).copied().unwrap_or(TValue::nil());
                    if !func_val.is_nil() {
                        let func_key = vm.strings.intern(b"func");
                        vm.gc.get_table_mut(tbl).raw_set_str(func_key, func_val);
                    }
                }
                // 'r' — ftransfer/ntransfer
                let what_check = what_str.strip_prefix('>').unwrap_or(&what_str);
                if what_check.contains('r') {
                    let frame = &vm.call_stack[frame_idx];
                    let ft_key = vm.strings.intern(b"ftransfer");
                    let nt_key = vm.strings.intern(b"ntransfer");
                    vm.gc
                        .get_table_mut(tbl)
                        .raw_set_str(ft_key, TValue::from_integer(frame.ftransfer as i64));
                    vm.gc
                        .get_table_mut(tbl)
                        .raw_set_str(nt_key, TValue::from_integer(frame.ntransfer as i64));
                }
                // 't' — istailcall
                if what_check.contains('t') {
                    let frame = &vm.call_stack[frame_idx];
                    let tc_key = vm.strings.intern(b"istailcall");
                    vm.gc
                        .get_table_mut(tbl)
                        .raw_set_str(tc_key, TValue::from_bool(frame.is_tail_call()));
                }
                // 'n' — function name from caller's context (works for C functions too)
                if what_check.contains('n') {
                    fill_func_name(vm, tbl, frame_idx);
                }
                return Ok(vec![TValue::from_table(tbl)]);
            }

            let frame = &vm.call_stack[frame_idx];
            let proto_idx = frame.proto_idx;
            let pc = if frame.pc > 0 { frame.pc - 1 } else { 0 };
            let func_val = frame.closure_idx.map(TValue::from_closure);

            fill_lua_info(vm, tbl, proto_idx, Some(pc), func_val, &what_str);

            // 'n' — function name from caller's context
            if what_str.contains('n') {
                fill_func_name(vm, tbl, frame_idx);
            }
        }
    } else if let Some(cl_idx) = arg1.as_closure_idx() {
        // Function object query
        let proto_idx = vm.gc.get_closure(cl_idx).proto_idx;
        fill_lua_info(vm, tbl, proto_idx, None, Some(arg1), &what_str);
    } else if arg1.as_native_idx().is_some() {
        fill_native_info(vm, tbl, arg1.as_native_idx());
    } else {
        return Ok(vec![TValue::nil()]);
    }

    // 'r' — ftransfer/ntransfer (transfer info) and 't' — istailcall
    if let Some(fi) = queried_frame_idx {
        let what_check = what_str.strip_prefix('>').unwrap_or(&what_str);
        if let Some(cid) = queried_coro {
            if what_check.contains('r') {
                let frame = &vm.coroutines[cid].call_stack[fi];
                let ft_key = vm.strings.intern(b"ftransfer");
                let nt_key = vm.strings.intern(b"ntransfer");
                vm.gc
                    .get_table_mut(tbl)
                    .raw_set_str(ft_key, TValue::from_integer(frame.ftransfer as i64));
                vm.gc
                    .get_table_mut(tbl)
                    .raw_set_str(nt_key, TValue::from_integer(frame.ntransfer as i64));
            }
            if what_check.contains('t') {
                let frame = &vm.coroutines[cid].call_stack[fi];
                let tc_key = vm.strings.intern(b"istailcall");
                vm.gc
                    .get_table_mut(tbl)
                    .raw_set_str(tc_key, TValue::from_bool(frame.is_tail_call()));
            }
        } else {
            if what_check.contains('r') {
                let frame = &vm.call_stack[fi];
                let ft_key = vm.strings.intern(b"ftransfer");
                let nt_key = vm.strings.intern(b"ntransfer");
                vm.gc
                    .get_table_mut(tbl)
                    .raw_set_str(ft_key, TValue::from_integer(frame.ftransfer as i64));
                vm.gc
                    .get_table_mut(tbl)
                    .raw_set_str(nt_key, TValue::from_integer(frame.ntransfer as i64));
            }
            if what_check.contains('t') {
                let frame = &vm.call_stack[fi];
                let tc_key = vm.strings.intern(b"istailcall");
                vm.gc
                    .get_table_mut(tbl)
                    .raw_set_str(tc_key, TValue::from_bool(frame.is_tail_call()));
            }
        }
    } else {
        // No frame — provide defaults for 'r' and 't' flags
        let what_check = what_str.strip_prefix('>').unwrap_or(&what_str);
        if what_check.contains('r') {
            let ft_key = vm.strings.intern(b"ftransfer");
            let nt_key = vm.strings.intern(b"ntransfer");
            vm.gc
                .get_table_mut(tbl)
                .raw_set_str(ft_key, TValue::from_integer(0));
            vm.gc
                .get_table_mut(tbl)
                .raw_set_str(nt_key, TValue::from_integer(0));
        }
        if what_check.contains('t') {
            let tc_key = vm.strings.intern(b"istailcall");
            vm.gc
                .get_table_mut(tbl)
                .raw_set_str(tc_key, TValue::from_bool(false));
        }
    }

    // Ensure namewhat defaults to "" when 'n' is requested (PUC Lua behavior)
    // For hook functions, ALWAYS set namewhat = "hook" (like PUC's CIST_HOOK)
    if what_str.contains('n') {
        let namewhat_key = vm.strings.intern(b"namewhat");
        let is_hook_frame = if let Some(cid) = queried_coro {
            queried_frame_idx
                .map(|fi| vm.coroutines[cid].call_stack[fi].is_hook_call())
                .unwrap_or(false)
        } else {
            queried_frame_idx
                .map(|fi| vm.call_stack[fi].is_hook_call())
                .unwrap_or(false)
        };
        if is_hook_frame {
            let hook_str = vm.strings.intern(b"hook");
            vm.gc
                .get_table_mut(tbl)
                .raw_set_str(namewhat_key, TValue::from_string_id(hook_str));
        } else {
            let t = vm.gc.get_table(tbl);
            if t.raw_get_str(namewhat_key).is_nil() {
                let empty = vm.strings.intern(b"");
                vm.gc
                    .get_table_mut(tbl)
                    .raw_set_str(namewhat_key, TValue::from_string_id(empty));
            }
        }
    }

    Ok(vec![TValue::from_table(tbl)])
}

/// debug.traceback([thread,] [message [, level]]) — produce a stack traceback string.
fn do_debug_traceback(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    // Detect optional thread (coroutine) argument
    let mut coro_id: Option<usize> = None;
    let (msg, level_arg) = {
        let first = args.first().copied().unwrap_or(TValue::nil());
        let is_thread = if let Some(tbl_idx) = first.as_table_idx() {
            if let Some(thread_mt) = vm.gc.thread_metatable {
                vm.gc.get_table(tbl_idx).metatable == Some(thread_mt)
            } else {
                false
            }
        } else {
            false
        };
        if is_thread {
            // First arg is a coroutine
            if let Some(tbl_idx) = first.as_table_idx() {
                let id_val = vm.gc.get_table(tbl_idx).raw_geti(1);
                let cid = id_val.as_integer().unwrap_or(-2);
                if cid >= 0 {
                    coro_id = Some(cid as usize);
                }
            }
            let m = args.get(1).copied().unwrap_or(TValue::nil());
            let l = args.get(2).copied().unwrap_or(TValue::nil());
            (m, l)
        } else {
            (first, args.get(1).copied().unwrap_or(TValue::nil()))
        }
    };

    // If message is not nil and not a string, return it as-is (PUC Lua behavior)
    if !msg.is_nil() && !msg.is_string() {
        return Ok(vec![msg]);
    }

    // Determine starting level (default 1 = caller of traceback)
    let start_level = if let Some(n) = level_arg.as_full_integer(&vm.gc) {
        n.max(0) as usize
    } else if coro_id.is_some() {
        0 // For coroutines, default level is 0
    } else {
        1
    };

    let mut lines: Vec<String> = Vec::new();

    // Add the message as first line if provided
    if let Some(sid) = msg.as_string_id() {
        let msg_str = String::from_utf8_lossy(vm.strings.get_bytes(sid)).into_owned();
        lines.push(msg_str);
    }

    lines.push("stack traceback:".to_string());

    // If the error came from a __close metamethod, add that frame
    if coro_id.is_none() && vm.last_error_from_close {
        lines.push("\t[C]: in metamethod 'close'".to_string());
        vm.last_error_from_close = false;
    }

    // Get the call_stack and stack to iterate over
    let (call_stack_ref, stack_ref): (Vec<CallInfo>, Vec<TValue>) = if let Some(cid) = coro_id {
        if cid < vm.coroutines.len() {
            (
                vm.coroutines[cid].call_stack.clone(),
                vm.coroutines[cid].stack.clone(),
            )
        } else {
            (vec![], vec![])
        }
    } else {
        // Use current thread's call stack (clone to avoid borrow issues)
        (vm.call_stack.clone(), vm.stack.clone())
    };

    let stack_len = call_stack_ref.len();

    // Level 0 = traceback itself (for current thread only).
    let mut frames_shown = 0;
    let skip_frames;
    if coro_id.is_none() && start_level == 0 {
        // Include traceback itself as level 0
        lines.push("\t[C]: in function 'debug.traceback'".to_string());
        frames_shown += 1;
        skip_frames = 0;
    } else if let Some(cid) = coro_id {
        // For coroutines, add a yield frame at level 0 if suspended
        if start_level == 0
            && cid < vm.coroutines.len()
            && vm.coroutines[cid].status == crate::vm::CoroutineStatus::Suspended
        {
            lines.push("\t[C]: in function 'coroutine.yield'".to_string());
            frames_shown += 1;
        }
        // skip_frames: start_level 0 means show all frames (yield already added)
        // start_level 1 means skip the yield frame (already not added above if start_level>0)
        //   and show from top of Lua frames
        skip_frames = if start_level > 0 { start_level - 1 } else { 0 };
    } else {
        skip_frames = start_level - 1;
    }
    let mut level = 0usize;

    // PUC Lua depth truncation: first 10, skip middle, last 11
    let max_first = 10usize;
    let max_last = 11usize;
    let total_frames = stack_len.saturating_sub(skip_frames);
    let needs_truncation = total_frames > max_first + max_last;

    for i in (0..stack_len).rev() {
        if level < skip_frames {
            level += 1;
            continue;
        }
        level += 1;

        // Depth truncation
        if needs_truncation {
            let frames_from_start = frames_shown;
            let frames_remaining = i + 1; // frames left including this one
            if frames_from_start >= max_first && frames_remaining > max_last {
                if frames_from_start == max_first {
                    let skipped = total_frames - max_first - max_last;
                    lines.push(format!("\t...\t(skipping {} levels)", skipped));
                }
                frames_shown += 1;
                continue;
            }
        }

        let frame = &call_stack_ref[i];
        if frame.is_lua() {
            let proto = &vm.protos[frame.proto_idx];
            let source_sid = proto
                .source
                .unwrap_or_else(|| vm.strings.intern_or_create(b"=?"));
            let source_bytes = vm.strings.get_bytes(source_sid).to_vec();
            let short_src = make_short_src(&source_bytes);

            let pc = if frame.pc > 0 { frame.pc - 1 } else { 0 };
            let current_line = proto.get_line(pc) as i64;

            // Determine function description
            let func_name = if proto.linedefined == 0 {
                "in main chunk".to_string()
            } else if coro_id.is_none() && vm.in_tbc_close > 0 && frames_shown == 0 {
                "in metamethod 'close'".to_string()
            } else if frame.is_hook_call() {
                let name = get_func_name_from_call_stack(vm, i, &call_stack_ref);
                if let Some(n) = name {
                    format!("in hook '{}'", n)
                } else {
                    format!("in hook <{}:{}>", short_src, proto.linedefined)
                }
            } else {
                // Try to find function name from caller
                let name = get_func_name_from_call_stack(vm, i, &call_stack_ref);
                if let Some(n) = name {
                    format!("in function '{}'", n)
                } else {
                    format!("in function <{}:{}>", short_src, proto.linedefined)
                }
            };

            lines.push(format!("\t{}:{}: {}", short_src, current_line, func_name));
        } else {
            // Native (C) function
            let func_val = stack_ref
                .get(frame.func_stack_idx)
                .copied()
                .unwrap_or(TValue::nil());
            if let Some(native_idx) = func_val.as_native_idx() {
                let name = vm.gc.get_native(native_idx).name;
                lines.push(format!("\t[C]: in function '{}'", name));
            } else {
                lines.push("\t[C]: in ?".to_string());
            }
        }
        frames_shown += 1;
    }

    let result = lines.join("\n");
    let sid = vm.strings.intern_or_create(result.as_bytes());
    Ok(vec![TValue::from_string_id(sid)])
}

/// Get function name for a frame by examining the caller's bytecode.
#[allow(dead_code)]
fn get_frame_func_name(vm: &Vm, frame_idx: usize) -> Option<String> {
    get_func_name_from_call_stack(vm, frame_idx, &vm.call_stack)
}

/// Get function name for a frame by examining the caller's bytecode in any call stack.
fn get_func_name_from_call_stack(
    vm: &Vm,
    frame_idx: usize,
    call_stack: &[CallInfo],
) -> Option<String> {
    use selune_compiler::opcode::OpCode;

    if frame_idx == 0 {
        return None;
    }
    let caller_idx = frame_idx - 1;
    let caller = &call_stack[caller_idx];
    if !caller.is_lua() || caller.pc == 0 {
        return None;
    }

    let caller_proto = &vm.protos[caller.proto_idx];
    let call_pc = caller.pc - 1;
    if call_pc >= caller_proto.code.len() {
        return None;
    }
    let call_inst = caller_proto.code[call_pc];

    let func_reg = match call_inst.opcode() {
        OpCode::Call | OpCode::TailCall => call_inst.a() as usize,
        _ => return None,
    };

    // Check if func_reg is a local variable at call_pc
    for lv in &caller_proto.local_vars {
        if lv.reg as usize == func_reg
            && (lv.start_pc as usize) <= call_pc
            && call_pc < (lv.end_pc as usize)
        {
            let name_bytes = vm.strings.get_bytes(lv.name);
            if !name_bytes.starts_with(b"(") {
                return Some(String::from_utf8_lossy(name_bytes).into_owned());
            }
        }
    }

    // Scan backwards for GetTabUp/GetField/Move
    if call_pc > 0 {
        for i in (0..call_pc).rev() {
            let prev_inst = caller_proto.code[i];
            if prev_inst.a() as usize != func_reg {
                continue;
            }
            match prev_inst.opcode() {
                OpCode::GetTabUp => {
                    let c = prev_inst.c() as usize;
                    if let Some(selune_compiler::proto::Constant::String(sid)) =
                        caller_proto.constants.get(c)
                    {
                        return Some(
                            String::from_utf8_lossy(vm.strings.get_bytes(*sid)).into_owned(),
                        );
                    }
                    break;
                }
                OpCode::GetField => {
                    let c = prev_inst.c() as usize;
                    if let Some(selune_compiler::proto::Constant::String(sid)) =
                        caller_proto.constants.get(c)
                    {
                        return Some(
                            String::from_utf8_lossy(vm.strings.get_bytes(*sid)).into_owned(),
                        );
                    }
                    break;
                }
                OpCode::GetUpval => {
                    let upval_idx = prev_inst.b() as usize;
                    if let Some(upval_desc) = caller_proto.upvalues.get(upval_idx) {
                        if let Some(name_sid) = upval_desc.name {
                            let name_bytes = vm.strings.get_bytes(name_sid);
                            if !name_bytes.starts_with(b"(") && name_bytes != b"_ENV" {
                                return Some(String::from_utf8_lossy(name_bytes).into_owned());
                            }
                        }
                    }
                    break;
                }
                OpCode::Move => {
                    let src_reg = prev_inst.b() as usize;
                    for lv in &caller_proto.local_vars {
                        if lv.reg as usize == src_reg
                            && (lv.start_pc as usize) <= i
                            && i < (lv.end_pc as usize)
                        {
                            let name_bytes = vm.strings.get_bytes(lv.name);
                            if !name_bytes.starts_with(b"(") {
                                return Some(String::from_utf8_lossy(name_bytes).into_owned());
                            }
                        }
                    }
                    break;
                }
                _ => break,
            }
        }
    }

    None
}

/// Fill info table for a native (C) function.
fn fill_native_info(
    vm: &mut Vm,
    tbl: selune_core::gc::GcIdx<selune_core::table::Table>,
    native_idx: Option<selune_core::gc::GcIdx<selune_core::gc::NativeFunction>>,
) {
    let what_key = vm.strings.intern(b"what");
    let what_val = vm.strings.intern_or_create(b"C");
    vm.gc
        .get_table_mut(tbl)
        .raw_set_str(what_key, TValue::from_string_id(what_val));

    let source_key = vm.strings.intern(b"source");
    let source_val = vm.strings.intern_or_create(b"=[C]");
    vm.gc
        .get_table_mut(tbl)
        .raw_set_str(source_key, TValue::from_string_id(source_val));

    let short_src_key = vm.strings.intern(b"short_src");
    let short_src_val = vm.strings.intern_or_create(b"[C]");
    vm.gc
        .get_table_mut(tbl)
        .raw_set_str(short_src_key, TValue::from_string_id(short_src_val));

    let currentline_key = vm.strings.intern(b"currentline");
    vm.gc
        .get_table_mut(tbl)
        .raw_set_str(currentline_key, TValue::from_integer(-1));

    let linedefined_key = vm.strings.intern(b"linedefined");
    vm.gc
        .get_table_mut(tbl)
        .raw_set_str(linedefined_key, TValue::from_integer(-1));

    let lastlinedefined_key = vm.strings.intern(b"lastlinedefined");
    vm.gc
        .get_table_mut(tbl)
        .raw_set_str(lastlinedefined_key, TValue::from_integer(-1));

    // nups: count upvalues for C closures (native functions with non-nil upvalue)
    let nups = if let Some(ni) = native_idx {
        let native = vm.gc.get_native(ni);
        if !native.upvalue.is_nil() {
            1i64
        } else {
            0
        }
    } else {
        0
    };
    let nups_key = vm.strings.intern(b"nups");
    vm.gc
        .get_table_mut(tbl)
        .raw_set_str(nups_key, TValue::from_integer(nups));

    let nparams_key = vm.strings.intern(b"nparams");
    vm.gc
        .get_table_mut(tbl)
        .raw_set_str(nparams_key, TValue::from_integer(0));

    let isvararg_key = vm.strings.intern(b"isvararg");
    vm.gc
        .get_table_mut(tbl)
        .raw_set_str(isvararg_key, TValue::from_bool(true));
}

/// Fill info table for a Lua function given its proto_idx.
fn fill_lua_info(
    vm: &mut Vm,
    tbl: selune_core::gc::GcIdx<selune_core::table::Table>,
    proto_idx: usize,
    pc: Option<usize>,
    func_val: Option<TValue>,
    what: &str,
) {
    let what_filter = what.strip_prefix('>').unwrap_or(what);

    // Source info
    {
        let proto = &vm.protos[proto_idx];

        let source_key = vm.strings.intern(b"source");
        let source_sid = proto
            .source
            .unwrap_or_else(|| vm.strings.intern_or_create(b"=?"));
        vm.gc
            .get_table_mut(tbl)
            .raw_set_str(source_key, TValue::from_string_id(source_sid));

        let source_bytes = vm.strings.get_bytes(source_sid).to_vec();
        let short_src = make_short_src(&source_bytes);
        let short_src_key = vm.strings.intern(b"short_src");
        let short_src_sid = vm.strings.intern_or_create(short_src.as_bytes());
        vm.gc
            .get_table_mut(tbl)
            .raw_set_str(short_src_key, TValue::from_string_id(short_src_sid));

        let what_key = vm.strings.intern(b"what");
        let is_main = proto.linedefined == 0 && proto.lastlinedefined == 0 && proto.is_vararg;
        let what_val = if is_main {
            vm.strings.intern_or_create(b"main")
        } else {
            vm.strings.intern_or_create(b"Lua")
        };
        vm.gc
            .get_table_mut(tbl)
            .raw_set_str(what_key, TValue::from_string_id(what_val));

        let linedefined_key = vm.strings.intern(b"linedefined");
        vm.gc.get_table_mut(tbl).raw_set_str(
            linedefined_key,
            TValue::from_integer(proto.linedefined as i64),
        );

        let lastlinedefined_key = vm.strings.intern(b"lastlinedefined");
        vm.gc.get_table_mut(tbl).raw_set_str(
            lastlinedefined_key,
            TValue::from_integer(proto.lastlinedefined as i64),
        );
    }

    // Current line
    {
        let currentline_key = vm.strings.intern(b"currentline");
        let current_line = if let Some(pc) = pc {
            let proto = &vm.protos[proto_idx];
            let line = proto.get_line(pc);
            if line == 0 {
                -1i64 // stripped code has no line info
            } else {
                line as i64
            }
        } else {
            -1
        };
        vm.gc
            .get_table_mut(tbl)
            .raw_set_str(currentline_key, TValue::from_integer(current_line));
    }

    // Upvalue/param info
    {
        let proto = &vm.protos[proto_idx];

        let nups_key = vm.strings.intern(b"nups");
        vm.gc
            .get_table_mut(tbl)
            .raw_set_str(nups_key, TValue::from_integer(proto.upvalues.len() as i64));

        let nparams_key = vm.strings.intern(b"nparams");
        vm.gc
            .get_table_mut(tbl)
            .raw_set_str(nparams_key, TValue::from_integer(proto.num_params as i64));

        let isvararg_key = vm.strings.intern(b"isvararg");
        vm.gc
            .get_table_mut(tbl)
            .raw_set_str(isvararg_key, TValue::from_bool(proto.is_vararg));
    }

    // 'f' — the function itself
    if what_filter.contains('f') {
        if let Some(fv) = func_val {
            let func_key = vm.strings.intern(b"func");
            vm.gc.get_table_mut(tbl).raw_set_str(func_key, fv);
        }
    }

    // 'L' — active lines table
    if what_filter.contains('L') {
        let proto = &vm.protos[proto_idx];
        let activelines_tbl = vm.gc.alloc_table(0, 8);
        for i in 0..proto.code.len() {
            let line = proto.get_line(i);
            if line > 0 {
                vm.gc
                    .get_table_mut(activelines_tbl)
                    .raw_seti(line as i64, TValue::from_bool(true));
            }
        }
        let activelines_key = vm.strings.intern(b"activelines");
        vm.gc
            .get_table_mut(tbl)
            .raw_set_str(activelines_key, TValue::from_table(activelines_tbl));
    }
}

/// Map metamethod index (from MMBin/MMBinI/MMBinK C field) to name without __ prefix.
fn mm_idx_to_name(idx: u8) -> &'static [u8] {
    match idx {
        0 => b"add",
        1 => b"sub",
        2 => b"mul",
        3 => b"mod",
        4 => b"pow",
        5 => b"div",
        6 => b"idiv",
        7 => b"band",
        8 => b"bor",
        9 => b"bxor",
        10 => b"shl",
        11 => b"shr",
        12 => b"concat",
        _ => b"unknown",
    }
}

/// Set name and namewhat="metamethod" on a debug.getinfo result table.
fn set_mm_name_on_table(
    vm: &mut Vm,
    tbl: selune_core::gc::GcIdx<selune_core::table::Table>,
    mm_name: &[u8],
) {
    let name_key = vm.strings.intern(b"name");
    let name_val = vm.strings.intern_or_create(mm_name);
    vm.gc
        .get_table_mut(tbl)
        .raw_set_str(name_key, TValue::from_string_id(name_val));
    let namewhat_key = vm.strings.intern(b"namewhat");
    let namewhat_val = vm.strings.intern_or_create(b"metamethod");
    vm.gc
        .get_table_mut(tbl)
        .raw_set_str(namewhat_key, TValue::from_string_id(namewhat_val));
}

/// Try to find a function name by examining the calling frame's bytecode.
/// Sets 'name' and 'namewhat' on the result table if found.
fn fill_func_name(
    vm: &mut Vm,
    tbl: selune_core::gc::GcIdx<selune_core::table::Table>,
    frame_idx: usize,
) {
    use selune_compiler::opcode::OpCode;

    // TBC __close calls: report as name="close", namewhat="metamethod"
    if frame_idx < vm.call_stack.len() && vm.call_stack[frame_idx].is_tbc_close() {
        set_mm_name_on_table(vm, tbl, b"close");
        return;
    }

    if frame_idx == 0 {
        return;
    }
    let caller_idx = frame_idx - 1;
    let caller = &vm.call_stack[caller_idx];
    if !caller.is_lua() || caller.pc == 0 {
        return;
    }

    let caller_proto = &vm.protos[caller.proto_idx];
    let call_pc = caller.pc - 1;
    if call_pc >= caller_proto.code.len() {
        return;
    }
    let call_inst = caller_proto.code[call_pc];

    let func_reg = match call_inst.opcode() {
        OpCode::Call | OpCode::TailCall => call_inst.a() as usize,
        // Metamethod invocations via MMBin/MMBinI/MMBinK (arithmetic/bitwise dispatched through fallthrough)
        OpCode::MMBin | OpCode::MMBinI | OpCode::MMBinK => {
            let mm_idx = call_inst.c();
            let mm_name: &[u8] = mm_idx_to_name(mm_idx);
            set_mm_name_on_table(vm, tbl, mm_name);
            return;
        }
        // Metamethod invocations from comparison ops (call call_function directly)
        OpCode::Eq | OpCode::EqI | OpCode::EqK => {
            set_mm_name_on_table(vm, tbl, b"eq");
            return;
        }
        OpCode::Lt | OpCode::LtI | OpCode::GtI => {
            set_mm_name_on_table(vm, tbl, b"lt");
            return;
        }
        OpCode::Le | OpCode::LeI | OpCode::GeI => {
            set_mm_name_on_table(vm, tbl, b"le");
            return;
        }
        // Metamethod invocations from index/newindex ops (call via table_index/table_newindex)
        OpCode::GetTable | OpCode::GetI | OpCode::GetField => {
            set_mm_name_on_table(vm, tbl, b"index");
            return;
        }
        OpCode::SetTable | OpCode::SetI | OpCode::SetField => {
            set_mm_name_on_table(vm, tbl, b"newindex");
            return;
        }
        // Unary metamethods (call call_function directly)
        OpCode::Unm => {
            set_mm_name_on_table(vm, tbl, b"unm");
            return;
        }
        OpCode::Len => {
            set_mm_name_on_table(vm, tbl, b"len");
            return;
        }
        OpCode::BNot => {
            set_mm_name_on_table(vm, tbl, b"bnot");
            return;
        }
        OpCode::Concat => {
            set_mm_name_on_table(vm, tbl, b"concat");
            return;
        }
        // ShlI/ShrI call call_function directly (no following MMBinI)
        OpCode::ShlI => {
            set_mm_name_on_table(vm, tbl, b"shl");
            return;
        }
        OpCode::ShrI => {
            set_mm_name_on_table(vm, tbl, b"shr");
            return;
        }
        OpCode::TForCall => {
            let name_key = vm.strings.intern(b"name");
            let name_val = vm.strings.intern_or_create(b"for iterator");
            vm.gc
                .get_table_mut(tbl)
                .raw_set_str(name_key, TValue::from_string_id(name_val));
            let namewhat_key = vm.strings.intern(b"namewhat");
            let namewhat_val = vm.strings.intern_or_create(b"");
            vm.gc
                .get_table_mut(tbl)
                .raw_set_str(namewhat_key, TValue::from_string_id(namewhat_val));
            return;
        }
        _ => return,
    };

    // Helper: find local variable name for a register at a given PC
    let find_local_name = |proto: &selune_compiler::proto::Proto,
                           reg: usize,
                           pc: usize|
     -> Option<selune_core::string::StringId> {
        for lv in &proto.local_vars {
            if lv.reg as usize == reg && (lv.start_pc as usize) <= pc && pc < (lv.end_pc as usize) {
                let name_bytes = vm.strings.get_bytes(lv.name);
                if !name_bytes.starts_with(b"(") {
                    return Some(lv.name);
                }
            }
        }
        None
    };

    let mut found_name: Option<(Vec<u8>, &'static [u8])> = None;

    // Strategy 1: Check if func_reg is a local variable at call_pc
    if let Some(name_sid) = find_local_name(caller_proto, func_reg, call_pc) {
        let name_bytes = vm.strings.get_bytes(name_sid).to_vec();
        found_name = Some((name_bytes, b"local"));
    }

    // Strategy 2: Scan backwards to find instruction that loaded func_reg
    if found_name.is_none() && call_pc > 0 {
        for i in (0..call_pc).rev() {
            let prev_inst = caller_proto.code[i];
            if prev_inst.a() as usize != func_reg {
                continue;
            }
            match prev_inst.opcode() {
                OpCode::GetTabUp => {
                    let c = prev_inst.c() as usize;
                    if let Some(selune_compiler::proto::Constant::String(sid)) =
                        caller_proto.constants.get(c)
                    {
                        let name_bytes = vm.strings.get_bytes(*sid).to_vec();
                        found_name = Some((name_bytes, b"global"));
                    }
                    break;
                }
                OpCode::GetField => {
                    let c = prev_inst.c() as usize;
                    if let Some(selune_compiler::proto::Constant::String(sid)) =
                        caller_proto.constants.get(c)
                    {
                        let name_bytes = vm.strings.get_bytes(*sid).to_vec();
                        found_name = Some((name_bytes, b"field"));
                    }
                    break;
                }
                OpCode::Self_ => {
                    let c = prev_inst.c() as usize;
                    if prev_inst.k() {
                        if let Some(selune_compiler::proto::Constant::String(sid)) =
                            caller_proto.constants.get(c)
                        {
                            let name_bytes = vm.strings.get_bytes(*sid).to_vec();
                            found_name = Some((name_bytes, b"method"));
                        }
                    }
                    break;
                }
                OpCode::GetUpval => {
                    let upval_idx = prev_inst.b() as usize;
                    if let Some(upval_desc) = caller_proto.upvalues.get(upval_idx) {
                        if let Some(name_sid) = upval_desc.name {
                            let name_bytes = vm.strings.get_bytes(name_sid).to_vec();
                            if !name_bytes.starts_with(b"(") && name_bytes != b"_ENV" {
                                found_name = Some((name_bytes, b"upvalue"));
                            }
                        }
                    }
                    break;
                }
                OpCode::Move => {
                    // Follow the move: check if source is a named local
                    let src_reg = prev_inst.b() as usize;
                    if let Some(name_sid) = find_local_name(caller_proto, src_reg, i) {
                        let name_bytes = vm.strings.get_bytes(name_sid).to_vec();
                        found_name = Some((name_bytes, b"local"));
                    }
                    break;
                }
                _ => break,
            }
        }
    }

    if let Some((name_bytes, namewhat_bytes)) = found_name {
        let name_key = vm.strings.intern(b"name");
        let name_val = vm.strings.intern_or_create(&name_bytes);
        vm.gc
            .get_table_mut(tbl)
            .raw_set_str(name_key, TValue::from_string_id(name_val));

        let namewhat_key = vm.strings.intern(b"namewhat");
        let namewhat_val = vm.strings.intern_or_create(namewhat_bytes);
        vm.gc
            .get_table_mut(tbl)
            .raw_set_str(namewhat_key, TValue::from_string_id(namewhat_val));
    }
}

/// Like fill_func_name, but uses an arbitrary call_stack (for coroutine queries).
fn fill_func_name_from_stack(
    vm: &mut Vm,
    tbl: selune_core::gc::GcIdx<selune_core::table::Table>,
    frame_idx: usize,
    call_stack: &[CallInfo],
) {
    use selune_compiler::opcode::OpCode;

    // TBC __close calls: report as name="close", namewhat="metamethod"
    if frame_idx < call_stack.len() && call_stack[frame_idx].is_tbc_close() {
        set_mm_name_on_table(vm, tbl, b"close");
        return;
    }

    if frame_idx == 0 {
        return;
    }
    let caller_idx = frame_idx - 1;
    let caller = &call_stack[caller_idx];
    if !caller.is_lua() || caller.pc == 0 {
        return;
    }

    let caller_proto = &vm.protos[caller.proto_idx];
    let call_pc = caller.pc - 1;
    if call_pc >= caller_proto.code.len() {
        return;
    }
    let call_inst = caller_proto.code[call_pc];

    let func_reg = match call_inst.opcode() {
        OpCode::Call | OpCode::TailCall => call_inst.a() as usize,
        // Metamethod invocations via MMBin/MMBinI/MMBinK (arithmetic/bitwise dispatched through fallthrough)
        OpCode::MMBin | OpCode::MMBinI | OpCode::MMBinK => {
            let mm_idx = call_inst.c();
            let mm_name: &[u8] = mm_idx_to_name(mm_idx);
            set_mm_name_on_table(vm, tbl, mm_name);
            return;
        }
        // Metamethod invocations from comparison ops (call call_function directly)
        OpCode::Eq | OpCode::EqI | OpCode::EqK => {
            set_mm_name_on_table(vm, tbl, b"eq");
            return;
        }
        OpCode::Lt | OpCode::LtI | OpCode::GtI => {
            set_mm_name_on_table(vm, tbl, b"lt");
            return;
        }
        OpCode::Le | OpCode::LeI | OpCode::GeI => {
            set_mm_name_on_table(vm, tbl, b"le");
            return;
        }
        // Metamethod invocations from index/newindex ops (call via table_index/table_newindex)
        OpCode::GetTable | OpCode::GetI | OpCode::GetField => {
            set_mm_name_on_table(vm, tbl, b"index");
            return;
        }
        OpCode::SetTable | OpCode::SetI | OpCode::SetField => {
            set_mm_name_on_table(vm, tbl, b"newindex");
            return;
        }
        // Unary metamethods (call call_function directly)
        OpCode::Unm => {
            set_mm_name_on_table(vm, tbl, b"unm");
            return;
        }
        OpCode::Len => {
            set_mm_name_on_table(vm, tbl, b"len");
            return;
        }
        OpCode::BNot => {
            set_mm_name_on_table(vm, tbl, b"bnot");
            return;
        }
        OpCode::Concat => {
            set_mm_name_on_table(vm, tbl, b"concat");
            return;
        }
        // ShlI/ShrI call call_function directly (no following MMBinI)
        OpCode::ShlI => {
            set_mm_name_on_table(vm, tbl, b"shl");
            return;
        }
        OpCode::ShrI => {
            set_mm_name_on_table(vm, tbl, b"shr");
            return;
        }
        OpCode::TForCall => {
            let name_key = vm.strings.intern(b"name");
            let name_val = vm.strings.intern_or_create(b"for iterator");
            vm.gc
                .get_table_mut(tbl)
                .raw_set_str(name_key, TValue::from_string_id(name_val));
            let namewhat_key = vm.strings.intern(b"namewhat");
            let namewhat_val = vm.strings.intern_or_create(b"");
            vm.gc
                .get_table_mut(tbl)
                .raw_set_str(namewhat_key, TValue::from_string_id(namewhat_val));
            return;
        }
        _ => return,
    };

    let find_local_name = |proto: &selune_compiler::proto::Proto,
                           reg: usize,
                           pc: usize|
     -> Option<selune_core::string::StringId> {
        for lv in &proto.local_vars {
            if lv.reg as usize == reg && (lv.start_pc as usize) <= pc && pc < (lv.end_pc as usize) {
                let name_bytes = vm.strings.get_bytes(lv.name);
                if !name_bytes.starts_with(b"(") {
                    return Some(lv.name);
                }
            }
        }
        None
    };

    let mut found_name: Option<(Vec<u8>, &'static [u8])> = None;

    if let Some(name_sid) = find_local_name(caller_proto, func_reg, call_pc) {
        let name_bytes = vm.strings.get_bytes(name_sid).to_vec();
        found_name = Some((name_bytes, b"local"));
    }

    if found_name.is_none() && call_pc > 0 {
        for i in (0..call_pc).rev() {
            let prev_inst = caller_proto.code[i];
            if prev_inst.a() as usize != func_reg {
                continue;
            }
            match prev_inst.opcode() {
                OpCode::GetTabUp => {
                    let c = prev_inst.c() as usize;
                    if let Some(selune_compiler::proto::Constant::String(sid)) =
                        caller_proto.constants.get(c)
                    {
                        let name_bytes = vm.strings.get_bytes(*sid).to_vec();
                        found_name = Some((name_bytes, b"global"));
                    }
                    break;
                }
                OpCode::GetField => {
                    let c = prev_inst.c() as usize;
                    if let Some(selune_compiler::proto::Constant::String(sid)) =
                        caller_proto.constants.get(c)
                    {
                        let name_bytes = vm.strings.get_bytes(*sid).to_vec();
                        found_name = Some((name_bytes, b"field"));
                    }
                    break;
                }
                OpCode::Self_ => {
                    let c = prev_inst.c() as usize;
                    if prev_inst.k() {
                        if let Some(selune_compiler::proto::Constant::String(sid)) =
                            caller_proto.constants.get(c)
                        {
                            let name_bytes = vm.strings.get_bytes(*sid).to_vec();
                            found_name = Some((name_bytes, b"method"));
                        }
                    }
                    break;
                }
                OpCode::GetUpval => {
                    let upval_idx = prev_inst.b() as usize;
                    if let Some(upval_desc) = caller_proto.upvalues.get(upval_idx) {
                        if let Some(name_sid) = upval_desc.name {
                            let name_bytes = vm.strings.get_bytes(name_sid).to_vec();
                            if !name_bytes.starts_with(b"(") && name_bytes != b"_ENV" {
                                found_name = Some((name_bytes, b"upvalue"));
                            }
                        }
                    }
                    break;
                }
                OpCode::Move => {
                    let src_reg = prev_inst.b() as usize;
                    if let Some(name_sid) = find_local_name(caller_proto, src_reg, i) {
                        let name_bytes = vm.strings.get_bytes(name_sid).to_vec();
                        found_name = Some((name_bytes, b"local"));
                    }
                    break;
                }
                _ => break,
            }
        }
    }

    if let Some((name_bytes, namewhat_bytes)) = found_name {
        let name_key = vm.strings.intern(b"name");
        let name_val = vm.strings.intern_or_create(&name_bytes);
        vm.gc
            .get_table_mut(tbl)
            .raw_set_str(name_key, TValue::from_string_id(name_val));

        let namewhat_key = vm.strings.intern(b"namewhat");
        let namewhat_val = vm.strings.intern_or_create(namewhat_bytes);
        vm.gc
            .get_table_mut(tbl)
            .raw_set_str(namewhat_key, TValue::from_string_id(namewhat_val));
    }
}

/// Create short_src from source name (like luaO_chunkid).
fn make_short_src(source: &[u8]) -> String {
    let s = String::from_utf8_lossy(source);
    if let Some(rest) = s.strip_prefix('=') {
        // Exact source: use as-is (truncated to LUA_IDSIZE - 1)
        if rest.len() >= 60 {
            rest[..59].to_string()
        } else {
            rest.to_string()
        }
    } else if let Some(name) = s.strip_prefix('@') {
        if name.len() > 60 {
            format!("...{}", &name[name.len() - 57..])
        } else {
            name.to_string()
        }
    } else {
        // String source: [string "first_line..."]
        // PUC Lua: take first line, add "..." if multi-line or too long
        let first_line = s.lines().next().unwrap_or(&s);
        let has_newline = s.contains('\n');
        // Max content: LUA_IDSIZE - 1 - 14 (overhead for [string "..."]) = 45
        let max_content = 45;
        if first_line.len() > max_content {
            format!("[string \"{}...\"]", &first_line[..max_content])
        } else if has_newline {
            format!("[string \"{}...\"]", first_line)
        } else {
            format!("[string \"{}\"]", first_line)
        }
    }
}

/// Handle `coroutine.running()` — returns the running coroutine and whether it's the main thread.
fn do_coro_running(vm: &mut Vm) -> Result<Vec<TValue>, LuaError> {
    if vm.running_coro.is_some() {
        // Inside a coroutine — return the coroutine's handle table
        if let Some(handle) = vm.running_coro_handle {
            Ok(vec![TValue::from_table(handle), TValue::from_bool(false)])
        } else {
            // Fallback (shouldn't happen)
            let thread_standin = vm.gc.alloc_table(0, 0);
            vm.gc.get_table_mut(thread_standin).metatable = vm.gc.thread_metatable;
            Ok(vec![
                TValue::from_table(thread_standin),
                TValue::from_bool(false),
            ])
        }
    } else {
        // Main thread — return stable main_thread_handle
        if let Some(handle) = vm.main_thread_handle {
            Ok(vec![TValue::from_table(handle), TValue::from_bool(true)])
        } else {
            let thread_standin = vm.gc.alloc_table(0, 0);
            vm.gc.get_table_mut(thread_standin).metatable = vm.gc.thread_metatable;
            Ok(vec![
                TValue::from_table(thread_standin),
                TValue::from_bool(true),
            ])
        }
    }
}

/// Handle `coroutine.isyieldable([co])` — returns whether the coroutine can yield.
fn do_coro_isyieldable(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    if let Some(co_val) = args.first() {
        // isyieldable(co) — check if the given coroutine is yieldable
        if let Some(table_idx) = co_val.as_table_idx() {
            // Check if it has a thread metatable
            let is_thread = vm
                .gc
                .thread_metatable
                .is_some_and(|mt| vm.gc.get_table(table_idx).metatable == Some(mt));
            if !is_thread {
                return Err(LuaError::Runtime(
                    "bad argument #1 to 'isyieldable' (coroutine expected)".to_string(),
                ));
            }
            // Check coro_id
            let id_val = vm.gc.get_table(table_idx).raw_geti(1);
            let coro_id = id_val.as_integer().unwrap_or(-2);
            if coro_id == -2 {
                // Main thread handle — never yieldable
                return Ok(vec![TValue::from_bool(false)]);
            }
            // A suspended coroutine is yieldable; a running one is yieldable
            // only if it IS the running coroutine (inside its body).
            // A dead or normal coroutine is not yieldable.
            if coro_id == -1 {
                // Not yet allocated — suspended, so yieldable
                return Ok(vec![TValue::from_bool(true)]);
            }
            let idx = coro_id as usize;
            if idx < vm.coroutines.len() {
                use crate::vm::CoroutineStatus;
                let status = vm.coroutines[idx].status;
                let yieldable = matches!(
                    status,
                    CoroutineStatus::Suspended | CoroutineStatus::Running
                );
                return Ok(vec![TValue::from_bool(yieldable)]);
            }
            return Ok(vec![TValue::from_bool(false)]);
        }
        return Err(LuaError::Runtime(
            "bad argument #1 to 'isyieldable' (coroutine expected)".to_string(),
        ));
    }
    // No args: check if we're in a yieldable context
    // Must be inside a coroutine AND not inside a non-yieldable C call
    Ok(vec![TValue::from_bool(
        vm.running_coro.is_some() && vm.nonyieldable_depth == 0,
    )])
}

/// Handle `coroutine.close(co)` — close a suspended or dead coroutine.
/// For suspended coroutines with TBC variables, resumes the coroutine to run __close metamethods.
fn do_coro_close(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    use crate::vm::CoroutineStatus;

    let co_val = args.first().copied().unwrap_or(TValue::nil());
    let table_idx = co_val.as_table_idx().ok_or_else(|| {
        let type_name = selune_core::object::lua_type_name(co_val, &vm.gc);
        LuaError::Runtime(format!(
            "bad argument #1 to 'close' (coroutine expected, got {})",
            type_name
        ))
    })?;

    // Verify it's a thread
    let is_thread = vm
        .gc
        .thread_metatable
        .is_some_and(|mt| vm.gc.get_table(table_idx).metatable == Some(mt));
    if !is_thread {
        return Err(LuaError::Runtime(
            "bad argument #1 to 'close' (coroutine expected, got table)".to_string(),
        ));
    }

    let status_val = vm.gc.get_table(table_idx).raw_geti(3);
    let status_bytes = if let Some(sid) = status_val.as_string_id() {
        vm.strings.get_bytes(sid).to_vec()
    } else {
        b"suspended".to_vec()
    };

    if status_bytes == b"dead" {
        // Check for stored error from a previous error death
        let err_val = vm.gc.get_table(table_idx).raw_geti(4);
        if !err_val.is_nil() {
            // Clear the stored error (subsequent close returns true)
            vm.gc.get_table_mut(table_idx).raw_seti(4, TValue::nil());
            return Ok(vec![TValue::from_bool(false), err_val]);
        }
        return Ok(vec![TValue::from_bool(true)]);
    }
    if status_bytes == b"running" {
        return Err(LuaError::Runtime(
            "cannot close a running coroutine".to_string(),
        ));
    }
    if status_bytes == b"normal" {
        return Err(LuaError::Runtime(
            "cannot close a normal coroutine".to_string(),
        ));
    }

    // It's "suspended" — we need to close it.
    let coro_id_val = vm.gc.get_table(table_idx).raw_geti(1);
    let coro_id = coro_id_val.as_integer().unwrap_or(-1);

    if coro_id == -2 {
        return Err(LuaError::Runtime(
            "cannot close a running coroutine".to_string(),
        ));
    }

    if coro_id == -1 {
        // Never resumed — just mark as dead
        let dead_sid = vm.strings.intern(b"dead");
        vm.gc
            .get_table_mut(table_idx)
            .raw_seti(3, TValue::from_string_id(dead_sid));
        return Ok(vec![TValue::from_bool(true)]);
    }

    let coro_idx = coro_id as usize;
    if coro_idx >= vm.coroutines.len() {
        let dead_sid = vm.strings.intern(b"dead");
        vm.gc
            .get_table_mut(table_idx)
            .raw_seti(3, TValue::from_string_id(dead_sid));
        return Ok(vec![TValue::from_bool(true)]);
    }

    // Check if the coroutine has TBC variables that need closing
    let has_tbc = vm.coroutines[coro_idx]
        .call_stack
        .iter()
        .any(|ci| !ci.tbc_slots_is_empty());

    if !has_tbc {
        // No TBC variables — just mark as dead
        vm.coroutines[coro_idx].status = CoroutineStatus::Dead;
        let dead_sid = vm.strings.intern(b"dead");
        vm.gc
            .get_table_mut(table_idx)
            .raw_seti(3, TValue::from_string_id(dead_sid));
        return Ok(vec![TValue::from_bool(true)]);
    }

    // Has TBC variables — need to resume the coroutine to run __close metamethods.
    let prev_running_coro = vm.running_coro;
    let prev_running_coro_handle = vm.running_coro_handle;
    let caller_thread_id = prev_running_coro.unwrap_or(usize::MAX);

    vm.remap_open_upvals_to_thread(caller_thread_id);

    // Save caller state by swapping
    {
        let mut caller = crate::vm::LuaThread {
            stack: Vec::new(),
            call_stack: Vec::new(),
            stack_top: 0,
            open_upvals: Vec::new(),
            status: CoroutineStatus::Normal,
            thread_id: caller_thread_id,
            hook_func: TValue::nil(),
            hook_mask: 0,
            hook_count: 0,
            hook_counter: 0,
            hooks_active: false,
            hook_last_line: -1,
            hook_old_pc: 0,
        };
        vm.save_running_state_swap(&mut caller);
        vm.coro_caller_stack.push(caller);
    }

    // Swap coroutine state into VM
    vm.restore_coro_into_running(coro_idx);
    vm.running_coro = Some(coro_idx);
    vm.running_coro_handle = Some(table_idx);
    vm.coroutines[coro_idx].status = CoroutineStatus::Running;

    vm.restore_open_upvals_from_thread(coro_idx);

    // Set status to "running"
    let running_sid = vm.strings.intern(b"running");
    vm.gc
        .get_table_mut(table_idx)
        .raw_seti(3, TValue::from_string_id(running_sid));

    // Close TBC variables in all frames (from top to bottom)
    let mut close_err: Option<TValue> = None;
    while !vm.call_stack.is_empty() {
        let ci_idx = vm.call_stack.len() - 1;
        if vm.call_stack[ci_idx].tbc_slots_is_empty() {
            if vm.call_stack.len() <= 1 {
                break;
            }
            vm.call_stack.pop();
            continue;
        }
        let base = vm.call_stack[ci_idx].base;
        match close_tbc_variables(vm, ci_idx, base, close_err) {
            Ok(()) => {
                close_err = None;
            }
            Err(LuaError::LuaValue(v)) => {
                close_err = Some(v);
            }
            Err(e) => {
                close_err = Some(e.to_tvalue(&mut vm.strings));
            }
        }
        if vm.call_stack.len() <= 1 {
            break;
        }
        vm.call_stack.pop();
    }

    // Close upvalues
    vm.close_upvalues(0);

    // Restore caller state
    let mut caller_state = vm.coro_caller_stack.pop().unwrap();
    vm.save_coro_state(coro_idx);
    vm.coroutines[coro_idx].status = CoroutineStatus::Dead;
    let dead_sid = vm.strings.intern(b"dead");
    vm.gc
        .get_table_mut(table_idx)
        .raw_seti(3, TValue::from_string_id(dead_sid));

    vm.restore_running_state_swap(&mut caller_state);
    vm.running_coro = prev_running_coro;
    vm.running_coro_handle = prev_running_coro_handle;
    vm.restore_open_upvals_from_thread(caller_thread_id);

    // Restore caller status
    let running_s = vm.strings.intern(b"running");
    if let Some(prev_handle) = prev_running_coro_handle {
        vm.gc
            .get_table_mut(prev_handle)
            .raw_seti(3, TValue::from_string_id(running_s));
    } else if let Some(main_handle) = vm.main_thread_handle {
        vm.gc
            .get_table_mut(main_handle)
            .raw_seti(3, TValue::from_string_id(running_s));
    }

    if let Some(err_val) = close_err {
        Ok(vec![TValue::from_bool(false), err_val])
    } else {
        Ok(vec![TValue::from_bool(true)])
    }
}

/// Handle `string.format(fmt, ...)` with VM access for __tostring metamethods.
/// Pre-processes args that use `%s` conversion via tostring, then calls the native format.
/// Handle `string.dump(func [, strip])` with full VM access.
fn do_string_dump(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    let func = args.first().copied().unwrap_or(TValue::nil());
    let strip = args
        .get(1)
        .copied()
        .map(|v| !v.is_nil() && !v.is_falsy())
        .unwrap_or(false);

    let closure_idx = func
        .as_closure_idx()
        .ok_or_else(|| LuaError::Runtime("unable to dump given function".to_string()))?;

    // Can't dump C (native) functions — but this is already checked by as_closure_idx
    let closure = vm.gc.get_closure(closure_idx);
    let proto_idx = closure.proto_idx;
    let proto = &vm.protos[proto_idx];

    let bytes = crate::binary_chunk::dump(proto, &vm.strings, strip);
    let sid = vm.strings.intern_or_create(&bytes);
    Ok(vec![TValue::from_string_id(sid)])
}

fn do_string_format(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    // Parse the format string to find which arg positions use %s
    let mut s_positions = Vec::new();
    if let Some(fmt_val) = args.first() {
        if let Some(sid) = fmt_val.as_string_id() {
            let fmt_bytes = vm.strings.get_bytes(sid).to_vec();
            let mut arg_idx = 1usize; // 1-based index into args (0 is fmt)
            let mut i = 0;
            while i < fmt_bytes.len() {
                if fmt_bytes[i] == b'%' {
                    i += 1;
                    if i >= fmt_bytes.len() {
                        break;
                    }
                    if fmt_bytes[i] == b'%' {
                        i += 1;
                        continue;
                    }
                    // Skip flags, width, precision
                    while i < fmt_bytes.len() && b"-+ #0".contains(&fmt_bytes[i]) {
                        i += 1;
                    }
                    while i < fmt_bytes.len() && fmt_bytes[i].is_ascii_digit() {
                        i += 1;
                    }
                    if i < fmt_bytes.len() && fmt_bytes[i] == b'.' {
                        i += 1;
                        while i < fmt_bytes.len() && fmt_bytes[i].is_ascii_digit() {
                            i += 1;
                        }
                    }
                    if i < fmt_bytes.len() {
                        if fmt_bytes[i] == b's' {
                            s_positions.push(arg_idx);
                        }
                        arg_idx += 1;
                        i += 1;
                    }
                } else {
                    i += 1;
                }
            }
        }
    }
    // Pre-process only args at %s positions that are table/userdata
    let mut processed_args = args.to_vec();
    for &pos in &s_positions {
        if pos < processed_args.len() {
            let val = processed_args[pos];
            if val.as_table_idx().is_some() || val.as_userdata_idx().is_some() {
                let ts = do_tostring(vm, &[val])?;
                if let Some(result) = ts.first() {
                    processed_args[pos] = *result;
                }
            }
        }
    }
    // Now call the native string.format with pre-processed args
    let native_ref = vm.gc.get_native(vm.string_format_idx.unwrap());
    let native_fn = native_ref.func;
    let native_upvalue = native_ref.upvalue;
    let mut ctx = NativeContext {
        args: &processed_args,
        gc: &mut vm.gc,
        strings: &mut vm.strings,
        upvalue: native_upvalue,
    };
    native_fn(&mut ctx).map_err(|e| LuaError::Runtime(format!("{:?}", e)))
}

/// Convert a compile-time Constant to a runtime TValue.
pub fn constant_to_tvalue(k: &Constant, gc: &mut selune_core::gc::GcHeap) -> TValue {
    match k {
        Constant::Nil => TValue::nil(),
        Constant::Boolean(b) => TValue::from_bool(*b),
        Constant::Integer(i) => TValue::from_full_integer(*i, gc),
        Constant::Float(f) => TValue::from_float(*f),
        Constant::String(sid) => TValue::from_string_id(*sid),
    }
}

/// pairs(t) — with __pairs metamethod support
fn do_pairs(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    let table_val = args.first().copied().unwrap_or(TValue::nil());

    // Check for __pairs metamethod
    let mm_name = vm.mm_names.as_ref().unwrap().pairs;
    if let Some(mm) = crate::metamethod::get_metamethod(table_val, mm_name, &vm.gc) {
        // Call __pairs(t) and return its results
        return call_function(vm, mm, &[table_val]);
    }

    // No metamethod: validate it's a table
    if table_val.as_table_idx().is_none() {
        return Err(add_error_prefix(
            vm,
            LuaError::Runtime("bad argument #1 to 'pairs' (table expected)".to_string()),
        ));
    }
    // Return (next, table, nil)
    let next_val = vm.next_val;
    Ok(vec![next_val, table_val, TValue::nil()])
}

/// ipairs iterator with __index support
fn do_ipairs_iter(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    let table_val = args.first().copied().unwrap_or(TValue::nil());
    let i = args
        .get(1)
        .and_then(|v| v.as_full_integer(&vm.gc))
        .unwrap_or(0);
    let next_i = i.wrapping_add(1);
    let key = TValue::from_full_integer(next_i, &mut vm.gc);

    // Use table_index which respects __index metamethods
    let val = table_index(vm, table_val, key)?;
    if val.is_nil() {
        Ok(vec![TValue::nil()])
    } else {
        Ok(vec![key, val])
    }
}

/// Get the length of a table-like object, respecting __len metamethod.
fn obj_len(vm: &mut Vm, obj: TValue) -> Result<i64, LuaError> {
    let mm_name = vm.mm_names.as_ref().unwrap().len;
    if let Some(mm) = crate::metamethod::get_metamethod(obj, mm_name, &vm.gc) {
        let result = call_function(vm, mm, &[obj, obj])?;
        let len_val = result.first().copied().unwrap_or(TValue::nil());
        if let Some(i) = len_val.as_full_integer(&vm.gc) {
            return Ok(i);
        }
        if let Some(f) = len_val.as_float() {
            if f.fract() == 0.0 {
                return Ok(f as i64);
            }
        }
        return Err(LuaError::Runtime(
            "object length is not an integer".to_string(),
        ));
    }
    if let Some(table_idx) = obj.as_table_idx() {
        Ok(vm.gc.get_table(table_idx).length())
    } else {
        Err(LuaError::Runtime(
            "attempt to get length of a non-table value".to_string(),
        ))
    }
}

/// table.insert(t [,pos], val) with full metamethod support
fn do_table_insert(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    let table_val = args.first().copied().unwrap_or(TValue::nil());
    let len = obj_len(vm, table_val)?;
    let e = len.wrapping_add(1);

    match args.len() {
        2 => {
            // table.insert(t, val) — append
            let val = args[1];
            let key = TValue::from_full_integer(e, &mut vm.gc);
            table_newindex(vm, table_val, key, val)?;
        }
        3 => {
            // table.insert(t, pos, val) — insert at pos
            let pos_val = args[1];
            let pos = pos_val.as_full_integer(&vm.gc).ok_or_else(|| {
                LuaError::Runtime(
                    "bad argument #2 to 'insert' (number has no integer representation)"
                        .to_string(),
                )
            })?;
            let val = args[2];

            // Validate: (pos - 1) as u64 < e as u64
            if (pos.wrapping_sub(1) as u64) >= (e as u64) {
                return Err(add_error_prefix(
                    vm,
                    LuaError::Runtime(
                        "bad argument #2 to 'insert' (position out of bounds)".to_string(),
                    ),
                ));
            }

            // Shift right: for (i = e; i > pos; i--) { t[i] = t[i-1]; }
            let mut i = e;
            while i > pos {
                let key_from = TValue::from_full_integer(i - 1, &mut vm.gc);
                let v = table_index(vm, table_val, key_from)?;
                let key_to = TValue::from_full_integer(i, &mut vm.gc);
                table_newindex(vm, table_val, key_to, v)?;
                i -= 1;
            }
            let key = TValue::from_full_integer(pos, &mut vm.gc);
            table_newindex(vm, table_val, key, val)?;
        }
        _ => {
            return Err(add_error_prefix(
                vm,
                LuaError::Runtime("wrong number of arguments to 'insert'".to_string()),
            ));
        }
    }
    Ok(vec![])
}

/// table.remove(t [,pos]) with full metamethod support
fn do_table_remove(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    let table_val = args.first().copied().unwrap_or(TValue::nil());
    let size = obj_len(vm, table_val)?;

    let pos = if args.len() > 1 {
        args[1].as_full_integer(&vm.gc).ok_or_else(|| {
            LuaError::Runtime(
                "bad argument #1 to 'remove' (number has no integer representation)".to_string(),
            )
        })?
    } else {
        size
    };

    // Validate: if pos != size, check (pos-1) as u64 <= size as u64
    if pos != size && (pos.wrapping_sub(1) as u64) > (size as u64) {
        return Err(add_error_prefix(
            vm,
            LuaError::Runtime("bad argument #1 to 'remove' (position out of bounds)".to_string()),
        ));
    }

    // result = t[pos]
    let key = TValue::from_full_integer(pos, &mut vm.gc);
    let removed = table_index(vm, table_val, key)?;

    // Shift left: for (; pos < size; pos++) { t[pos] = t[pos+1]; }
    let mut i = pos;
    while i < size {
        let key_from = TValue::from_full_integer(i + 1, &mut vm.gc);
        let v = table_index(vm, table_val, key_from)?;
        let key_to = TValue::from_full_integer(i, &mut vm.gc);
        table_newindex(vm, table_val, key_to, v)?;
        i += 1;
    }
    // t[pos] = nil (pos is now the last slot)
    let nil_key = TValue::from_full_integer(i, &mut vm.gc);
    table_newindex(vm, table_val, nil_key, TValue::nil())?;

    Ok(vec![removed])
}

/// table.concat(t [,sep [,i [,j]]]) with full metamethod support
fn do_table_concat(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    let table_val = args.first().copied().unwrap_or(TValue::nil());
    if table_val.as_table_idx().is_none() {
        return Err(add_error_prefix(
            vm,
            LuaError::Runtime(format!(
                "bad argument #1 to 'concat' (table expected, got {})",
                obj_type_name(table_val, vm)
            )),
        ));
    }

    let sep = if args.len() > 1 {
        let val = args[1];
        if let Some(sid) = val.as_string_id() {
            String::from_utf8_lossy(vm.strings.get_bytes(sid)).into_owned()
        } else if val.is_nil() {
            String::new()
        } else {
            return Err(add_error_prefix(
                vm,
                LuaError::Runtime("bad argument #2 to 'concat' (string expected)".to_string()),
            ));
        }
    } else {
        String::new()
    };

    let i = if args.len() > 2 {
        args[2].as_full_integer(&vm.gc).ok_or_else(|| {
            add_error_prefix(
                vm,
                LuaError::Runtime(
                    "bad argument #3 to 'concat' (number has no integer representation)"
                        .to_string(),
                ),
            )
        })?
    } else {
        1
    };

    let j = if args.len() > 3 {
        args[3].as_full_integer(&vm.gc).ok_or_else(|| {
            add_error_prefix(
                vm,
                LuaError::Runtime(
                    "bad argument #4 to 'concat' (number has no integer representation)"
                        .to_string(),
                ),
            )
        })?
    } else {
        obj_len(vm, table_val)?
    };

    let mut parts = Vec::new();
    let mut k = i;
    while k <= j {
        let key = TValue::from_full_integer(k, &mut vm.gc);
        let val = table_index(vm, table_val, key)?;
        if let Some(sid) = coerce::to_string_for_concat(val, &vm.gc, &mut vm.strings) {
            parts.push(String::from_utf8_lossy(vm.strings.get_bytes(sid)).into_owned());
        } else {
            return Err(add_error_prefix(
                vm,
                LuaError::Runtime(format!(
                    "invalid value (table) at index {} in table for 'concat'",
                    k
                )),
            ));
        }
        k = match k.checked_add(1) {
            Some(next) => next,
            None => break,
        };
    }

    let result = parts.join(&sep);
    let sid = vm.strings.intern_or_create(result.as_bytes());
    Ok(vec![TValue::from_string_id(sid)])
}

/// table.unpack(t [,i [,j]]) with full metamethod support
fn do_table_unpack(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    let table_val = args.first().copied().unwrap_or(TValue::nil());
    if table_val.as_table_idx().is_none() {
        return Err(add_error_prefix(
            vm,
            LuaError::Runtime(format!(
                "bad argument #1 to 'unpack' (table expected, got {})",
                obj_type_name(table_val, vm)
            )),
        ));
    }

    let i = if args.len() > 1 && !args[1].is_nil() {
        args[1].as_full_integer(&vm.gc).ok_or_else(|| {
            add_error_prefix(
                vm,
                LuaError::Runtime(
                    "bad argument #2 to 'unpack' (number has no integer representation)"
                        .to_string(),
                ),
            )
        })?
    } else {
        1
    };

    let j = if args.len() > 2 && !args[2].is_nil() {
        args[2].as_full_integer(&vm.gc).ok_or_else(|| {
            add_error_prefix(
                vm,
                LuaError::Runtime(
                    "bad argument #3 to 'unpack' (number has no integer representation)"
                        .to_string(),
                ),
            )
        })?
    } else {
        obj_len(vm, table_val)?
    };

    // Check for too many results
    if j >= i {
        let n = (j as i128) - (i as i128) + 1;
        if n > 1_000_000 {
            return Err(add_error_prefix(
                vm,
                LuaError::Runtime("too many results to unpack".to_string()),
            ));
        }
    }

    let mut results = Vec::new();
    let mut k = i;
    while k <= j {
        let key = TValue::from_full_integer(k, &mut vm.gc);
        let val = table_index(vm, table_val, key)?;
        results.push(val);
        if k == j {
            break;
        }
        k += 1;
    }
    Ok(results)
}

/// warn(msg1, msg2, ...) — warning system with @on/@off/@store/@normal control
fn do_warn(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    if args.is_empty() {
        return Err(add_error_prefix(
            vm,
            LuaError::Runtime(
                "bad argument #1 to 'warn' (string expected, got no value)".to_string(),
            ),
        ));
    }

    // Get first argument as string
    let first = args[0];
    let first_str = if let Some(sid) = first.as_string_id() {
        String::from_utf8_lossy(vm.strings.get_bytes(sid)).into_owned()
    } else if let Some(i) = first.as_full_integer(&vm.gc) {
        i.to_string()
    } else if let Some(f) = first.as_float() {
        format!("{}", f)
    } else {
        return Err(add_error_prefix(
            vm,
            LuaError::Runtime(format!(
                "bad argument #1 to 'warn' (string expected, got {})",
                obj_type_name(first, vm)
            )),
        ));
    };

    // Check for control messages (first arg starts with '@')
    if first_str.starts_with('@') {
        match first_str.as_str() {
            "@on" => {
                vm.warn_enabled = true;
            }
            "@off" => {
                vm.warn_enabled = false;
            }
            "@store" => {
                // Test-suite extension: store messages in _WARN global
                vm.warn_store = true;
                vm.warn_enabled = true;
            }
            "@normal" => {
                // Test-suite extension: switch back to stderr output
                vm.warn_store = false;
            }
            _ => {
                // Unknown control message: ignore (PUC behavior)
            }
        }
        return Ok(vec![]);
    }

    // Not a control message: concatenate all arguments
    if !vm.warn_enabled {
        return Ok(vec![]);
    }

    let mut message = first_str;
    for arg in &args[1..] {
        if let Some(sid) = arg.as_string_id() {
            message.push_str(&String::from_utf8_lossy(vm.strings.get_bytes(sid)));
        } else if let Some(i) = arg.as_full_integer(&vm.gc) {
            message.push_str(&i.to_string());
        } else if let Some(f) = arg.as_float() {
            message.push_str(&format!("{}", f));
        } else {
            return Err(add_error_prefix(
                vm,
                LuaError::Runtime("bad argument to 'warn' (string expected)".to_string()),
            ));
        }
    }

    if vm.warn_store {
        // Store in _WARN global
        if let Some(env_idx) = vm.env_idx {
            let warn_key = vm.strings.intern(b"_WARN");
            let warn_sid = vm.strings.intern_or_create(message.as_bytes());
            vm.gc
                .get_table_mut(env_idx)
                .raw_set_str(warn_key, TValue::from_string_id(warn_sid));
        }
    } else {
        // Output to stderr: "Lua warning: <message>\n"
        eprintln!("Lua warning: {}", message);
    }

    Ok(vec![])
}

// Hook mask constants
const HOOK_CALL: u8 = 1;
const HOOK_RETURN: u8 = 2;
const HOOK_LINE: u8 = 4;
const HOOK_COUNT: u8 = 8;

/// debug.sethook([thread,] hook, mask [, count])
fn do_debug_sethook(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    // Detect optional thread argument
    let mut target_coro_id: Option<usize> = None; // None = current thread
    let (hook_arg, mask_arg, count_arg) =
        if args.is_empty() || (args.len() == 1 && args[0].is_nil()) {
            (TValue::nil(), TValue::nil(), TValue::nil())
        } else if args.len() >= 2 {
            let is_thread = if let Some(tbl_idx) = args[0].as_table_idx() {
                if let Some(thread_mt) = vm.gc.thread_metatable {
                    if vm.gc.get_table(tbl_idx).metatable == Some(thread_mt) {
                        let id_val = vm.gc.get_table(tbl_idx).raw_geti(1);
                        let mut coro_id = id_val.as_integer().unwrap_or(-2);
                        if coro_id == -1 {
                            // Coroutine not yet allocated — allocate it now
                            let func = vm.gc.get_table(tbl_idx).raw_geti(2);
                            if func.is_function() {
                                coro_id = vm.create_coroutine(func) as i64;
                                vm.gc
                                    .get_table_mut(tbl_idx)
                                    .raw_seti(1, TValue::from_integer(coro_id));
                            }
                        }
                        if coro_id >= 0 {
                            target_coro_id = Some(coro_id as usize);
                        }
                        true
                    } else {
                        false
                    }
                } else {
                    false
                }
            } else {
                false
            };
            if is_thread {
                let h = args.get(1).copied().unwrap_or(TValue::nil());
                let m = args.get(2).copied().unwrap_or(TValue::nil());
                let c = args.get(3).copied().unwrap_or(TValue::nil());
                (h, m, c)
            } else {
                (
                    args[0],
                    args.get(1).copied().unwrap_or(TValue::nil()),
                    args.get(2).copied().unwrap_or(TValue::nil()),
                )
            }
        } else {
            (args[0], TValue::nil(), TValue::nil())
        };

    // Parse mask string
    let mut mask: u8 = 0;
    if !mask_arg.is_nil() {
        if let Some(sid) = mask_arg.as_string_id() {
            let bytes = vm.strings.get_bytes(sid);
            for &b in bytes {
                match b {
                    b'c' => mask |= HOOK_CALL,
                    b'r' => mask |= HOOK_RETURN,
                    b'l' => mask |= HOOK_LINE,
                    _ => {}
                }
            }
        } else {
            return Err(add_error_prefix(
                vm,
                LuaError::Runtime("bad argument #2 to 'sethook' (string expected)".to_string()),
            ));
        }
    }

    // Parse count (accept both integer and float-that-is-whole-number)
    let count = if let Some(n) = count_arg.as_full_integer(&vm.gc) {
        if n > 0 {
            n as u32
        } else {
            0
        }
    } else if let Some(f) = count_arg.as_float() {
        let n = f as i64;
        if n > 0 && (n as f64) == f {
            n as u32
        } else {
            0
        }
    } else {
        0
    };
    if count > 0 {
        mask |= HOOK_COUNT;
    }

    let hooks_active = mask != 0 && !hook_arg.is_nil();
    let final_mask = if hooks_active { mask } else { 0 };
    let final_func = if hooks_active {
        hook_arg
    } else {
        TValue::nil()
    };
    let final_count = if hooks_active { count } else { 0 };

    if let Some(coro_id) = target_coro_id {
        // Set hook on a specific coroutine
        if coro_id < vm.coroutines.len() {
            let coro = &mut vm.coroutines[coro_id];
            coro.hook_func = final_func;
            coro.hook_mask = final_mask;
            coro.hook_count = final_count;
            coro.hook_counter = final_count;
            coro.hooks_active = hooks_active;
            coro.hook_last_line = -1;
        }
    } else {
        // Set hook on current thread
        vm.hook_func = final_func;
        vm.hook_mask = final_mask;
        vm.hook_count = final_count;
        vm.hook_counter = final_count;
        vm.hooks_active = hooks_active;
        if final_mask & HOOK_LINE != 0 {
            let mut last_line = -1i32;
            if let Some(frame) = vm.call_stack.last() {
                if frame.is_lua() && frame.pc > 0 {
                    let proto = &vm.protos[frame.proto_idx];
                    last_line = proto.get_line(frame.pc - 1) as i32;
                }
            }
            vm.hook_last_line = last_line;
        } else {
            vm.hook_last_line = -1;
        }
    }

    Ok(vec![])
}

/// debug.gethook([thread])
fn do_debug_gethook(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    // Detect optional thread argument
    let first = args.first().copied().unwrap_or(TValue::nil());
    let coro_id = detect_thread_arg(vm, first).flatten();

    let (hook_func, hook_mask, hook_count) = if let Some(cid) = coro_id {
        if cid < vm.coroutines.len() {
            let coro = &vm.coroutines[cid];
            (coro.hook_func, coro.hook_mask, coro.hook_count)
        } else {
            (TValue::nil(), 0u8, 0u32)
        }
    } else {
        (vm.hook_func, vm.hook_mask, vm.hook_count)
    };

    if hook_func.is_nil() || hook_mask == 0 {
        return Ok(vec![TValue::nil(), TValue::nil(), TValue::from_integer(0)]);
    }

    // Build mask string
    let mut mask_str = String::new();
    if hook_mask & HOOK_CALL != 0 {
        mask_str.push('c');
    }
    if hook_mask & HOOK_RETURN != 0 {
        mask_str.push('r');
    }
    if hook_mask & HOOK_LINE != 0 {
        mask_str.push('l');
    }

    let mask_sid = vm.strings.intern_or_create(mask_str.as_bytes());
    Ok(vec![
        hook_func,
        TValue::from_string_id(mask_sid),
        TValue::from_integer(hook_count as i64),
    ])
}

/// debug.getlocal([thread,] level, local)
fn do_debug_getlocal(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    if args.is_empty() {
        return Ok(vec![TValue::nil()]);
    }

    // Detect optional thread argument
    let first = args[0];
    let thread_info = detect_thread_arg(vm, first);
    let is_thread = thread_info.is_some();
    let coro_id = thread_info.flatten();
    let (level_arg, local_arg) = if is_thread {
        if args.len() >= 3 {
            (args[1], args[2])
        } else {
            return Ok(vec![TValue::nil()]);
        }
    } else if args.len() >= 2 {
        (args[0], args[1])
    } else {
        return Ok(vec![TValue::nil()]);
    };

    // If first arg is a function (static query), return parameter name only
    if let Some(cl_idx) = level_arg.as_closure_idx() {
        let proto_idx = vm.gc.get_closure(cl_idx).proto_idx;
        let local_n = if let Some(n) = local_arg.as_full_integer(&vm.gc) {
            n
        } else {
            return Ok(vec![TValue::nil()]);
        };
        if local_n < 1 {
            return Ok(vec![TValue::nil()]);
        }
        let proto = &vm.protos[proto_idx];
        // For static query, find parameter names (params are the first local_vars with start_pc == 0)
        let mut param_count = 0i64;
        for lv in &proto.local_vars {
            if lv.start_pc == 0 {
                param_count += 1;
                if param_count == local_n {
                    let name_bytes = vm.strings.get_bytes(lv.name).to_vec();
                    let name_sid = vm.strings.intern_or_create(&name_bytes);
                    return Ok(vec![TValue::from_string_id(name_sid)]);
                }
            }
        }
        return Ok(vec![TValue::nil()]);
    }

    let level = if let Some(n) = level_arg.as_full_integer(&vm.gc) {
        n
    } else {
        return Ok(vec![TValue::nil()]);
    };
    let local_n = if let Some(n) = local_arg.as_full_integer(&vm.gc) {
        n
    } else {
        return Ok(vec![TValue::nil()]);
    };

    if level < 0 {
        return Ok(vec![TValue::nil()]);
    }
    let level = level as usize;

    if let Some(cid) = coro_id {
        // Querying a coroutine
        if cid >= vm.coroutines.len() {
            return Ok(vec![TValue::nil()]);
        }
        // For coroutines, level 0 = yield point (C), level 1 = top Lua frame
        if level == 0 {
            // C yield function — return temporaries
            if local_n < 1 {
                return Ok(vec![TValue::nil()]);
            }
            let temp_name = vm.strings.intern_or_create(b"(C temporary)");
            return Ok(vec![TValue::from_string_id(temp_name)]);
        }
        let coro_stack_len = vm.coroutines[cid].call_stack.len();
        if level > coro_stack_len {
            return Ok(vec![TValue::nil()]);
        }
        let frame_idx = coro_stack_len - level;
        let frame = vm.coroutines[cid].call_stack[frame_idx].clone();

        if !frame.is_lua() {
            if local_n < 1 {
                return Ok(vec![TValue::nil()]);
            }
            let stack_idx = frame.func_stack_idx + local_n as usize;
            let frame_top = if frame_idx + 1 < vm.coroutines[cid].call_stack.len() {
                vm.coroutines[cid].call_stack[frame_idx + 1].func_stack_idx
            } else {
                vm.coroutines[cid].stack_top
            };
            if stack_idx >= frame_top {
                return Ok(vec![TValue::nil()]);
            }
            let val = vm.coroutines[cid]
                .stack
                .get(stack_idx)
                .copied()
                .unwrap_or(TValue::nil());
            let temp_name = vm.strings.intern_or_create(b"(C temporary)");
            return Ok(vec![TValue::from_string_id(temp_name), val]);
        }

        let proto_idx = frame.proto_idx;
        let base = frame.base;
        let pc = if frame.pc > 0 { frame.pc - 1 } else { 0 };

        if local_n < 0 {
            if let Some(vararg_base) = frame.vararg_base {
                let vararg_idx = (-local_n) as usize;
                let num_params = vm.protos[proto_idx].num_params as usize;
                let vararg_start = vararg_base + num_params;
                let vararg_end = base;
                if vararg_start > vararg_end {
                    return Ok(vec![TValue::nil()]);
                }
                let vararg_count = vararg_end - vararg_start;
                if vararg_idx < 1 || vararg_idx > vararg_count {
                    return Ok(vec![TValue::nil()]);
                }
                let stack_idx = vararg_start + (vararg_idx - 1);
                let name_sid = vm.strings.intern_or_create(b"(vararg)");
                let val = vm.coroutines[cid]
                    .stack
                    .get(stack_idx)
                    .copied()
                    .unwrap_or(TValue::nil());
                return Ok(vec![TValue::from_string_id(name_sid), val]);
            }
            return Ok(vec![TValue::nil()]);
        }

        if local_n < 1 {
            return Ok(vec![TValue::nil()]);
        }

        let proto = &vm.protos[proto_idx];
        let mut count = 0i64;
        for lv in &proto.local_vars {
            if (lv.start_pc as usize) <= pc && pc < (lv.end_pc as usize) {
                count += 1;
                if count == local_n {
                    let name_bytes = vm.strings.get_bytes(lv.name).to_vec();
                    let name_sid = vm.strings.intern_or_create(&name_bytes);
                    let stack_idx = base + lv.reg as usize;
                    let val = vm.coroutines[cid]
                        .stack
                        .get(stack_idx)
                        .copied()
                        .unwrap_or(TValue::nil());
                    return Ok(vec![TValue::from_string_id(name_sid), val]);
                }
            }
        }

        return Ok(vec![TValue::nil()]);
    }

    // Querying the current thread
    // Level 0 = getlocal itself (C function) — return its own args as temporaries
    if level == 0 {
        if local_n < 1 || local_n as usize > args.len() {
            return Ok(vec![TValue::nil()]);
        }
        let temp_name = vm.strings.intern_or_create(b"(C temporary)");
        let val = args[(local_n - 1) as usize];
        return Ok(vec![TValue::from_string_id(temp_name), val]);
    }
    let stack_len = vm.call_stack.len();
    if level > stack_len {
        return Err(add_error_prefix(
            vm,
            LuaError::Runtime("bad argument #1 to 'getlocal' (level out of range)".to_string()),
        ));
    }
    let frame_idx = stack_len - level;
    let frame = &vm.call_stack[frame_idx];

    if !frame.is_lua() {
        // For C/native frames, return temporaries from the stack
        if local_n < 1 {
            return Ok(vec![TValue::nil()]);
        }
        let stack_idx = frame.func_stack_idx + local_n as usize;
        let frame_top = if frame_idx + 1 < vm.call_stack.len() {
            vm.call_stack[frame_idx + 1].func_stack_idx
        } else {
            vm.stack_top
        };
        if stack_idx >= frame_top {
            return Ok(vec![TValue::nil()]);
        }
        let val = vm.stack.get(stack_idx).copied().unwrap_or(TValue::nil());
        let temp_name = vm.strings.intern_or_create(b"(C temporary)");
        return Ok(vec![TValue::from_string_id(temp_name), val]);
    }

    let proto_idx = frame.proto_idx;
    let base = frame.base;
    let pc = if frame.pc > 0 { frame.pc - 1 } else { 0 };

    if local_n < 0 {
        // Negative index = varargs
        if let Some(vararg_base) = frame.vararg_base {
            let vararg_idx = (-local_n) as usize;
            let num_params = vm.protos[proto_idx].num_params as usize;
            let vararg_start = vararg_base + num_params;
            let vararg_end = base;
            if vararg_start > vararg_end {
                return Ok(vec![TValue::nil()]);
            }
            let vararg_count = vararg_end - vararg_start;
            if vararg_idx < 1 || vararg_idx > vararg_count {
                return Ok(vec![TValue::nil()]);
            }
            let stack_idx = vararg_start + (vararg_idx - 1);
            let name_sid = vm.strings.intern_or_create(b"(vararg)");
            let val = vm.stack.get(stack_idx).copied().unwrap_or(TValue::nil());
            return Ok(vec![TValue::from_string_id(name_sid), val]);
        }
        return Ok(vec![TValue::nil()]);
    }

    if local_n < 1 {
        return Ok(vec![TValue::nil()]);
    }

    // Find the local_n-th active local at pc
    let proto = &vm.protos[proto_idx];
    let mut count = 0i64;
    for lv in &proto.local_vars {
        if (lv.start_pc as usize) <= pc && pc < (lv.end_pc as usize) {
            count += 1;
            if count == local_n {
                let name_bytes = vm.strings.get_bytes(lv.name).to_vec();
                let name_sid = vm.strings.intern_or_create(&name_bytes);
                let stack_idx = base + lv.reg as usize;
                let val = vm.stack.get(stack_idx).copied().unwrap_or(TValue::nil());
                return Ok(vec![TValue::from_string_id(name_sid), val]);
            }
        }
    }

    // Check for temporaries (registers beyond named locals) — current thread only
    if local_n > count {
        let reg = (local_n - 1) as usize;
        let frame_top = if frame_idx + 1 < vm.call_stack.len() {
            vm.call_stack[frame_idx + 1].func_stack_idx
        } else {
            vm.stack_top
        };
        let stack_idx = base + reg;
        if stack_idx < frame_top {
            let temp_name = vm.strings.intern_or_create(b"(temporary)");
            let val = vm.stack.get(stack_idx).copied().unwrap_or(TValue::nil());
            return Ok(vec![TValue::from_string_id(temp_name), val]);
        }
    }

    Ok(vec![TValue::nil()])
}

/// debug.setlocal([thread,] level, local, value)
fn do_debug_setlocal(vm: &mut Vm, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
    if args.len() < 3 {
        return Ok(vec![TValue::nil()]);
    }

    // Detect optional thread argument
    let first = args[0];
    let thread_info = detect_thread_arg(vm, first);
    let is_thread = thread_info.is_some();
    let coro_id = thread_info.flatten();
    let (level_arg, local_arg, value_arg) = if is_thread {
        if args.len() >= 4 {
            (args[1], args[2], args[3])
        } else {
            (args[0], args[1], args[2])
        }
    } else {
        (args[0], args[1], args[2])
    };

    let level = if let Some(n) = level_arg.as_full_integer(&vm.gc) {
        n
    } else {
        return Ok(vec![TValue::nil()]);
    };
    let local_n = if let Some(n) = local_arg.as_full_integer(&vm.gc) {
        n
    } else {
        return Ok(vec![TValue::nil()]);
    };

    if level < 1 {
        return Err(add_error_prefix(
            vm,
            LuaError::Runtime("bad argument #1 to 'setlocal' (level out of range)".to_string()),
        ));
    }
    let level = level as usize;

    if let Some(cid) = coro_id {
        // Setting local in a coroutine
        if cid >= vm.coroutines.len() {
            return Ok(vec![TValue::nil()]);
        }
        let coro_stack_len = vm.coroutines[cid].call_stack.len();
        if level > coro_stack_len {
            return Ok(vec![TValue::nil()]);
        }
        let frame_idx = coro_stack_len - level;
        let frame = vm.coroutines[cid].call_stack[frame_idx].clone();

        if !frame.is_lua() {
            return Ok(vec![TValue::nil()]);
        }

        let proto_idx = frame.proto_idx;
        let base = frame.base;
        let pc = if frame.pc > 0 { frame.pc - 1 } else { 0 };

        if local_n < 0 {
            if let Some(vararg_base) = frame.vararg_base {
                let vararg_idx = (-local_n) as usize;
                let num_params = vm.protos[proto_idx].num_params as usize;
                let vararg_start = vararg_base + num_params;
                let vararg_end = base;
                if vararg_start > vararg_end {
                    return Ok(vec![TValue::nil()]);
                }
                let vararg_count = vararg_end - vararg_start;
                if vararg_idx < 1 || vararg_idx > vararg_count {
                    return Ok(vec![TValue::nil()]);
                }
                let stack_idx = vararg_start + (vararg_idx - 1);
                let name_sid = vm.strings.intern_or_create(b"(vararg)");
                if stack_idx < vm.coroutines[cid].stack.len() {
                    vm.coroutines[cid].stack[stack_idx] = value_arg;
                }
                return Ok(vec![TValue::from_string_id(name_sid)]);
            }
            return Ok(vec![TValue::nil()]);
        }

        if local_n < 1 {
            return Ok(vec![TValue::nil()]);
        }

        let proto = &vm.protos[proto_idx];
        let mut count = 0i64;
        for lv in &proto.local_vars {
            if (lv.start_pc as usize) <= pc && pc < (lv.end_pc as usize) {
                count += 1;
                if count == local_n {
                    let name_bytes = vm.strings.get_bytes(lv.name).to_vec();
                    let name_sid = vm.strings.intern_or_create(&name_bytes);
                    let stack_idx = base + lv.reg as usize;
                    if stack_idx < vm.coroutines[cid].stack.len() {
                        vm.coroutines[cid].stack[stack_idx] = value_arg;
                    }
                    return Ok(vec![TValue::from_string_id(name_sid)]);
                }
            }
        }

        return Ok(vec![TValue::nil()]);
    }

    // Current thread
    let stack_len = vm.call_stack.len();
    if level > stack_len {
        return Err(add_error_prefix(
            vm,
            LuaError::Runtime("bad argument #1 to 'setlocal' (level out of range)".to_string()),
        ));
    }
    let frame_idx = stack_len - level;
    let frame = &vm.call_stack[frame_idx];

    if !frame.is_lua() {
        return Ok(vec![TValue::nil()]);
    }

    let proto_idx = frame.proto_idx;
    let base = frame.base;
    let pc = if frame.pc > 0 { frame.pc - 1 } else { 0 };

    if local_n < 0 {
        // Negative index = set varargs
        if let Some(vararg_base) = frame.vararg_base {
            let vararg_idx = (-local_n) as usize;
            let num_params = vm.protos[proto_idx].num_params as usize;
            let vararg_start = vararg_base + num_params;
            let vararg_end = base;
            if vararg_start > vararg_end {
                return Ok(vec![TValue::nil()]);
            }
            let vararg_count = vararg_end - vararg_start;
            if vararg_idx < 1 || vararg_idx > vararg_count {
                return Ok(vec![TValue::nil()]);
            }
            let stack_idx = vararg_start + (vararg_idx - 1);
            let name_sid = vm.strings.intern_or_create(b"(vararg)");
            if stack_idx < vm.stack.len() {
                vm.stack[stack_idx] = value_arg;
            }
            return Ok(vec![TValue::from_string_id(name_sid)]);
        }
        return Ok(vec![TValue::nil()]);
    }

    if local_n < 1 {
        return Ok(vec![TValue::nil()]);
    }

    let proto = &vm.protos[proto_idx];
    let mut count = 0i64;
    for lv in &proto.local_vars {
        if (lv.start_pc as usize) <= pc && pc < (lv.end_pc as usize) {
            count += 1;
            if count == local_n {
                let name_bytes = vm.strings.get_bytes(lv.name).to_vec();
                let name_sid = vm.strings.intern_or_create(&name_bytes);
                let stack_idx = base + lv.reg as usize;
                if stack_idx < vm.stack.len() {
                    vm.stack[stack_idx] = value_arg;
                }
                return Ok(vec![TValue::from_string_id(name_sid)]);
            }
        }
    }

    // Check for temporaries (registers beyond named locals) — current thread only
    if local_n > count {
        let reg = (local_n - 1) as usize;
        let frame_top = if frame_idx + 1 < vm.call_stack.len() {
            vm.call_stack[frame_idx + 1].func_stack_idx
        } else {
            vm.stack_top
        };
        let stack_idx = base + reg;
        if stack_idx < frame_top && stack_idx < vm.stack.len() {
            let temp_name = vm.strings.intern_or_create(b"(temporary)");
            vm.stack[stack_idx] = value_arg;
            return Ok(vec![TValue::from_string_id(temp_name)]);
        }
    }

    Ok(vec![TValue::nil()])
}

/// debug.getregistry()
fn do_debug_getregistry(vm: &mut Vm) -> Result<Vec<TValue>, LuaError> {
    // Create registry table lazily
    if vm.registry_idx.is_none() {
        let reg = vm.gc.alloc_table(0, 4);
        // Create _HOOKKEY table with weak-key metatable
        let hookkey = vm.gc.alloc_table(0, 0);
        let mt = vm.gc.alloc_table(0, 1);
        let mode_key = vm.strings.intern(b"__mode");
        let mode_val = vm.strings.intern_or_create(b"k");
        vm.gc
            .get_table_mut(mt)
            .raw_set_str(mode_key, TValue::from_string_id(mode_val));
        vm.gc.get_table_mut(hookkey).metatable = Some(mt);
        let hookkey_key = vm.strings.intern(b"_HOOKKEY");
        vm.gc
            .get_table_mut(reg)
            .raw_set_str(hookkey_key, TValue::from_table(hookkey));
        vm.registry_idx = Some(reg);
    }
    Ok(vec![TValue::from_table(vm.registry_idx.unwrap())])
}

/// PUC-style changedline: check if any instruction between old_pc and new_pc
/// has a non-zero line delta. This catches same-line backward jumps in loops.
/// PUC's changedline: returns true if the line at old_pc differs from line at new_pc.
/// Only called for forward movement (new_pc > old_pc). Uses line delta accumulation
/// like PUC Lua — if net delta from old_pc to new_pc is non-zero, line changed.
fn changedline(proto: &selune_compiler::proto::Proto, old_pc: usize, new_pc: usize) -> bool {
    if new_pc <= old_pc {
        return false;
    }
    // Compare lines at old_pc and new_pc directly
    proto.get_line(old_pc) != proto.get_line(new_pc)
}

/// Fire a hook event. `event` is "call", "return", "line", "count", "tail call".
/// For line events, `line` is the line number; for others, -1.
fn fire_hook(vm: &mut Vm, event: &str, line: i32, _entry_depth: usize) -> Result<(), LuaError> {
    if vm.in_hook || vm.hook_func.is_nil() {
        return Ok(());
    }

    // Temporarily advance the target frame's pc so that debug.getinfo(level)
    // with `frame.pc - 1` correctly points to the current instruction.
    // (In our dispatch loop, pc hasn't been advanced yet when hooks fire.)
    let target_ci_idx = vm.call_stack.len() - 1;
    let target_is_lua = vm.call_stack[target_ci_idx].is_lua();
    if target_is_lua {
        vm.call_stack[target_ci_idx].pc += 1;
    }

    vm.in_hook = true;
    vm.pending_hook_call = true;
    let event_sid = vm.strings.intern_or_create(event.as_bytes());
    let event_val = TValue::from_string_id(event_sid);
    let line_val = if line >= 0 {
        TValue::from_integer(line as i64)
    } else {
        TValue::nil()
    };
    let args = vec![event_val, line_val];
    let hook_func = vm.hook_func;
    let result = call_function(vm, hook_func, &args);
    vm.in_hook = false;

    // Restore pc so the instruction still executes
    if target_is_lua && target_ci_idx < vm.call_stack.len() {
        vm.call_stack[target_ci_idx].pc -= 1;
    }

    match result {
        Ok(_) => Ok(()),
        Err(e) => Err(e),
    }
}
