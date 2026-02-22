//! Main bytecode dispatch loop.

use crate::arith::{self, ArithOp};
use crate::callinfo::CallInfo;
use crate::coerce;
use crate::compare;
use crate::error::LuaError;
use crate::metamethod;
use crate::vm::Vm;
use selune_compiler::opcode::OpCode;
use selune_compiler::proto::{Constant, Proto};
use selune_core::gc::{NativeContext, NativeError};
use selune_core::value::TValue;

/// Helper macro to get current proto without borrowing all of vm.
macro_rules! proto {
    ($vm:expr, $ci_idx:expr) => {
        &$vm.protos[$vm.call_stack[$ci_idx].proto_idx]
    };
}

/// Get a constant from the current proto, cloned to avoid borrow issues.
#[inline]
fn get_k(vm: &Vm, ci_idx: usize, idx: usize) -> Constant {
    vm.protos[vm.call_stack[ci_idx].proto_idx].constants[idx].clone()
}

/// Convert a constant to TValue using get_k to avoid borrow conflicts.
#[inline]
#[allow(dead_code)]
fn k_to_tvalue(vm: &mut Vm, ci_idx: usize, idx: usize) -> TValue {
    let k = get_k(vm, ci_idx, idx);
    constant_to_tvalue(&k, &mut vm.gc)
}

/// Execute starting from proto at the given index, returning results.
pub fn execute(vm: &mut Vm, _start_proto_idx: usize) -> Result<Vec<TValue>, LuaError> {
    execute_from(vm, 1)
}

/// Execute the dispatch loop, returning when call_stack depth drops to entry_depth.
pub fn execute_from(vm: &mut Vm, entry_depth: usize) -> Result<Vec<TValue>, LuaError> {
    loop {
        let ci_idx = vm.call_stack.len() - 1;
        let base = vm.call_stack[ci_idx].base;

        let pc = vm.call_stack[ci_idx].pc;
        if pc >= proto!(vm, ci_idx).code.len() {
            // Fell off the end — return empty
            if vm.call_stack.len() <= entry_depth {
                return Ok(vec![]);
            }
            // Return from nested call
            let results = vec![];
            return_from_call(vm, &results)?;
            continue;
        }

        let inst = proto!(vm, ci_idx).code[pc];
        let op = inst.opcode();
        let a = inst.a() as usize;

        // Advance PC
        vm.call_stack[ci_idx].pc += 1;

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
                let proto = proto!(vm, ci_idx);
                let val = constant_to_tvalue(&proto.constants[bx], &mut vm.gc);
                vm.stack[base + a] = val;
            }

            OpCode::LoadKX => {
                let proto = proto!(vm, ci_idx);
                let next_inst = proto.code[vm.call_stack[ci_idx].pc];
                vm.call_stack[ci_idx].pc += 1;
                let ax = next_inst.ax_field() as usize;
                let val = constant_to_tvalue(&proto.constants[ax], &mut vm.gc);
                vm.stack[base + a] = val;
            }

            OpCode::LoadFalse => {
                vm.stack[base + a] = TValue::from_bool(false);
            }

            OpCode::LFalseSkip => {
                vm.stack[base + a] = TValue::from_bool(false);
                vm.call_stack[ci_idx].pc += 1;
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

            // ---- Arithmetic (register-register) ----
            // On success: store result and skip next MMBIN instruction.
            // On NeedMetamethod: don't skip, let MMBIN handle it.
            OpCode::Add
            | OpCode::Sub
            | OpCode::Mul
            | OpCode::Mod
            | OpCode::Pow
            | OpCode::Div
            | OpCode::IDiv => {
                let b = inst.b() as usize;
                let c = inst.c() as usize;
                let vb = vm.stack[base + b];
                let vc = vm.stack[base + c];
                let aop = match op {
                    OpCode::Add => ArithOp::Add,
                    OpCode::Sub => ArithOp::Sub,
                    OpCode::Mul => ArithOp::Mul,
                    OpCode::Mod => ArithOp::Mod,
                    OpCode::Pow => ArithOp::Pow,
                    OpCode::Div => ArithOp::Div,
                    _ => ArithOp::IDiv,
                };
                match arith::arith_op(aop, vb, vc, &mut vm.gc, &vm.strings) {
                    arith::ArithResult::Ok(result) => {
                        vm.stack[base + a] = result;
                        vm.call_stack[ci_idx].pc += 1; // skip MMBin
                    }
                    arith::ArithResult::NeedMetamethod => {} // fall through to MMBin
                    arith::ArithResult::Error(e) => return Err(e),
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
                        vm.call_stack[ci_idx].pc += 1; // skip MMBin
                    }
                    arith::ArithResult::NeedMetamethod => {} // fall through to MMBin
                    arith::ArithResult::Error(e) => return Err(e),
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
                let proto = proto!(vm, ci_idx);
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
                        vm.call_stack[ci_idx].pc += 1; // skip MMBinK
                    }
                    arith::ArithResult::NeedMetamethod => {} // fall through to MMBinK
                    arith::ArithResult::Error(e) => return Err(e),
                }
            }
            OpCode::BAndK | OpCode::BOrK | OpCode::BXorK => {
                let b = inst.b() as usize;
                let c = inst.c() as usize;
                let vb = vm.stack[base + b];
                let proto = proto!(vm, ci_idx);
                let vc = constant_to_tvalue(&proto.constants[c], &mut vm.gc);
                let aop = match op {
                    OpCode::BAndK => ArithOp::BAnd,
                    OpCode::BOrK => ArithOp::BOr,
                    _ => ArithOp::BXor,
                };
                match arith::bitwise_op(aop, vb, vc, &mut vm.gc, &vm.strings) {
                    arith::ArithResult::Ok(result) => {
                        vm.stack[base + a] = result;
                        vm.call_stack[ci_idx].pc += 1; // skip MMBinK
                    }
                    arith::ArithResult::NeedMetamethod => {} // fall through to MMBinK
                    arith::ArithResult::Error(e) => return Err(e),
                }
            }

            // ---- Arithmetic (register + immediate) ----
            OpCode::AddI => {
                let b = inst.b() as usize;
                let sc = inst.c() as i8 as i64;
                let vb = vm.stack[base + b];
                let imm = TValue::from_full_integer(sc, &mut vm.gc);
                match arith::arith_op(ArithOp::Add, vb, imm, &mut vm.gc, &vm.strings) {
                    arith::ArithResult::Ok(result) => {
                        vm.stack[base + a] = result;
                        vm.call_stack[ci_idx].pc += 1; // skip MMBinI
                    }
                    arith::ArithResult::NeedMetamethod => {}
                    arith::ArithResult::Error(e) => return Err(e),
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
                            let result = call_function(vm, mm_func, &[vb, imm])?;
                            vm.stack[base + a] =
                                result.first().copied().unwrap_or(TValue::nil());
                        } else {
                            return Err(LuaError::Runtime(format!(
                                "attempt to perform bitwise operation on a {} value",
                                selune_core::object::lua_type_name(vb, &vm.gc)
                            )));
                        }
                    }
                    arith::ArithResult::Error(e) => return Err(e),
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
                            let result = call_function(vm, mm_func, &[vb, imm])?;
                            vm.stack[base + a] =
                                result.first().copied().unwrap_or(TValue::nil());
                        } else {
                            return Err(LuaError::Runtime(format!(
                                "attempt to perform bitwise operation on a {} value",
                                selune_core::object::lua_type_name(vb, &vm.gc)
                            )));
                        }
                    }
                    arith::ArithResult::Error(e) => return Err(e),
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
                            let result = call_function(vm, mm, &[vb])?;
                            vm.stack[base + a] =
                                result.first().copied().unwrap_or(TValue::nil());
                        } else {
                            return Err(LuaError::Runtime(format!(
                                "attempt to perform arithmetic on a {} value",
                                selune_core::object::lua_type_name(vb, &vm.gc)
                            )));
                        }
                    }
                    arith::ArithResult::Error(e) => return Err(e),
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
                            let result = call_function(vm, mm, &[vb])?;
                            vm.stack[base + a] =
                                result.first().copied().unwrap_or(TValue::nil());
                        } else {
                            return Err(LuaError::Runtime(format!(
                                "attempt to perform bitwise operation on a {} value",
                                selune_core::object::lua_type_name(vb, &vm.gc)
                            )));
                        }
                    }
                    arith::ArithResult::Error(e) => return Err(e),
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
                        let result = call_function(vm, mm, &[vb])?;
                        vm.stack[base + a] = result.first().copied().unwrap_or(TValue::nil());
                    } else {
                        let table_idx = vb.as_table_idx().unwrap();
                        let len = vm.gc.get_table(table_idx).length();
                        vm.stack[base + a] = TValue::from_full_integer(len, &mut vm.gc);
                    }
                } else {
                    return Err(LuaError::Runtime(format!(
                        "attempt to get length of a {} value",
                        selune_core::object::lua_type_name(vb, &vm.gc)
                    )));
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
                        // Find first non-string/non-number value and try __concat
                        let mm_name = vm.mm_names.as_ref().unwrap().concat;
                        // Binary fold from left: ((a .. b) .. c) .. d
                        let mut accum = values[0];
                        for &val in &values[1..] {
                            // Try raw concat of pair first
                            match arith::lua_concat(&[accum, val], &vm.gc, &mut vm.strings) {
                                arith::ArithResult::Ok(result) => {
                                    accum = result;
                                }
                                _ => {
                                    // Try metamethod on left operand, then right
                                    let mm = metamethod::get_metamethod(accum, mm_name, &vm.gc)
                                        .or_else(|| {
                                            metamethod::get_metamethod(val, mm_name, &vm.gc)
                                        });
                                    if let Some(mm_func) = mm {
                                        let result =
                                            call_function(vm, mm_func, &[accum, val])?;
                                        accum = result
                                            .first()
                                            .copied()
                                            .unwrap_or(TValue::nil());
                                    } else {
                                        return Err(LuaError::Runtime(format!(
                                            "attempt to concatenate a {} value",
                                            selune_core::object::lua_type_name(
                                                accum, &vm.gc
                                            )
                                        )));
                                    }
                                }
                            }
                        }
                        vm.stack[base + a] = accum;
                    }
                    arith::ArithResult::Error(e) => return Err(e),
                }
            }

            // ---- Metamethod dispatch (MMBin/MMBinI/MMBinK) ----
            OpCode::MMBin => {
                // A = left operand reg, B = right operand reg, C = metamethod index
                let b_reg = inst.b() as usize;
                let mm_idx = inst.c() as u8;
                let va = vm.stack[base + a];
                let vb = vm.stack[base + b_reg];
                let mm_name = vm.mm_names.as_ref().unwrap().from_mm_index(mm_idx);
                // Try left operand's metamethod, then right
                let mm = metamethod::get_metamethod(va, mm_name, &vm.gc)
                    .or_else(|| metamethod::get_metamethod(vb, mm_name, &vm.gc));
                if let Some(mm_func) = mm {
                    let result = call_function(vm, mm_func, &[va, vb])?;
                    // Destination = previous instruction's A field
                    let prev_inst =
                        proto!(vm, ci_idx).code[vm.call_stack[ci_idx].pc - 2];
                    let dest = prev_inst.a() as usize;
                    vm.stack[base + dest] =
                        result.first().copied().unwrap_or(TValue::nil());
                } else {
                    return Err(LuaError::Runtime(format!(
                        "attempt to perform {} on a {} value",
                        mm_op_description(mm_idx),
                        selune_core::object::lua_type_name(va, &vm.gc)
                    )));
                }
            }
            OpCode::MMBinI => {
                // A = left operand reg, sB = immediate, C = metamethod index, k = flip
                let sb = inst.b() as i8 as i64;
                let mm_idx = inst.c() as u8;
                let k_flip = inst.k();
                let va = vm.stack[base + a];
                let vb = TValue::from_full_integer(sb, &mut vm.gc);
                let mm_name = vm.mm_names.as_ref().unwrap().from_mm_index(mm_idx);
                // If k_flip, the original operation was `imm op reg` so swap
                let (left, right) = if k_flip { (vb, va) } else { (va, vb) };
                let mm = metamethod::get_metamethod(left, mm_name, &vm.gc)
                    .or_else(|| metamethod::get_metamethod(right, mm_name, &vm.gc));
                if let Some(mm_func) = mm {
                    let result = call_function(vm, mm_func, &[left, right])?;
                    let prev_inst =
                        proto!(vm, ci_idx).code[vm.call_stack[ci_idx].pc - 2];
                    let dest = prev_inst.a() as usize;
                    vm.stack[base + dest] =
                        result.first().copied().unwrap_or(TValue::nil());
                } else {
                    return Err(LuaError::Runtime(format!(
                        "attempt to perform {} on a {} value",
                        mm_op_description(mm_idx),
                        selune_core::object::lua_type_name(va, &vm.gc)
                    )));
                }
            }
            OpCode::MMBinK => {
                // A = left operand reg, B = constant index, C = metamethod index, k = flip
                let b_k = inst.b() as usize;
                let mm_idx = inst.c() as u8;
                let k_flip = inst.k();
                let va = vm.stack[base + a];
                let proto = proto!(vm, ci_idx);
                let vb = constant_to_tvalue(&proto.constants[b_k], &mut vm.gc);
                let mm_name = vm.mm_names.as_ref().unwrap().from_mm_index(mm_idx);
                let (left, right) = if k_flip { (vb, va) } else { (va, vb) };
                let mm = metamethod::get_metamethod(left, mm_name, &vm.gc)
                    .or_else(|| metamethod::get_metamethod(right, mm_name, &vm.gc));
                if let Some(mm_func) = mm {
                    let result = call_function(vm, mm_func, &[left, right])?;
                    let prev_inst =
                        proto!(vm, ci_idx).code[vm.call_stack[ci_idx].pc - 2];
                    let dest = prev_inst.a() as usize;
                    vm.stack[base + dest] =
                        result.first().copied().unwrap_or(TValue::nil());
                } else {
                    return Err(LuaError::Runtime(format!(
                        "attempt to perform {} on a {} value",
                        mm_op_description(mm_idx),
                        selune_core::object::lua_type_name(va, &vm.gc)
                    )));
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
                    if let Some(mm) =
                        metamethod::get_metamethod(va, mm_name, &vm.gc)
                            .or_else(|| metamethod::get_metamethod(vb, mm_name, &vm.gc))
                    {
                        let res = call_function(vm, mm, &[va, vb])?;
                        !res.first().copied().unwrap_or(TValue::nil()).is_falsy()
                    } else {
                        eq
                    }
                } else {
                    eq
                };
                if result != k {
                    vm.call_stack[ci_idx].pc += 1;
                }
            }
            OpCode::Lt => {
                let b = inst.b() as usize;
                let k = inst.k();
                let va = vm.stack[base + a];
                let vb = vm.stack[base + b];
                let result = match compare::lua_lt(va, vb, &vm.gc, &vm.strings) {
                    compare::CompareResult::Ok(v) => v,
                    compare::CompareResult::NeedMetamethod => {
                        let mm_name = vm.mm_names.as_ref().unwrap().lt;
                        if let Some(mm) =
                            metamethod::get_metamethod(va, mm_name, &vm.gc)
                                .or_else(|| metamethod::get_metamethod(vb, mm_name, &vm.gc))
                        {
                            let res = call_function(vm, mm, &[va, vb])?;
                            !res.first().copied().unwrap_or(TValue::nil()).is_falsy()
                        } else {
                            return Err(LuaError::Runtime(format!(
                                "attempt to compare two {} values",
                                selune_core::object::lua_type_name(va, &vm.gc)
                            )));
                        }
                    }
                };
                if result != k {
                    vm.call_stack[ci_idx].pc += 1;
                }
            }
            OpCode::Le => {
                let b = inst.b() as usize;
                let k = inst.k();
                let va = vm.stack[base + a];
                let vb = vm.stack[base + b];
                let result = match compare::lua_le(va, vb, &vm.gc, &vm.strings) {
                    compare::CompareResult::Ok(v) => v,
                    compare::CompareResult::NeedMetamethod => {
                        let mm_name = vm.mm_names.as_ref().unwrap().le;
                        if let Some(mm) =
                            metamethod::get_metamethod(va, mm_name, &vm.gc)
                                .or_else(|| metamethod::get_metamethod(vb, mm_name, &vm.gc))
                        {
                            let res = call_function(vm, mm, &[va, vb])?;
                            !res.first().copied().unwrap_or(TValue::nil()).is_falsy()
                        } else {
                            return Err(LuaError::Runtime(format!(
                                "attempt to compare two {} values",
                                selune_core::object::lua_type_name(va, &vm.gc)
                            )));
                        }
                    }
                };
                if result != k {
                    vm.call_stack[ci_idx].pc += 1;
                }
            }
            OpCode::EqK => {
                let b = inst.b() as usize;
                let k = inst.k();
                let va = vm.stack[base + a];
                let proto = proto!(vm, ci_idx);
                let vb = constant_to_tvalue(&proto.constants[b], &mut vm.gc);
                let (eq, _) = compare::lua_eq(va, vb, &vm.gc, &vm.strings);
                if eq != k {
                    vm.call_stack[ci_idx].pc += 1;
                }
            }
            OpCode::EqI => {
                let sb = inst.b() as i8 as i64;
                let k = inst.k();
                let va = vm.stack[base + a];
                let imm = TValue::from_full_integer(sb, &mut vm.gc);
                let (eq, _) = compare::lua_eq(va, imm, &vm.gc, &vm.strings);
                if eq != k {
                    vm.call_stack[ci_idx].pc += 1;
                }
            }
            OpCode::LtI => {
                let sb = inst.b() as i8 as i64;
                let k = inst.k();
                let va = vm.stack[base + a];
                let imm = TValue::from_full_integer(sb, &mut vm.gc);
                let result = match compare::lua_lt(va, imm, &vm.gc, &vm.strings) {
                    compare::CompareResult::Ok(v) => v,
                    compare::CompareResult::NeedMetamethod => {
                        return Err(LuaError::Runtime(format!(
                            "attempt to compare two {} values",
                            selune_core::object::lua_type_name(va, &vm.gc)
                        )));
                    }
                };
                if result != k {
                    vm.call_stack[ci_idx].pc += 1;
                }
            }
            OpCode::LeI => {
                let sb = inst.b() as i8 as i64;
                let k = inst.k();
                let va = vm.stack[base + a];
                let imm = TValue::from_full_integer(sb, &mut vm.gc);
                let result = match compare::lua_le(va, imm, &vm.gc, &vm.strings) {
                    compare::CompareResult::Ok(v) => v,
                    compare::CompareResult::NeedMetamethod => {
                        return Err(LuaError::Runtime(format!(
                            "attempt to compare two {} values",
                            selune_core::object::lua_type_name(va, &vm.gc)
                        )));
                    }
                };
                if result != k {
                    vm.call_stack[ci_idx].pc += 1;
                }
            }
            OpCode::GtI => {
                let sb = inst.b() as i8 as i64;
                let k = inst.k();
                let va = vm.stack[base + a];
                let imm = TValue::from_full_integer(sb, &mut vm.gc);
                let result = match compare::lua_lt(imm, va, &vm.gc, &vm.strings) {
                    compare::CompareResult::Ok(v) => v,
                    compare::CompareResult::NeedMetamethod => {
                        return Err(LuaError::Runtime(format!(
                            "attempt to compare two {} values",
                            selune_core::object::lua_type_name(va, &vm.gc)
                        )));
                    }
                };
                if result != k {
                    vm.call_stack[ci_idx].pc += 1;
                }
            }
            OpCode::GeI => {
                let sb = inst.b() as i8 as i64;
                let k = inst.k();
                let va = vm.stack[base + a];
                let imm = TValue::from_full_integer(sb, &mut vm.gc);
                let result = match compare::lua_le(imm, va, &vm.gc, &vm.strings) {
                    compare::CompareResult::Ok(v) => v,
                    compare::CompareResult::NeedMetamethod => {
                        return Err(LuaError::Runtime(format!(
                            "attempt to compare two {} values",
                            selune_core::object::lua_type_name(va, &vm.gc)
                        )));
                    }
                };
                if result != k {
                    vm.call_stack[ci_idx].pc += 1;
                }
            }
            OpCode::Test => {
                let k = inst.k();
                let va = vm.stack[base + a];
                if va.is_truthy() == k {
                    vm.call_stack[ci_idx].pc += 1;
                }
            }
            OpCode::TestSet => {
                let b = inst.b() as usize;
                let k = inst.k();
                let vb = vm.stack[base + b];
                if vb.is_truthy() != k {
                    vm.stack[base + a] = vb;
                    vm.call_stack[ci_idx].pc += 1;
                }
            }

            // ---- Control flow ----
            OpCode::Jmp => {
                let sj = inst.get_sj();
                let new_pc = vm.call_stack[ci_idx].pc as i64 + sj as i64;
                vm.call_stack[ci_idx].pc = new_pc as usize;
            }

            // ---- Numeric for loop ----
            OpCode::ForPrep => {
                let init = vm.stack[base + a];
                let limit = vm.stack[base + a + 1];
                let step = vm.stack[base + a + 2];

                if let (Some(i_init), Some(i_limit), Some(i_step)) = (
                    init.as_full_integer(&vm.gc),
                    limit.as_full_integer(&vm.gc),
                    step.as_full_integer(&vm.gc),
                ) {
                    if i_step == 0 {
                        return Err(LuaError::Runtime("'for' step is zero".to_string()));
                    }
                    vm.stack[base + a] = TValue::from_full_integer(i_init, &mut vm.gc);
                    vm.stack[base + a + 1] = TValue::from_full_integer(i_limit, &mut vm.gc);
                    vm.stack[base + a + 2] = TValue::from_full_integer(i_step, &mut vm.gc);
                    vm.stack[base + a + 3] = TValue::from_full_integer(i_init, &mut vm.gc);
                    let should_enter = if i_step > 0 {
                        i_init <= i_limit
                    } else {
                        i_init >= i_limit
                    };
                    if !should_enter {
                        let sbx = inst.sbx();
                        vm.call_stack[ci_idx].pc =
                            (vm.call_stack[ci_idx].pc as i64 + sbx as i64) as usize;
                        vm.call_stack[ci_idx].pc += 1;
                    }
                } else {
                    let f_init = coerce::to_number(init, &vm.gc, &vm.strings).ok_or_else(|| {
                        LuaError::Runtime("'for' initial value must be a number".to_string())
                    })?;
                    let f_limit =
                        coerce::to_number(limit, &vm.gc, &vm.strings).ok_or_else(|| {
                            LuaError::Runtime("'for' limit must be a number".to_string())
                        })?;
                    let f_step = coerce::to_number(step, &vm.gc, &vm.strings).ok_or_else(|| {
                        LuaError::Runtime("'for' step must be a number".to_string())
                    })?;
                    if f_step == 0.0 {
                        return Err(LuaError::Runtime("'for' step is zero".to_string()));
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
                        vm.call_stack[ci_idx].pc =
                            (vm.call_stack[ci_idx].pc as i64 + sbx as i64) as usize;
                        vm.call_stack[ci_idx].pc += 1;
                    }
                }
            }

            OpCode::ForLoop => {
                let counter = vm.stack[base + a];
                let limit = vm.stack[base + a + 1];
                let step = vm.stack[base + a + 2];

                if let (Some(i_counter), Some(i_limit), Some(i_step)) = (
                    counter.as_full_integer(&vm.gc),
                    limit.as_full_integer(&vm.gc),
                    step.as_full_integer(&vm.gc),
                ) {
                    let next = i_counter.wrapping_add(i_step);
                    let continue_loop = if i_step > 0 {
                        next <= i_limit
                    } else {
                        next >= i_limit
                    };
                    if continue_loop {
                        // Close upvalues for the loop variable before updating
                        vm.close_upvalues(base + a + 3);
                        vm.stack[base + a] = TValue::from_full_integer(next, &mut vm.gc);
                        vm.stack[base + a + 3] = TValue::from_full_integer(next, &mut vm.gc);
                        let sbx = inst.sbx();
                        vm.call_stack[ci_idx].pc =
                            (vm.call_stack[ci_idx].pc as i64 + sbx as i64) as usize;
                    }
                } else {
                    let f_counter = counter.as_float().unwrap();
                    let f_limit = limit.as_float().unwrap();
                    let f_step = step.as_float().unwrap();
                    let next = f_counter + f_step;
                    let continue_loop = if f_step > 0.0 {
                        next <= f_limit
                    } else {
                        next >= f_limit
                    };
                    if continue_loop {
                        // Close upvalues for the loop variable before updating
                        vm.close_upvalues(base + a + 3);
                        vm.stack[base + a] = TValue::from_float(next);
                        vm.stack[base + a + 3] = TValue::from_float(next);
                        let sbx = inst.sbx();
                        vm.call_stack[ci_idx].pc =
                            (vm.call_stack[ci_idx].pc as i64 + sbx as i64) as usize;
                    }
                }
            }

            // ---- Returns ----
            OpCode::Return0 => {
                close_tbc_variables(vm, ci_idx, base, None)?;
                if vm.call_stack.len() <= entry_depth {
                    return Ok(vec![]);
                }
                vm.close_upvalues(base);
                return_from_call(vm, &[])?;
            }

            OpCode::Return1 => {
                let val = vm.stack[base + a];
                close_tbc_variables(vm, ci_idx, base, None)?;
                if vm.call_stack.len() <= entry_depth {
                    return Ok(vec![val]);
                }
                vm.close_upvalues(base);
                return_from_call(vm, &[val])?;
            }

            OpCode::Return => {
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
                close_tbc_variables(vm, ci_idx, base, None)?;
                if vm.call_stack.len() <= entry_depth {
                    return Ok(results);
                }
                vm.close_upvalues(base);
                return_from_call(vm, &results)?;
            }

            OpCode::VarArgPrep => {
                // For the top-level chunk, this is a no-op.
                // For vararg functions, the caller has already set up vararg_base.
            }

            // ---- Closure ----
            OpCode::Closure => {
                let bx = inst.bx() as usize;
                // Get the child proto from the current proto
                let proto = proto!(vm, ci_idx);
                let child_proto = &proto.protos[bx];
                let upval_descs = child_proto.upvalues.clone();

                // Store child proto in vm.protos if not already there
                let child_flat_idx = vm.protos.len();
                vm.protos.push(child_proto.clone());

                // Capture upvalues
                let closure_idx_opt = vm.call_stack[ci_idx].closure_idx;
                let mut upvals = Vec::with_capacity(upval_descs.len());
                for desc in &upval_descs {
                    if desc.in_stack {
                        // Upvalue is in the current function's stack
                        let stack_idx = base + desc.index as usize;
                        let uv_idx = vm.find_or_create_open_upval(stack_idx);
                        upvals.push(uv_idx);
                    } else {
                        // Upvalue is in the enclosing function's upvalue list
                        if let Some(parent_closure_idx) = closure_idx_opt {
                            let parent_closure = vm.gc.get_closure(parent_closure_idx);
                            let uv_idx = parent_closure.upvalues[desc.index as usize];
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
                        vm.call_stack.push(ci);
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
                        vm.call_stack.push(ci);
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
                        let pcall_args: Vec<TValue> = (1..num_args)
                            .map(|i| vm.stack[base + a + 1 + i])
                            .collect();

                        let result_base = base + a;
                        match call_function(vm, pcall_func, &pcall_args) {
                            Ok(results) => {
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
                            Err(e) => {
                                // Place (false, error_value)
                                let err_val = e.to_tvalue(&mut vm.strings);
                                let all = vec![TValue::from_bool(false), err_val];
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
                        let xpcall_args: Vec<TValue> = (2..num_args)
                            .map(|i| vm.stack[base + a + 1 + i])
                            .collect();

                        let result_base = base + a;
                        match call_function(vm, xpcall_func, &xpcall_args) {
                            Ok(results) => {
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
                            Err(e) => {
                                // Call handler with error value
                                let err_val = e.to_tvalue(&mut vm.strings);
                                let handler_result =
                                    call_function(vm, handler, &[err_val]);
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
                                    Err(handler_err) => {
                                        // Handler itself errored
                                        let handler_err_val =
                                            handler_err.to_tvalue(&mut vm.strings);
                                        let all = vec![
                                            TValue::from_bool(false),
                                            handler_err_val,
                                        ];
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
                    } else {
                        // Normal native function call
                        let args: Vec<TValue> =
                            (0..num_args).map(|i| vm.stack[base + a + 1 + i]).collect();

                        let native_fn = vm.gc.get_native(native_idx).func;
                        let mut ctx = NativeContext {
                            args: &args,
                            gc: &mut vm.gc,
                            strings: &mut vm.strings,
                        };
                        let results = native_fn(&mut ctx).map_err(map_native_error)?;

                        // Place results
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
                    }
                } else {
                    // Try __call metamethod
                    let mm_name = vm.mm_names.as_ref().unwrap().call;
                    if let Some(mm) = metamethod::get_metamethod(func_val, mm_name, &vm.gc) {
                        let mut mm_args = vec![func_val];
                        for i in 0..num_args {
                            mm_args.push(vm.stack[base + a + 1 + i]);
                        }
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
                        return Err(LuaError::Runtime(format!(
                            "attempt to call a {} value",
                            selune_core::object::lua_type_name(func_val, &vm.gc)
                        )));
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
                    }
                } else if let Some(native_idx) = func_val.as_native_idx() {
                    // Tail call to native: just call it normally and return
                    let args: Vec<TValue> =
                        (0..num_args).map(|i| vm.stack[base + a + 1 + i]).collect();

                    let native_fn = vm.gc.get_native(native_idx).func;
                    let mut ctx = NativeContext {
                        args: &args,
                        gc: &mut vm.gc,
                        strings: &mut vm.strings,
                    };
                    let results = native_fn(&mut ctx).map_err(map_native_error)?;

                    vm.close_upvalues(base);
                    if vm.call_stack.len() <= entry_depth {
                        return Ok(results);
                    }
                    return_from_call(vm, &results)?;
                } else {
                    // Try __call metamethod for TailCall
                    let mm_name = vm.mm_names.as_ref().unwrap().call;
                    if let Some(mm) = metamethod::get_metamethod(func_val, mm_name, &vm.gc) {
                        let mut mm_args = vec![func_val];
                        for i in 0..num_args {
                            mm_args.push(vm.stack[base + a + 1 + i]);
                        }
                        let results = call_function(vm, mm, &mm_args)?;

                        vm.close_upvalues(base);
                        if vm.call_stack.len() <= entry_depth {
                            return Ok(results);
                        }
                        return_from_call(vm, &results)?;
                    } else {
                        return Err(LuaError::Runtime(format!(
                            "attempt to call a {} value",
                            selune_core::object::lua_type_name(func_val, &vm.gc)
                        )));
                    }
                }
            }

            // ---- Vararg ----
            OpCode::VarArg => {
                let c = inst.c() as usize;
                let ci = &vm.call_stack[ci_idx];
                if let Some(vararg_base) = ci.vararg_base {
                    let num_params = proto!(vm, ci_idx).num_params as usize;
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
                close_tbc_variables(vm, ci_idx, base + a, None)?;
                vm.close_upvalues(base + a);
            }

            OpCode::Tbc => {
                // Register this stack slot as to-be-closed
                vm.call_stack[ci_idx].tbc_slots.push(base + a);
            }

            // ---- Generic for loop ----
            OpCode::TForPrep => {
                let sbx = inst.sbx();
                // Jump forward to TFORCALL
                vm.call_stack[ci_idx].pc =
                    (vm.call_stack[ci_idx].pc as i64 + sbx as i64) as usize;
            }

            OpCode::TForCall => {
                let c = inst.c() as usize; // number of loop variables
                let iter_func = vm.stack[base + a];
                let state = vm.stack[base + a + 1];
                let control = vm.stack[base + a + 2];
                // Call iterator function: iter_func(state, control)
                let results = call_function(vm, iter_func, &[state, control])?;
                // Place results in R[A+4], R[A+5], ... R[A+3+c]
                for i in 0..c {
                    vm.stack[base + a + 4 + i] =
                        results.get(i).copied().unwrap_or(TValue::nil());
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
                    vm.call_stack[ci_idx].pc =
                        (vm.call_stack[ci_idx].pc as i64 + sbx as i64) as usize;
                }
            }

            // ---- Table operations ----
            OpCode::NewTable => {
                let b = inst.b() as usize;
                let c = inst.c() as usize;
                if inst.k() {
                    vm.call_stack[ci_idx].pc += 1;
                }
                let table_idx = vm.gc.alloc_table(b, c);
                vm.stack[base + a] = TValue::from_table(table_idx);
            }

            OpCode::GetTable => {
                let b = inst.b() as usize;
                let c = inst.c() as usize;
                let table_val = vm.stack[base + b];
                let key = vm.stack[base + c];
                let result = table_index(vm, table_val, key)?;
                vm.stack[base + a] = result;
            }

            OpCode::GetI => {
                let b = inst.b() as usize;
                let c = inst.c() as i64;
                let table_val = vm.stack[base + b];
                let key = TValue::from_integer(c);
                let result = table_index(vm, table_val, key)?;
                vm.stack[base + a] = result;
            }

            OpCode::GetField => {
                let b = inst.b() as usize;
                let c = inst.c() as usize;
                let table_val = vm.stack[base + b];
                let key_k = get_k(vm, ci_idx, c);
                let key_sid = match key_k {
                    Constant::String(sid) => sid,
                    _ => {
                        return Err(LuaError::Runtime(
                            "GetField: non-string constant".to_string(),
                        ))
                    }
                };
                let key = TValue::from_string_id(key_sid);
                let result = table_index(vm, table_val, key)?;
                vm.stack[base + a] = result;
            }

            OpCode::SetTable => {
                let b = inst.b() as usize;
                let c = inst.c() as usize;
                let table_val = vm.stack[base + a];
                let key = vm.stack[base + b];
                let val = if inst.k() {
                    let proto = proto!(vm, ci_idx);
                    constant_to_tvalue(&proto.constants[c], &mut vm.gc)
                } else {
                    vm.stack[base + c]
                };
                table_newindex(vm, table_val, key, val)?;
            }

            OpCode::SetI => {
                let b = inst.b() as i64;
                let c = inst.c() as usize;
                let table_val = vm.stack[base + a];
                let val = if inst.k() {
                    let proto = proto!(vm, ci_idx);
                    constant_to_tvalue(&proto.constants[c], &mut vm.gc)
                } else {
                    vm.stack[base + c]
                };
                let key = TValue::from_integer(b);
                table_newindex(vm, table_val, key, val)?;
            }

            OpCode::SetField => {
                let b = inst.b() as usize;
                let c = inst.c() as usize;
                let table_val = vm.stack[base + a];
                let proto = proto!(vm, ci_idx);
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
                let key = TValue::from_string_id(key_sid);
                table_newindex(vm, table_val, key, val)?;
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
                        b, closure.upvalues.len()
                    )));
                }
                let uv_idx = closure.upvalues[b];
                let upval = vm.get_upval_value(uv_idx);
                let key_k = get_k(vm, ci_idx, c);
                let key_sid = match key_k {
                    Constant::String(sid) => sid,
                    _ => {
                        return Err(LuaError::Runtime(
                            "GetTabUp: non-string constant".to_string(),
                        ))
                    }
                };
                let key = TValue::from_string_id(key_sid);
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
                let table_idx = upval.as_table_idx().ok_or_else(|| {
                    LuaError::Runtime("SetTabUp: upvalue is not a table".to_string())
                })?;
                let proto = proto!(vm, ci_idx);
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
                vm.gc.get_table_mut(table_idx).raw_set_str(key_sid, val);
            }

            OpCode::SetList => {
                let b = inst.b() as usize;
                let mut c = inst.c() as usize;
                if inst.k() {
                    let proto = proto!(vm, ci_idx);
                    let next_inst = proto.code[vm.call_stack[ci_idx].pc];
                    vm.call_stack[ci_idx].pc += 1;
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
                    let proto = proto!(vm, ci_idx);
                    constant_to_tvalue(&proto.constants[c], &mut vm.gc)
                } else {
                    vm.stack[base + c]
                };
                let result = table_index(vm, table_val, key)?;
                vm.stack[base + a] = result;
            }

            OpCode::ExtraArg => {}

            _ => {
                return Err(LuaError::Runtime(format!("unimplemented opcode: {:?}", op)));
            }
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
fn close_tbc_variables(
    vm: &mut Vm,
    ci_idx: usize,
    from_level: usize,
    error_val: Option<TValue>,
) -> Result<(), LuaError> {
    // Collect TBC slots that need closing (those >= from_level), in reverse order
    let slots_to_close: Vec<usize> = vm.call_stack[ci_idx]
        .tbc_slots
        .iter()
        .copied()
        .filter(|&slot| slot >= from_level)
        .collect();

    // Remove them from the tracking list
    vm.call_stack[ci_idx]
        .tbc_slots
        .retain(|&slot| slot < from_level);

    // Close in reverse order (last registered first)
    let err_arg = error_val.unwrap_or(TValue::nil());
    for &slot in slots_to_close.iter().rev() {
        let val = vm.stack[slot];
        if val.is_nil() {
            continue; // nil TBC values are allowed, just skip
        }
        // Look up __close metamethod
        let mm_name = vm.mm_names.as_ref().unwrap().close;
        if let Some(mm) = metamethod::get_metamethod(val, mm_name, &vm.gc) {
            // Call __close(val, error_or_nil)
            // Ignore errors during close when already in error path
            let result = call_function(vm, mm, &[val, err_arg]);
            if error_val.is_none() {
                // Normal exit: propagate __close errors
                result?;
            }
            // Error exit: suppress __close errors (Lua 5.4 semantics)
        }
    }
    Ok(())
}

/// Close TBC variables during error unwinding.
/// Iterates frames from the top of call_stack down to target_depth,
/// closing TBC variables in each frame. Does NOT pop frames.
fn unwind_tbc(vm: &mut Vm, target_depth: usize, error_val: Option<TValue>) {
    let len = vm.call_stack.len();
    for ci_idx in (target_depth..len).rev() {
        let base = vm.call_stack[ci_idx].base;
        // Close TBC variables in this frame (errors suppressed since we're in error path)
        let _ = close_tbc_variables(vm, ci_idx, base, error_val);
    }
}

/// Table index with __index metamethod support.
/// Handles: tables (with fallback to __index), and non-table values with __index.
fn table_index(vm: &mut Vm, table_val: TValue, key: TValue) -> Result<TValue, LuaError> {
    if let Some(table_idx) = table_val.as_table_idx() {
        // Raw get first
        let result = vm.gc.get_table(table_idx).raw_get(key);
        if !result.is_nil() {
            return Ok(result);
        }
        // Check __index metamethod
        let mm_name = vm.mm_names.as_ref().unwrap().index;
        if let Some(mm) = metamethod::get_metamethod(table_val, mm_name, &vm.gc) {
            if mm.as_table_idx().is_some() {
                // __index is a table: recurse
                return table_index(vm, mm, key);
            }
            // __index is a function: call with (table, key)
            let results = call_function(vm, mm, &[table_val, key])?;
            Ok(results.first().copied().unwrap_or(TValue::nil()))
        } else {
            Ok(TValue::nil())
        }
    } else {
        // Non-table: check for __index metamethod (unlikely but valid for userdata etc.)
        Err(LuaError::Runtime(format!(
            "attempt to index a {} value",
            selune_core::object::lua_type_name(table_val, &vm.gc)
        )))
    }
}

/// Table newindex with __newindex metamethod support.
fn table_newindex(vm: &mut Vm, table_val: TValue, key: TValue, val: TValue) -> Result<(), LuaError> {
    if let Some(table_idx) = table_val.as_table_idx() {
        // Check if key already exists (raw)
        let existing = vm.gc.get_table(table_idx).raw_get(key);
        if !existing.is_nil() {
            // Key exists, just set it (no metamethod)
            vm.gc
                .get_table_mut(table_idx)
                .raw_set(key, val)
                .map_err(|e: &str| LuaError::Runtime(e.to_string()))?;
            return Ok(());
        }
        // Key doesn't exist: check __newindex metamethod
        let mm_name = vm.mm_names.as_ref().unwrap().newindex;
        if let Some(mm) = metamethod::get_metamethod(table_val, mm_name, &vm.gc) {
            if mm.as_table_idx().is_some() {
                // __newindex is a table: recurse
                return table_newindex(vm, mm, key, val);
            }
            // __newindex is a function: call with (table, key, value)
            call_function(vm, mm, &[table_val, key, val])?;
            Ok(())
        } else {
            // No __newindex: just raw set
            vm.gc
                .get_table_mut(table_idx)
                .raw_set(key, val)
                .map_err(|e: &str| LuaError::Runtime(e.to_string()))?;
            Ok(())
        }
    } else {
        Err(LuaError::Runtime(format!(
            "attempt to index a {} value",
            selune_core::object::lua_type_name(table_val, &vm.gc)
        )))
    }
}

/// Return from a function call, placing results in the caller's frame.
fn return_from_call(vm: &mut Vm, results: &[TValue]) -> Result<(), LuaError> {
    let ci_idx = vm.call_stack.len() - 1;
    let num_results = vm.call_stack[ci_idx].num_results;
    let func_stack_idx = vm.call_stack[ci_idx].func_stack_idx;

    vm.call_stack.pop();

    // Place results starting at func_stack_idx
    if num_results < 0 {
        // Multi-return: place all results
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

    Ok(())
}

/// Map a NativeError to a LuaError.
fn map_native_error(e: NativeError) -> LuaError {
    match e {
        NativeError::String(s) => LuaError::Runtime(s),
        NativeError::Value(v) => LuaError::LuaValue(v),
    }
}

/// Return the operation description for metamethod error messages.
fn mm_op_description(mm_idx: u8) -> &'static str {
    match mm_idx {
        0..=6 => "arithmetic",  // add, sub, mul, mod, pow, div, idiv
        7..=11 => "bitwise operation", // band, bor, bxor, shl, shr
        12 => "concatenation",  // concat
        _ => "arithmetic",
    }
}

/// Call a Lua function (closure, native, or __call metamethod) with given args.
/// This is used by metamethod dispatch, pcall, xpcall, and TFORCALL.
pub fn call_function(vm: &mut Vm, func: TValue, args: &[TValue]) -> Result<Vec<TValue>, LuaError> {
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
            vm.call_stack.push(ci);

            let result = execute_from(vm, entry_depth);
            if result.is_err() {
                // Close TBC variables in all unwinding frames
                let err_val = result.as_ref().err().map(|e| e.to_tvalue(&mut vm.strings));
                unwind_tbc(vm, saved_call_depth, err_val);
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
            vm.call_stack.push(ci);

            let result = execute_from(vm, entry_depth);
            if result.is_err() {
                // Close TBC variables in all unwinding frames
                let err_val = result.as_ref().err().map(|e| e.to_tvalue(&mut vm.strings));
                unwind_tbc(vm, saved_call_depth, err_val);
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
            match call_function(vm, pcall_func, pcall_args) {
                Ok(results) => {
                    let mut all = vec![TValue::from_bool(true)];
                    all.extend(results);
                    Ok(all)
                }
                Err(e) => {
                    let err_val = e.to_tvalue(&mut vm.strings);
                    Ok(vec![TValue::from_bool(false), err_val])
                }
            }
        } else if is_xpcall {
            let xpcall_func = args.first().copied().unwrap_or(TValue::nil());
            let handler = args.get(1).copied().unwrap_or(TValue::nil());
            let xpcall_args = if args.len() > 2 { &args[2..] } else { &[] };
            match call_function(vm, xpcall_func, xpcall_args) {
                Ok(results) => {
                    let mut all = vec![TValue::from_bool(true)];
                    all.extend(results);
                    Ok(all)
                }
                Err(e) => {
                    let err_val = e.to_tvalue(&mut vm.strings);
                    match call_function(vm, handler, &[err_val]) {
                        Ok(handler_results) => {
                            let mut all = vec![TValue::from_bool(false)];
                            all.extend(handler_results);
                            Ok(all)
                        }
                        Err(handler_err) => {
                            let handler_err_val = handler_err.to_tvalue(&mut vm.strings);
                            Ok(vec![TValue::from_bool(false), handler_err_val])
                        }
                    }
                }
            }
        } else {
            // Normal native function call
            let native_fn = vm.gc.get_native(native_idx).func;
            let args_vec = args.to_vec();
            let mut ctx = NativeContext {
                args: &args_vec,
                gc: &mut vm.gc,
                strings: &mut vm.strings,
            };
            native_fn(&mut ctx).map_err(map_native_error)
        }
    } else {
        // Try __call metamethod
        let mm_name = vm.mm_names.as_ref().unwrap().call;
        if let Some(mm) = crate::metamethod::get_metamethod(func, mm_name, &vm.gc) {
            // Prepend the original value as first arg
            let mut new_args = vec![func];
            new_args.extend_from_slice(args);
            call_function(vm, mm, &new_args)
        } else {
            Err(LuaError::Runtime(format!(
                "attempt to call a {} value",
                selune_core::object::lua_type_name(func, &vm.gc)
            )))
        }
    }
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
