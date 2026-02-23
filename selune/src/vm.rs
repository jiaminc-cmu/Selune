use crate::opcode::OpCode;
use crate::value::{TValue, Tag};

pub fn execute(instructions: &[OpCode]) -> TValue {
    let mut registers = vec![TValue::nil(); 256];
    let mut pc = 0;

    while pc < instructions.len() {
        let op = &instructions[pc];
        let mut next_pc = pc + 1;

        match op {
            OpCode::LoadInt(dst, val) => registers[*dst] = TValue::int(*val),
            OpCode::LoadFloat(dst, val) => registers[*dst] = TValue::float(*val),
            OpCode::Add(dst, lhs, rhs) => {
                let l = registers[*lhs];
                let r = registers[*rhs];
                unsafe {
                    match (l.tag, r.tag) {
                        (Tag::Int, Tag::Int) => {
                            registers[*dst] = TValue::int(l.payload.i + r.payload.i)
                        }
                        (Tag::Float, Tag::Float) => {
                            registers[*dst] = TValue::float(l.payload.f + r.payload.f)
                        }
                        (Tag::Int, Tag::Float) => {
                            registers[*dst] = TValue::float(l.payload.i as f64 + r.payload.f)
                        }
                        (Tag::Float, Tag::Int) => {
                            registers[*dst] = TValue::float(l.payload.f + r.payload.i as f64)
                        }
                        _ => panic!("Type Error in Add"),
                    }
                }
            }
            OpCode::Lt(dst, lhs, rhs) => {
                let l = registers[*lhs];
                let r = registers[*rhs];
                unsafe {
                    match (l.tag, r.tag) {
                        (Tag::Int, Tag::Int) => {
                            registers[*dst] = TValue::boolean(l.payload.i < r.payload.i)
                        }
                        (Tag::Float, Tag::Float) => {
                            registers[*dst] = TValue::boolean(l.payload.f < r.payload.f)
                        }
                        (Tag::Int, Tag::Float) => {
                            registers[*dst] = TValue::boolean((l.payload.i as f64) < r.payload.f)
                        }
                        (Tag::Float, Tag::Int) => {
                            registers[*dst] = TValue::boolean(l.payload.f < (r.payload.i as f64))
                        }
                        _ => panic!("Type Error in Lt"),
                    }
                }
            }
            OpCode::JumpIfFalse(cond_reg, offset) => {
                let cond = registers[*cond_reg];
                let is_truthy = match cond.tag {
                    Tag::Nil => false,
                    Tag::Bool => unsafe { cond.payload.b },
                    _ => true,
                };
                if !is_truthy {
                    next_pc = (pc as isize + offset) as usize;
                }
            }
            OpCode::Jump(offset) => {
                next_pc = (pc as isize + offset) as usize;
            }
            OpCode::Return(reg) => {
                return registers[*reg];
            }
        }

        pc = next_pc;
    }
    panic!("Execution finished without Return instruction");
}
