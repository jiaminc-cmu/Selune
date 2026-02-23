use crate::opcode::OpCode;
use crate::value::{TValue, Tag};

pub fn execute(instructions: &[OpCode]) -> TValue {
    let mut registers = vec![TValue::int(0); 256];

    for op in instructions {
        match op {
            OpCode::LoadInt(dst, val) => {
                registers[*dst] = TValue::int(*val);
            }
            OpCode::Add(dst, lhs, rhs) => {
                let l = registers[*lhs];
                let r = registers[*rhs];
                unsafe {
                    if l.tag == Tag::Int && r.tag == Tag::Int {
                        registers[*dst] = TValue::int(l.payload.i + r.payload.i);
                    } else {
                        panic!("Type Error!");
                    }
                }
            }
            OpCode::Return(reg) => {
                return registers[*reg];
            }
        }
    }
    panic!("Execution finished without Return instruction");
}
