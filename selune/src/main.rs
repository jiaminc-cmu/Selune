mod opcode;
mod value;
mod vm;

use opcode::OpCode;

fn main() {
    let chunk = vec![
        OpCode::LoadInt(0, 10),
        OpCode::LoadInt(1, 20),
        OpCode::Add(2, 0, 1),
        OpCode::Return(2),
    ];

    let result = vm::execute(&chunk);
    unsafe {
        println!("Result: {}", result.payload.i);
    }
}
