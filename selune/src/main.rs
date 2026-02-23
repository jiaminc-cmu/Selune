mod opcode;
mod value;
mod vm;

use opcode::OpCode;

fn main() {
    let chunk = vec![
        OpCode::LoadFloat(0, 1.5),
        OpCode::LoadFloat(1, 2.7),
        OpCode::Add(2, 0, 1),
        OpCode::Return(2),
    ];

    let result = vm::execute(&chunk);
    unsafe {
        println!("Result: {}", result.payload.f);
    }
}
