mod opcode;
mod value;
mod vm;

use opcode::OpCode;

fn main() {
    let chunk = vec![
        /* 0 */ OpCode::LoadInt(0, 0), // sum = 0
        /* 1 */ OpCode::LoadInt(1, 1), // i = 1
        /* 2 */ OpCode::LoadInt(2, 101), // limit = 101
        /* 3 */ OpCode::LoadInt(3, 1), // step = 1
        // --- Loop starts (PC = 4) ---
        /* 4 */
        OpCode::Lt(4, 1, 2), // R4 = i < limit
        /* 5 */
        OpCode::JumpIfFalse(4, 4), // If R4 is false, jump to 4
        /* 6 */ OpCode::Add(0, 0, 1), // sum = sum + i
        /* 7 */ OpCode::Add(1, 1, 3), // i = i + step
        /* 8 */
        OpCode::Jump(-4), // Jump back to the start
        /* 9 */
        OpCode::Return(0), // return sum
    ];

    let result = vm::execute(&chunk);

    unsafe {
        println!("The sum of 1 to 100 is: {}", result.payload.i);
    }
}
