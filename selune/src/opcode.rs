#[derive(Debug)]
pub enum OpCode {
    LoadInt(usize, i64),
    LoadFloat(usize, f64),
    Add(usize, usize, usize),
    Lt(usize, usize, usize),
    JumpIfFalse(usize, isize),
    Jump(isize),
    Return(usize),
}
