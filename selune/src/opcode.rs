#[derive(Debug)]
pub enum OpCode {
    LoadInt(usize, i64),
    Add(usize, usize, usize),
    Return(usize),
}
