#[derive(Debug)]
pub enum OpCode {
    LoadInt(usize, i64),
    LoadFloat(usize, f64),
    Add(usize, usize, usize),
    Return(usize),
}
