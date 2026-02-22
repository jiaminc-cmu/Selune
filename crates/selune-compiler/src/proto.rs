/// Function prototype: holds compiled bytecode, constants, and debug info.
use crate::opcode::Instruction;
use selune_core::string::StringId;

/// A constant value in the constant pool.
#[derive(Clone, Debug, PartialEq)]
pub enum Constant {
    Nil,
    Boolean(bool),
    Integer(i64),
    Float(f64),
    String(StringId),
}

/// Description of an upvalue.
#[derive(Clone, Debug)]
pub struct UpvalDesc {
    /// Name of the upvalue (for debug info).
    pub name: Option<StringId>,
    /// True if this upvalue is in the enclosing function's stack (not another upvalue).
    pub in_stack: bool,
    /// Index: register index if in_stack, upvalue index in parent otherwise.
    pub index: u8,
    /// Kind (regular=0, const=1, close=2, to-be-closed=3).
    pub kind: u8,
}

/// A local variable debug entry.
#[derive(Clone, Debug)]
pub struct LocalVar {
    pub name: StringId,
    /// First PC where the variable is active.
    pub start_pc: u32,
    /// First PC where the variable is dead.
    pub end_pc: u32,
}

/// Absolute line info entry for compressed line info.
#[derive(Clone, Debug)]
pub struct AbsLineInfo {
    pub pc: u32,
    pub line: u32,
}

/// A compiled function prototype.
#[derive(Clone, Debug)]
pub struct Proto {
    /// Bytecode instructions.
    pub code: Vec<Instruction>,
    /// Constant pool.
    pub constants: Vec<Constant>,
    /// Nested function prototypes.
    pub protos: Vec<Proto>,
    /// Upvalue descriptors.
    pub upvalues: Vec<UpvalDesc>,
    /// Number of fixed parameters.
    pub num_params: u8,
    /// Whether this function accepts varargs.
    pub is_vararg: bool,
    /// Maximum stack size needed.
    pub max_stack_size: u8,
    /// Source name (for error messages).
    pub source: Option<StringId>,

    // --- Debug info ---
    /// Relative line info (delta from previous instruction).
    pub line_info: Vec<i8>,
    /// Absolute line info (for large line deltas).
    pub abs_line_info: Vec<AbsLineInfo>,
    /// Local variable debug info.
    pub local_vars: Vec<LocalVar>,

    /// Current line being compiled (used during compilation).
    current_line: u32,
}

impl Proto {
    /// Create a new empty prototype.
    pub fn new() -> Self {
        Proto {
            code: Vec::new(),
            constants: Vec::new(),
            protos: Vec::new(),
            upvalues: Vec::new(),
            num_params: 0,
            is_vararg: false,
            max_stack_size: 2, // minimum
            source: None,
            line_info: Vec::new(),
            abs_line_info: Vec::new(),
            local_vars: Vec::new(),
            current_line: 0,
        }
    }

    /// Emit an instruction at the given source line.
    pub fn emit(&mut self, inst: Instruction, line: u32) -> usize {
        let pc = self.code.len();
        self.code.push(inst);

        // Save line info
        let delta = line as i32 - self.current_line as i32;
        if delta >= -128 && delta <= 127 {
            self.line_info.push(delta as i8);
        } else {
            // Large delta: store 0 and add absolute line info
            self.line_info.push(0);
            self.abs_line_info.push(AbsLineInfo { pc: pc as u32, line });
        }
        self.current_line = line;

        pc
    }

    /// Add a constant to the pool, returning its index. Deduplicates.
    pub fn add_constant(&mut self, k: Constant) -> usize {
        // Search for existing
        for (i, existing) in self.constants.iter().enumerate() {
            if constants_equal(existing, &k) {
                return i;
            }
        }
        let idx = self.constants.len();
        self.constants.push(k);
        idx
    }

    /// Get the line number for a given PC.
    pub fn get_line(&self, pc: usize) -> u32 {
        if pc >= self.line_info.len() {
            return 0;
        }

        // Check absolute line info first for this PC
        for abs in self.abs_line_info.iter().rev() {
            if abs.pc as usize <= pc {
                // Accumulate deltas from this absolute point
                let mut line = abs.line as i32;
                for i in (abs.pc as usize + 1)..=pc {
                    let delta = self.line_info[i];
                    if delta != 0 || !self.abs_line_info.iter().any(|a| a.pc as usize == i) {
                        line += delta as i32;
                    }
                }
                return line as u32;
            }
        }

        // No absolute info before this PC, accumulate from start
        let mut line = 0i32;
        for i in 0..=pc {
            let delta = self.line_info[i];
            if delta != 0 || !self.abs_line_info.iter().any(|a| a.pc as usize == i) {
                line += delta as i32;
            } else if let Some(abs) = self.abs_line_info.iter().find(|a| a.pc as usize == i) {
                line = abs.line as i32;
            }
        }
        line as u32
    }

    /// Get the number of instructions.
    pub fn code_len(&self) -> usize {
        self.code.len()
    }

    /// Get a mutable reference to an instruction (for backpatching).
    pub fn get_mut(&mut self, pc: usize) -> &mut Instruction {
        &mut self.code[pc]
    }
}

impl Default for Proto {
    fn default() -> Self {
        Self::new()
    }
}

/// Check if two constants are equal (NaN != NaN for floats in constant pool dedup).
fn constants_equal(a: &Constant, b: &Constant) -> bool {
    match (a, b) {
        (Constant::Nil, Constant::Nil) => true,
        (Constant::Boolean(a), Constant::Boolean(b)) => a == b,
        (Constant::Integer(a), Constant::Integer(b)) => a == b,
        (Constant::Float(a), Constant::Float(b)) => a.to_bits() == b.to_bits(),
        (Constant::String(a), Constant::String(b)) => a == b,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::opcode::OpCode;

    #[test]
    fn test_empty_proto() {
        let p = Proto::new();
        assert_eq!(p.code_len(), 0);
        assert!(p.constants.is_empty());
        assert!(p.protos.is_empty());
        assert!(p.upvalues.is_empty());
        assert_eq!(p.num_params, 0);
        assert!(!p.is_vararg);
        assert_eq!(p.max_stack_size, 2);
    }

    #[test]
    fn test_emit_instruction() {
        let mut p = Proto::new();
        let pc = p.emit(Instruction::abc(OpCode::Move, 0, 1, 0, false), 1);
        assert_eq!(pc, 0);
        assert_eq!(p.code_len(), 1);
        assert_eq!(p.code[0].opcode(), OpCode::Move);
    }

    #[test]
    fn test_add_constant_dedup() {
        let mut p = Proto::new();
        let i1 = p.add_constant(Constant::Integer(42));
        let i2 = p.add_constant(Constant::Integer(42));
        assert_eq!(i1, i2);
        assert_eq!(p.constants.len(), 1);
    }

    #[test]
    fn test_add_constant_different() {
        let mut p = Proto::new();
        let i1 = p.add_constant(Constant::Integer(42));
        let i2 = p.add_constant(Constant::Integer(43));
        assert_ne!(i1, i2);
        assert_eq!(p.constants.len(), 2);
    }

    #[test]
    fn test_add_constant_float_dedup() {
        let mut p = Proto::new();
        let i1 = p.add_constant(Constant::Float(3.14));
        let i2 = p.add_constant(Constant::Float(3.14));
        assert_eq!(i1, i2);
    }

    #[test]
    fn test_add_constant_nan_no_dedup() {
        let mut p = Proto::new();
        // NaN == NaN for dedup purposes (same bit pattern)
        let i1 = p.add_constant(Constant::Float(f64::NAN));
        let i2 = p.add_constant(Constant::Float(f64::NAN));
        assert_eq!(i1, i2);
    }

    #[test]
    fn test_line_tracking() {
        let mut p = Proto::new();
        p.emit(Instruction::abc(OpCode::Move, 0, 1, 0, false), 1);
        p.emit(Instruction::abc(OpCode::Move, 1, 2, 0, false), 2);
        p.emit(Instruction::abc(OpCode::Move, 2, 3, 0, false), 5);
        assert_eq!(p.get_line(0), 1);
        assert_eq!(p.get_line(1), 2);
        assert_eq!(p.get_line(2), 5);
    }

    #[test]
    fn test_get_mut_backpatch() {
        let mut p = Proto::new();
        p.emit(Instruction::sj(OpCode::Jmp, 0), 1);
        p.get_mut(0).set_sj(42);
        assert_eq!(p.code[0].get_sj(), 42);
    }
}
