/// Lua 5.4 opcodes and instruction encoding.
///
/// Instruction format (32 bits):
/// - Bits 0-6: OpCode (7 bits)
/// - Bit 7: k flag (1 bit) — extra arg, used by some instructions
/// - Bits 8-15: A (8 bits)
/// - For iABC format:
///   - Bits 16-23: B (8 bits)
///   - Bits 24-31: C (8 bits)
///   Note: In PUC Lua 5.4, C is bits 16-24, B is bits 25-32, but
///   for simplicity we use the layout: opcode(7) | k(1) | A(8) | B(8) | C(8)
/// - For iABx: Bx = bits 16-31 (unsigned 16 bits)
/// - For iAsBx: sBx = Bx - offset (signed interpretation)
/// - For iAx: Ax = bits 8-31 (24 bits, unsigned)
/// - For isJ: sJ = bits 8-31 (24 bits, signed with offset)
use std::fmt;

/// Size constants for instruction fields.
const SIZE_OP: u32 = 7;
const SIZE_K: u32 = 1;
const SIZE_A: u32 = 8;
const SIZE_B: u32 = 8;
const SIZE_C: u32 = 8;
const SIZE_BX: u32 = SIZE_B + SIZE_C; // 16
const SIZE_AX: u32 = SIZE_A + SIZE_B + SIZE_C; // 24
const SIZE_SJ: u32 = SIZE_A + SIZE_B + SIZE_C; // 24

/// Position constants.
const POS_OP: u32 = 0;
const POS_K: u32 = POS_OP + SIZE_OP; // 7
const POS_A: u32 = POS_K + SIZE_K; // 8
const POS_B: u32 = POS_A + SIZE_A; // 16
const POS_C: u32 = POS_B + SIZE_B; // 24

/// Mask helpers.
const fn mask(n: u32) -> u32 {
    (1 << n) - 1
}

pub const MAX_A: u32 = mask(SIZE_A); // 255
pub const MAX_B: u32 = mask(SIZE_B); // 255
pub const MAX_C: u32 = mask(SIZE_C); // 255
pub const MAX_BX: u32 = mask(SIZE_BX); // 65535
pub const MAX_SBX: i32 = (MAX_BX >> 1) as i32; // 32767
pub const MIN_SBX: i32 = -MAX_SBX; // -32767
pub const MAX_AX: u32 = mask(SIZE_AX); // 16777215
pub const MAX_SJ: i32 = (mask(SIZE_SJ) >> 1) as i32; // 8388607
pub const MIN_SJ: i32 = -MAX_SJ; // -8388607

const OFFSET_SBX: i32 = MAX_SBX;
const OFFSET_SJ: i32 = MAX_SJ;

/// All 83 Lua 5.4 opcodes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum OpCode {
    Move = 0,
    LoadI,
    LoadF,
    LoadK,
    LoadKX,
    LoadFalse,
    LFalseSkip,
    LoadTrue,
    LoadNil,
    GetUpval,
    SetUpval,
    GetTabUp,
    GetTable,
    GetI,
    GetField,
    SetTabUp,
    SetTable,
    SetI,
    SetField,
    NewTable,
    Self_,
    AddI,
    AddK,
    SubK,
    MulK,
    ModK,
    PowK,
    DivK,
    IDivK,
    BAndK,
    BOrK,
    BXorK,
    ShrI,
    ShlI,
    Add,
    Sub,
    Mul,
    Mod,
    Pow,
    Div,
    IDiv,
    BAnd,
    BOr,
    BXor,
    Shl,
    Shr,
    MMBin,
    MMBinI,
    MMBinK,
    Unm,
    BNot,
    Not,
    Len,
    Concat,
    Close,
    Tbc,
    Jmp,
    Eq,
    Lt,
    Le,
    EqK,
    EqI,
    LtI,
    LeI,
    GtI,
    GeI,
    Test,
    TestSet,
    Call,
    TailCall,
    Return,
    Return0,
    Return1,
    ForLoop,
    ForPrep,
    TForPrep,
    TForCall,
    TForLoop,
    SetList,
    Closure,
    VarArg,
    VarArgPrep,
    ExtraArg,
}

impl OpCode {
    /// Number of opcodes.
    pub const COUNT: usize = 83;

    /// Get the opcode from a u8 value.
    pub fn from_u8(val: u8) -> Option<OpCode> {
        if (val as usize) < Self::COUNT {
            // Safety: OpCode is repr(u8) and we've verified the range
            Some(unsafe { std::mem::transmute(val) })
        } else {
            None
        }
    }

    /// Get the instruction format for this opcode.
    pub fn format(&self) -> InstructionFormat {
        use InstructionFormat::*;
        use OpCode::*;
        match self {
            // iAx format
            ExtraArg => IAx,
            // isJ format
            Jmp => IsJ,
            // iABx format
            LoadI | LoadF | LoadK | LoadKX | LoadFalse | LFalseSkip | LoadTrue | LoadNil
            | ForLoop | ForPrep | TForPrep | TForLoop | Closure | VarArgPrep => IABx,
            // All others are iABC
            _ => IABC,
        }
    }

    /// Get the name of this opcode.
    pub fn name(&self) -> &'static str {
        use OpCode::*;
        match self {
            Move => "MOVE",
            LoadI => "LOADI",
            LoadF => "LOADF",
            LoadK => "LOADK",
            LoadKX => "LOADKX",
            LoadFalse => "LOADFALSE",
            LFalseSkip => "LFALSESKIP",
            LoadTrue => "LOADTRUE",
            LoadNil => "LOADNIL",
            GetUpval => "GETUPVAL",
            SetUpval => "SETUPVAL",
            GetTabUp => "GETTABUP",
            GetTable => "GETTABLE",
            GetI => "GETI",
            GetField => "GETFIELD",
            SetTabUp => "SETTABUP",
            SetTable => "SETTABLE",
            SetI => "SETI",
            SetField => "SETFIELD",
            NewTable => "NEWTABLE",
            Self_ => "SELF",
            AddI => "ADDI",
            AddK => "ADDK",
            SubK => "SUBK",
            MulK => "MULK",
            ModK => "MODK",
            PowK => "POWK",
            DivK => "DIVK",
            IDivK => "IDIVK",
            BAndK => "BANDK",
            BOrK => "BORK",
            BXorK => "BXORK",
            ShrI => "SHRI",
            ShlI => "SHLI",
            Add => "ADD",
            Sub => "SUB",
            Mul => "MUL",
            Mod => "MOD",
            Pow => "POW",
            Div => "DIV",
            IDiv => "IDIV",
            BAnd => "BAND",
            BOr => "BOR",
            BXor => "BXOR",
            Shl => "SHL",
            Shr => "SHR",
            MMBin => "MMBIN",
            MMBinI => "MMBINI",
            MMBinK => "MMBINK",
            Unm => "UNM",
            BNot => "BNOT",
            Not => "NOT",
            Len => "LEN",
            Concat => "CONCAT",
            Close => "CLOSE",
            Tbc => "TBC",
            Jmp => "JMP",
            Eq => "EQ",
            Lt => "LT",
            Le => "LE",
            EqK => "EQK",
            EqI => "EQI",
            LtI => "LTI",
            LeI => "LEI",
            GtI => "GTI",
            GeI => "GEI",
            Test => "TEST",
            TestSet => "TESTSET",
            Call => "CALL",
            TailCall => "TAILCALL",
            Return => "RETURN",
            Return0 => "RETURN0",
            Return1 => "RETURN1",
            ForLoop => "FORLOOP",
            ForPrep => "FORPREP",
            TForPrep => "TFORPREP",
            TForCall => "TFORCALL",
            TForLoop => "TFORLOOP",
            SetList => "SETLIST",
            Closure => "CLOSURE",
            VarArg => "VARARG",
            VarArgPrep => "VARARGPREP",
            ExtraArg => "EXTRAARG",
        }
    }

    /// Returns true if this opcode is a test (conditional skip).
    pub fn is_test(&self) -> bool {
        use OpCode::*;
        matches!(
            self,
            Eq | Lt | Le | EqK | EqI | LtI | LeI | GtI | GeI | Test | TestSet
        )
    }
}

/// Instruction format types.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InstructionFormat {
    IABC,
    IABx,
    IAsBx, // signed Bx, same bits as ABx
    IAx,
    IsJ,
}

/// A 32-bit Lua bytecode instruction.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Instruction(pub u32);

impl Instruction {
    // ---- Constructors ----

    /// Create an iABC instruction.
    pub fn abc(op: OpCode, a: u8, b: u8, c: u8, k: bool) -> Self {
        let mut i = (op as u32) << POS_OP;
        i |= (k as u32) << POS_K;
        i |= (a as u32) << POS_A;
        i |= (b as u32) << POS_B;
        i |= (c as u32) << POS_C;
        Instruction(i)
    }

    /// Create an iABx instruction.
    pub fn abx(op: OpCode, a: u8, bx: u32) -> Self {
        debug_assert!(bx <= MAX_BX, "Bx out of range: {bx}");
        let mut i = (op as u32) << POS_OP;
        i |= (a as u32) << POS_A;
        i |= bx << POS_B;
        Instruction(i)
    }

    /// Create an iAsBx instruction (signed Bx).
    pub fn asbx(op: OpCode, a: u8, sbx: i32) -> Self {
        debug_assert!(
            sbx >= MIN_SBX && sbx <= MAX_SBX,
            "sBx out of range: {sbx}"
        );
        let bx = (sbx + OFFSET_SBX) as u32;
        Self::abx(op, a, bx)
    }

    /// Create an iAx instruction.
    pub fn ax(op: OpCode, ax: u32) -> Self {
        debug_assert!(ax <= MAX_AX, "Ax out of range: {ax}");
        let mut i = (op as u32) << POS_OP;
        i |= ax << POS_A;
        Instruction(i)
    }

    /// Create an isJ instruction (signed jump).
    pub fn sj(op: OpCode, sj: i32) -> Self {
        debug_assert!(
            sj >= MIN_SJ && sj <= MAX_SJ,
            "sJ out of range: {sj}"
        );
        let val = (sj + OFFSET_SJ) as u32;
        let mut i = (op as u32) << POS_OP;
        i |= val << POS_A;
        Instruction(i)
    }

    // ---- Decoders ----

    /// Get the opcode.
    pub fn opcode(&self) -> OpCode {
        let val = (self.0 >> POS_OP) & mask(SIZE_OP);
        OpCode::from_u8(val as u8).unwrap_or(OpCode::Move)
    }

    /// Get the k flag.
    pub fn k(&self) -> bool {
        ((self.0 >> POS_K) & 1) != 0
    }

    /// Get field A.
    pub fn a(&self) -> u8 {
        ((self.0 >> POS_A) & mask(SIZE_A)) as u8
    }

    /// Get field B.
    pub fn b(&self) -> u8 {
        ((self.0 >> POS_B) & mask(SIZE_B)) as u8
    }

    /// Get field C.
    pub fn c(&self) -> u8 {
        ((self.0 >> POS_C) & mask(SIZE_C)) as u8
    }

    /// Get field Bx (unsigned).
    pub fn bx(&self) -> u32 {
        (self.0 >> POS_B) & mask(SIZE_BX)
    }

    /// Get field sBx (signed).
    pub fn sbx(&self) -> i32 {
        self.bx() as i32 - OFFSET_SBX
    }

    /// Get field Ax (unsigned).
    pub fn ax_field(&self) -> u32 {
        (self.0 >> POS_A) & mask(SIZE_AX)
    }

    /// Get field sJ (signed jump).
    pub fn get_sj(&self) -> i32 {
        let val = (self.0 >> POS_A) & mask(SIZE_SJ);
        val as i32 - OFFSET_SJ
    }

    // ---- Mutators (for backpatching) ----

    /// Set field A.
    pub fn set_a(&mut self, a: u8) {
        self.0 = (self.0 & !(mask(SIZE_A) << POS_A)) | ((a as u32) << POS_A);
    }

    /// Set field sBx.
    pub fn set_sbx(&mut self, sbx: i32) {
        debug_assert!(sbx >= MIN_SBX && sbx <= MAX_SBX);
        let bx = (sbx + OFFSET_SBX) as u32;
        self.0 = (self.0 & !(mask(SIZE_BX) << POS_B)) | (bx << POS_B);
    }

    /// Set field sJ.
    pub fn set_sj(&mut self, sj: i32) {
        debug_assert!(sj >= MIN_SJ && sj <= MAX_SJ);
        let val = (sj + OFFSET_SJ) as u32;
        self.0 = (self.0 & !(mask(SIZE_SJ) << POS_A)) | (val << POS_A);
    }

    /// Set the k flag.
    pub fn set_k(&mut self, k: bool) {
        self.0 = (self.0 & !(1 << POS_K)) | ((k as u32) << POS_K);
    }
}

impl fmt::Debug for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let op = self.opcode();
        write!(f, "{}", op.name())?;
        match op.format() {
            InstructionFormat::IABC => {
                write!(f, " A={} B={} C={}", self.a(), self.b(), self.c())?;
                if self.k() {
                    write!(f, " k")?;
                }
            }
            InstructionFormat::IABx | InstructionFormat::IAsBx => {
                write!(f, " A={} Bx={}", self.a(), self.bx())?;
            }
            InstructionFormat::IAx => {
                write!(f, " Ax={}", self.ax_field())?;
            }
            InstructionFormat::IsJ => {
                write!(f, " sJ={}", self.get_sj())?;
            }
        }
        Ok(())
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_opcode_count() {
        assert_eq!(OpCode::ExtraArg as u8 + 1, OpCode::COUNT as u8);
    }

    #[test]
    fn test_all_opcodes_from_u8() {
        for i in 0..OpCode::COUNT {
            let op = OpCode::from_u8(i as u8);
            assert!(op.is_some(), "opcode {i} should be valid");
            assert_eq!(op.unwrap() as u8, i as u8);
        }
        assert!(OpCode::from_u8(OpCode::COUNT as u8).is_none());
    }

    #[test]
    fn test_abc_roundtrip() {
        let inst = Instruction::abc(OpCode::Add, 10, 20, 30, false);
        assert_eq!(inst.opcode(), OpCode::Add);
        assert_eq!(inst.a(), 10);
        assert_eq!(inst.b(), 20);
        assert_eq!(inst.c(), 30);
        assert!(!inst.k());
    }

    #[test]
    fn test_abc_with_k() {
        let inst = Instruction::abc(OpCode::Eq, 5, 10, 15, true);
        assert_eq!(inst.opcode(), OpCode::Eq);
        assert_eq!(inst.a(), 5);
        assert_eq!(inst.b(), 10);
        assert_eq!(inst.c(), 15);
        assert!(inst.k());
    }

    #[test]
    fn test_abc_max_values() {
        let inst = Instruction::abc(OpCode::Move, 255, 255, 255, true);
        assert_eq!(inst.a(), 255);
        assert_eq!(inst.b(), 255);
        assert_eq!(inst.c(), 255);
        assert!(inst.k());
    }

    #[test]
    fn test_abx_roundtrip() {
        let inst = Instruction::abx(OpCode::LoadK, 5, 1000);
        assert_eq!(inst.opcode(), OpCode::LoadK);
        assert_eq!(inst.a(), 5);
        assert_eq!(inst.bx(), 1000);
    }

    #[test]
    fn test_abx_max() {
        let inst = Instruction::abx(OpCode::LoadK, 0, MAX_BX);
        assert_eq!(inst.bx(), MAX_BX);
    }

    #[test]
    fn test_asbx_roundtrip() {
        let inst = Instruction::asbx(OpCode::ForPrep, 0, 100);
        assert_eq!(inst.opcode(), OpCode::ForPrep);
        assert_eq!(inst.sbx(), 100);

        let inst = Instruction::asbx(OpCode::ForLoop, 0, -100);
        assert_eq!(inst.sbx(), -100);
    }

    #[test]
    fn test_asbx_zero() {
        let inst = Instruction::asbx(OpCode::ForPrep, 3, 0);
        assert_eq!(inst.a(), 3);
        assert_eq!(inst.sbx(), 0);
    }

    #[test]
    fn test_asbx_boundaries() {
        let inst = Instruction::asbx(OpCode::ForLoop, 0, MAX_SBX);
        assert_eq!(inst.sbx(), MAX_SBX);

        let inst = Instruction::asbx(OpCode::ForLoop, 0, MIN_SBX);
        assert_eq!(inst.sbx(), MIN_SBX);
    }

    #[test]
    fn test_ax_roundtrip() {
        let inst = Instruction::ax(OpCode::ExtraArg, 12345);
        assert_eq!(inst.opcode(), OpCode::ExtraArg);
        assert_eq!(inst.ax_field(), 12345);
    }

    #[test]
    fn test_ax_max() {
        let inst = Instruction::ax(OpCode::ExtraArg, MAX_AX);
        assert_eq!(inst.ax_field(), MAX_AX);
    }

    #[test]
    fn test_sj_roundtrip() {
        let inst = Instruction::sj(OpCode::Jmp, 42);
        assert_eq!(inst.opcode(), OpCode::Jmp);
        assert_eq!(inst.get_sj(), 42);

        let inst = Instruction::sj(OpCode::Jmp, -42);
        assert_eq!(inst.get_sj(), -42);
    }

    #[test]
    fn test_sj_zero() {
        let inst = Instruction::sj(OpCode::Jmp, 0);
        assert_eq!(inst.get_sj(), 0);
    }

    #[test]
    fn test_sj_boundaries() {
        let inst = Instruction::sj(OpCode::Jmp, MAX_SJ);
        assert_eq!(inst.get_sj(), MAX_SJ);

        let inst = Instruction::sj(OpCode::Jmp, MIN_SJ);
        assert_eq!(inst.get_sj(), MIN_SJ);
    }

    #[test]
    fn test_set_a() {
        let mut inst = Instruction::abc(OpCode::Move, 5, 10, 15, false);
        inst.set_a(99);
        assert_eq!(inst.a(), 99);
        assert_eq!(inst.b(), 10); // preserved
        assert_eq!(inst.c(), 15); // preserved
        assert_eq!(inst.opcode(), OpCode::Move); // preserved
    }

    #[test]
    fn test_set_sbx() {
        let mut inst = Instruction::asbx(OpCode::ForLoop, 3, 100);
        inst.set_sbx(-50);
        assert_eq!(inst.sbx(), -50);
        assert_eq!(inst.a(), 3); // preserved
    }

    #[test]
    fn test_set_sj() {
        let mut inst = Instruction::sj(OpCode::Jmp, 100);
        inst.set_sj(-200);
        assert_eq!(inst.get_sj(), -200);
        assert_eq!(inst.opcode(), OpCode::Jmp); // preserved
    }

    #[test]
    fn test_set_k() {
        let mut inst = Instruction::abc(OpCode::Eq, 1, 2, 3, false);
        assert!(!inst.k());
        inst.set_k(true);
        assert!(inst.k());
        assert_eq!(inst.a(), 1); // preserved
        inst.set_k(false);
        assert!(!inst.k());
    }

    #[test]
    fn test_is_test() {
        assert!(OpCode::Eq.is_test());
        assert!(OpCode::Lt.is_test());
        assert!(OpCode::Le.is_test());
        assert!(OpCode::Test.is_test());
        assert!(OpCode::TestSet.is_test());
        assert!(!OpCode::Move.is_test());
        assert!(!OpCode::Add.is_test());
        assert!(!OpCode::Jmp.is_test());
    }

    #[test]
    fn test_format() {
        assert_eq!(OpCode::Move.format(), InstructionFormat::IABC);
        assert_eq!(OpCode::LoadK.format(), InstructionFormat::IABx);
        assert_eq!(OpCode::ExtraArg.format(), InstructionFormat::IAx);
        assert_eq!(OpCode::Jmp.format(), InstructionFormat::IsJ);
    }

    #[test]
    fn test_opcode_names() {
        assert_eq!(OpCode::Move.name(), "MOVE");
        assert_eq!(OpCode::LoadK.name(), "LOADK");
        assert_eq!(OpCode::Add.name(), "ADD");
        assert_eq!(OpCode::Jmp.name(), "JMP");
        assert_eq!(OpCode::Return.name(), "RETURN");
        assert_eq!(OpCode::ExtraArg.name(), "EXTRAARG");
    }

    #[test]
    fn test_debug_display() {
        let inst = Instruction::abc(OpCode::Add, 1, 2, 3, false);
        let s = format!("{inst:?}");
        assert!(s.contains("ADD"));
        assert!(s.contains("A=1"));

        let inst = Instruction::sj(OpCode::Jmp, -5);
        let s = format!("{inst:?}");
        assert!(s.contains("JMP"));
        assert!(s.contains("sJ=-5"));
    }

    #[test]
    fn test_mutation_preserves_other_fields() {
        let mut inst = Instruction::abc(OpCode::Eq, 10, 20, 30, true);
        inst.set_a(50);
        assert_eq!(inst.opcode(), OpCode::Eq);
        assert_eq!(inst.b(), 20);
        assert_eq!(inst.c(), 30);
        assert!(inst.k());
    }
}
