/// Expression description and expression compilation.
use selune_core::string::StringId;

/// Describes where an expression's value currently lives.
#[derive(Clone, Debug)]
pub enum ExprDesc {
    /// No value (statement result).
    Void,
    /// Nil literal.
    Nil,
    /// True literal.
    True,
    /// False literal.
    False,
    /// Integer literal.
    Integer(i64),
    /// Float literal.
    Float(f64),
    /// String literal.
    Str(StringId),
    /// Value in a register.
    Register(u8),
    /// Upvalue at the given index.
    Upvalue(u8),
    /// Constant at the given index.
    Constant(u32),
    /// Indexed: table in register, key info.
    Indexed { table: u8, key: IndexKey },
    /// Relocatable: instruction at PC whose destination register is not yet set.
    Relocatable(usize),
    /// Jump: the expression is the result of a comparison, with a jump PC.
    Jump(usize),
    /// Function call result: instruction at PC.
    Call(usize),
    /// Vararg expression: instruction at PC.
    Vararg(usize),
    /// Global variable: _ENV[name_constant], upvalue index + constant index.
    Global { env_upval: u8, name_k: u32 },
}

/// Key type for table indexing.
#[derive(Clone, Debug)]
pub enum IndexKey {
    /// Key is a constant string (for field access).
    Field(u32), // constant index
    /// Key is in a register.
    Register(u8),
    /// Key is an integer constant.
    Integer(u8), // the integer value fits in u8
    /// Key is a constant.
    Constant(u32),
}

impl ExprDesc {
    /// Returns true if this is a literal constant that doesn't need a register.
    pub fn is_literal(&self) -> bool {
        matches!(
            self,
            ExprDesc::Nil
                | ExprDesc::True
                | ExprDesc::False
                | ExprDesc::Integer(_)
                | ExprDesc::Float(_)
                | ExprDesc::Str(_)
        )
    }

    /// Returns true if this expression has a definite single value.
    pub fn has_value(&self) -> bool {
        !matches!(self, ExprDesc::Void)
    }
}

/// Binary operator with precedence info.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    IDiv,
    Mod,
    Pow,
    Concat,
    Shl,
    Shr,
    BAnd,
    BOr,
    BXor,
    Eq,
    NotEq,
    Lt,
    LtEq,
    Gt,
    GtEq,
    And,
    Or,
}

/// Unary operator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    BNot,
    Not,
    Len,
}

/// Operator precedence level (higher = binds tighter).
/// Returns (left priority, right priority).
impl BinOp {
    pub fn priority(self) -> (u8, u8) {
        match self {
            BinOp::Or => (1, 1),
            BinOp::And => (2, 2),
            BinOp::Lt | BinOp::Gt | BinOp::LtEq | BinOp::GtEq | BinOp::NotEq | BinOp::Eq => (3, 3),
            BinOp::BOr => (4, 4),
            BinOp::BXor => (5, 5),
            BinOp::BAnd => (6, 6),
            BinOp::Shl | BinOp::Shr => (7, 7),
            BinOp::Concat => (8, 7), // right-associative
            BinOp::Add | BinOp::Sub => (10, 10),
            BinOp::Mul | BinOp::Div | BinOp::IDiv | BinOp::Mod => (11, 11),
            BinOp::Pow => (14, 13), // right-associative
        }
    }

    pub fn is_comparison(self) -> bool {
        matches!(
            self,
            BinOp::Eq | BinOp::NotEq | BinOp::Lt | BinOp::LtEq | BinOp::Gt | BinOp::GtEq
        )
    }
}

/// Minimum precedence for unary operators.
pub const UNARY_PRIORITY: u8 = 12;
