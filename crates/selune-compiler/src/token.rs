use selune_core::string::StringId;
use std::fmt;

/// Source location span.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    pub line: u32,
    pub column: u32,
}

/// A token with its source location.
#[derive(Clone, Debug, PartialEq)]
pub struct SpannedToken {
    pub token: Token,
    pub span: Span,
}

/// All Lua 5.4 tokens.
#[derive(Clone, Debug, PartialEq)]
pub enum Token {
    // --- Keywords (22) ---
    And,
    Break,
    Do,
    Else,
    ElseIf,
    End,
    False,
    For,
    Function,
    Goto,
    If,
    In,
    Local,
    Nil,
    Not,
    Or,
    Repeat,
    Return,
    Then,
    True,
    Until,
    While,

    // --- Literals ---
    Integer(i64),
    Float(f64),
    String(StringId),
    Name(StringId),

    // --- Single-char operators/punctuation ---
    Plus,       // +
    Minus,      // -
    Star,       // *
    Slash,      // /
    Percent,    // %
    Caret,      // ^
    Hash,       // #
    Ampersand,  // &
    Tilde,      // ~
    Pipe,       // |
    Less,       // <
    Greater,    // >
    Assign,     // =
    LParen,     // (
    RParen,     // )
    LBrace,     // {
    RBrace,     // }
    LBracket,   // [
    RBracket,   // ]
    DoubleColon, // ::
    Semi,       // ;
    Colon,      // :
    Comma,      // ,
    Dot,        // .

    // --- Multi-char operators ---
    ShiftLeft,  // <<
    ShiftRight, // >>
    FloorDiv,   // //
    Equal,      // ==
    NotEqual,   // ~=
    LessEq,     // <=
    GreaterEq,  // >=
    DotDot,     // ..
    DotDotDot,  // ...
    // DoubleColon is above

    // --- EOF ---
    Eof,
}

impl Token {
    /// Try to match a keyword from an identifier string.
    pub fn keyword_from_str(s: &str) -> Option<Token> {
        match s {
            "and" => Some(Token::And),
            "break" => Some(Token::Break),
            "do" => Some(Token::Do),
            "else" => Some(Token::Else),
            "elseif" => Some(Token::ElseIf),
            "end" => Some(Token::End),
            "false" => Some(Token::False),
            "for" => Some(Token::For),
            "function" => Some(Token::Function),
            "goto" => Some(Token::Goto),
            "if" => Some(Token::If),
            "in" => Some(Token::In),
            "local" => Some(Token::Local),
            "nil" => Some(Token::Nil),
            "not" => Some(Token::Not),
            "or" => Some(Token::Or),
            "repeat" => Some(Token::Repeat),
            "return" => Some(Token::Return),
            "then" => Some(Token::Then),
            "true" => Some(Token::True),
            "until" => Some(Token::Until),
            "while" => Some(Token::While),
            _ => None,
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::And => write!(f, "and"),
            Token::Break => write!(f, "break"),
            Token::Do => write!(f, "do"),
            Token::Else => write!(f, "else"),
            Token::ElseIf => write!(f, "elseif"),
            Token::End => write!(f, "end"),
            Token::False => write!(f, "false"),
            Token::For => write!(f, "for"),
            Token::Function => write!(f, "function"),
            Token::Goto => write!(f, "goto"),
            Token::If => write!(f, "if"),
            Token::In => write!(f, "in"),
            Token::Local => write!(f, "local"),
            Token::Nil => write!(f, "nil"),
            Token::Not => write!(f, "not"),
            Token::Or => write!(f, "or"),
            Token::Repeat => write!(f, "repeat"),
            Token::Return => write!(f, "return"),
            Token::Then => write!(f, "then"),
            Token::True => write!(f, "true"),
            Token::Until => write!(f, "until"),
            Token::While => write!(f, "while"),
            Token::Integer(i) => write!(f, "{i}"),
            Token::Float(fl) => write!(f, "{fl}"),
            Token::String(_) => write!(f, "<string>"),
            Token::Name(_) => write!(f, "<name>"),
            Token::Plus => write!(f, "+"),
            Token::Minus => write!(f, "-"),
            Token::Star => write!(f, "*"),
            Token::Slash => write!(f, "/"),
            Token::Percent => write!(f, "%"),
            Token::Caret => write!(f, "^"),
            Token::Hash => write!(f, "#"),
            Token::Ampersand => write!(f, "&"),
            Token::Tilde => write!(f, "~"),
            Token::Pipe => write!(f, "|"),
            Token::Less => write!(f, "<"),
            Token::Greater => write!(f, ">"),
            Token::Assign => write!(f, "="),
            Token::LParen => write!(f, "("),
            Token::RParen => write!(f, ")"),
            Token::LBrace => write!(f, "{{"),
            Token::RBrace => write!(f, "}}"),
            Token::LBracket => write!(f, "["),
            Token::RBracket => write!(f, "]"),
            Token::DoubleColon => write!(f, "::"),
            Token::Semi => write!(f, ";"),
            Token::Colon => write!(f, ":"),
            Token::Comma => write!(f, ","),
            Token::Dot => write!(f, "."),
            Token::ShiftLeft => write!(f, "<<"),
            Token::ShiftRight => write!(f, ">>"),
            Token::FloorDiv => write!(f, "//"),
            Token::Equal => write!(f, "=="),
            Token::NotEqual => write!(f, "~="),
            Token::LessEq => write!(f, "<="),
            Token::GreaterEq => write!(f, ">="),
            Token::DotDot => write!(f, ".."),
            Token::DotDotDot => write!(f, "..."),
            Token::Eof => write!(f, "<eof>"),
        }
    }
}
