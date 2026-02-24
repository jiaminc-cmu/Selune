use crate::token::{Span, SpannedToken, Token};
use selune_core::string::StringInterner;
use std::fmt;

/// Lexer error.
#[derive(Clone, Debug, PartialEq)]
pub struct LexError {
    pub message: String,
    pub line: u32,
    pub column: u32,
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}: {}", self.line, self.column, self.message)
    }
}

impl std::error::Error for LexError {}

/// Pull-based lexer for Lua 5.4.
pub struct Lexer<'a> {
    source: &'a [u8],
    pos: usize,
    line: u32,
    column: u32,
    current: Option<Result<SpannedToken, LexError>>,
    pub strings: StringInterner,
    /// Original text of the current token (used for error messages, e.g., "near '1.000'")
    pub token_text: String,
    /// Line number of the last consumed token (like PUC's ls->lastline).
    pub lastline: u32,
}

impl<'a> Lexer<'a> {
    /// Create a new lexer from source bytes.
    pub fn new(source: &'a [u8]) -> Self {
        let mut lexer = Lexer {
            source,
            pos: 0,
            line: 1,
            column: 1,
            current: None,
            strings: StringInterner::new(),
            token_text: String::new(),
            lastline: 1,
        };
        // Prime the first token
        lexer.current = Some(lexer.scan_token());
        lexer
    }

    /// Create a new lexer reusing an existing string interner.
    pub fn with_strings(source: &'a [u8], strings: StringInterner) -> Self {
        let mut lexer = Lexer {
            source,
            pos: 0,
            line: 1,
            column: 1,
            current: None,
            strings,
            token_text: String::new(),
            lastline: 1,
        };
        // Prime the first token using the provided interner
        lexer.current = Some(lexer.scan_token());
        lexer
    }

    /// Peek at the current token without consuming.
    pub fn current(&self) -> Result<&SpannedToken, &LexError> {
        match &self.current {
            Some(Ok(tok)) => Ok(tok),
            Some(Err(e)) => Err(e),
            None => unreachable!("lexer should always have a current token"),
        }
    }

    /// Consume the current token and advance to the next one.
    pub fn advance(&mut self) -> Result<SpannedToken, LexError> {
        // Record the line of the token being consumed (like PUC's lastline)
        if let Some(Ok(ref tok)) = self.current {
            self.lastline = tok.span.line;
        }
        let prev = self.current.take().unwrap();
        self.current = Some(self.scan_token());
        prev
    }

    /// Get current line number.
    pub fn line(&self) -> u32 {
        self.line
    }

    // ---- Internal scanning ----

    fn peek(&self) -> Option<u8> {
        self.source.get(self.pos).copied()
    }

    fn peek_at(&self, offset: usize) -> Option<u8> {
        self.source.get(self.pos + offset).copied()
    }

    fn advance_char(&mut self) -> Option<u8> {
        let ch = self.source.get(self.pos).copied()?;
        self.pos += 1;
        if ch == b'\n' {
            // \n\r counts as one newline (Lua 5.4)
            if self.peek() == Some(b'\r') {
                self.pos += 1;
            }
            self.line += 1;
            self.column = 1;
        } else if ch == b'\r' {
            // \r\n counts as one newline
            if self.peek() == Some(b'\n') {
                self.pos += 1;
            }
            self.line += 1;
            self.column = 1;
        } else {
            self.column += 1;
        }
        Some(ch)
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            // Skip whitespace
            while let Some(ch) = self.peek() {
                if ch == b' '
                    || ch == b'\t'
                    || ch == b'\n'
                    || ch == b'\r'
                    || ch == b'\x0C'
                    || ch == b'\x0B'
                {
                    self.advance_char();
                } else {
                    break;
                }
            }

            // Check for comments
            if self.peek() == Some(b'-') && self.peek_at(1) == Some(b'-') {
                self.advance_char(); // -
                self.advance_char(); // -
                if self.peek() == Some(b'[') {
                    if let Some(level) = self.check_long_bracket() {
                        // Long comment
                        if self.scan_long_string_content(level).is_err() {
                            // Error will be caught when we try to scan the next token
                            return;
                        }
                        continue;
                    }
                }
                // Short comment: skip to end of line
                while let Some(ch) = self.peek() {
                    if ch == b'\n' || ch == b'\r' {
                        break;
                    }
                    self.advance_char();
                }
                continue;
            }

            break;
        }
    }

    /// Check if current position starts a long bracket `[=*[`. Returns the level if so.
    fn check_long_bracket(&self) -> Option<usize> {
        if self.peek() != Some(b'[') {
            return None;
        }
        let mut level = 0;
        let mut offset = 1;
        while self.peek_at(offset) == Some(b'=') {
            level += 1;
            offset += 1;
        }
        if self.peek_at(offset) == Some(b'[') {
            Some(level)
        } else {
            None
        }
    }

    fn scan_token(&mut self) -> Result<SpannedToken, LexError> {
        self.skip_whitespace_and_comments();

        let token_start = self.pos;
        let result = self.scan_token_inner();
        // Set token_text from the source bytes consumed
        let token_end = self.pos;
        if token_start < token_end && token_start < self.source.len() {
            self.token_text =
                String::from_utf8_lossy(&self.source[token_start..token_end]).into_owned();
        }
        result
    }

    fn scan_token_inner(&mut self) -> Result<SpannedToken, LexError> {
        let span = Span {
            line: self.line,
            column: self.column,
        };

        let ch = match self.peek() {
            Some(ch) => ch,
            None => {
                self.token_text = "<eof>".to_string();
                return Ok(SpannedToken {
                    token: Token::Eof,
                    span,
                });
            }
        };

        match ch {
            b'+' => {
                self.advance_char();
                Ok(SpannedToken {
                    token: Token::Plus,
                    span,
                })
            }
            b'*' => {
                self.advance_char();
                Ok(SpannedToken {
                    token: Token::Star,
                    span,
                })
            }
            b'^' => {
                self.advance_char();
                Ok(SpannedToken {
                    token: Token::Caret,
                    span,
                })
            }
            b'%' => {
                self.advance_char();
                Ok(SpannedToken {
                    token: Token::Percent,
                    span,
                })
            }
            b'&' => {
                self.advance_char();
                Ok(SpannedToken {
                    token: Token::Ampersand,
                    span,
                })
            }
            b'|' => {
                self.advance_char();
                Ok(SpannedToken {
                    token: Token::Pipe,
                    span,
                })
            }
            b'(' => {
                self.advance_char();
                Ok(SpannedToken {
                    token: Token::LParen,
                    span,
                })
            }
            b')' => {
                self.advance_char();
                Ok(SpannedToken {
                    token: Token::RParen,
                    span,
                })
            }
            b'{' => {
                self.advance_char();
                Ok(SpannedToken {
                    token: Token::LBrace,
                    span,
                })
            }
            b'}' => {
                self.advance_char();
                Ok(SpannedToken {
                    token: Token::RBrace,
                    span,
                })
            }
            b']' => {
                self.advance_char();
                Ok(SpannedToken {
                    token: Token::RBracket,
                    span,
                })
            }
            b';' => {
                self.advance_char();
                Ok(SpannedToken {
                    token: Token::Semi,
                    span,
                })
            }
            b',' => {
                self.advance_char();
                Ok(SpannedToken {
                    token: Token::Comma,
                    span,
                })
            }
            b'#' => {
                self.advance_char();
                Ok(SpannedToken {
                    token: Token::Hash,
                    span,
                })
            }
            b'-' => {
                self.advance_char();
                // Comments already handled in skip_whitespace_and_comments
                Ok(SpannedToken {
                    token: Token::Minus,
                    span,
                })
            }
            b'/' => {
                self.advance_char();
                if self.peek() == Some(b'/') {
                    self.advance_char();
                    Ok(SpannedToken {
                        token: Token::FloorDiv,
                        span,
                    })
                } else {
                    Ok(SpannedToken {
                        token: Token::Slash,
                        span,
                    })
                }
            }
            b'<' => {
                self.advance_char();
                if self.peek() == Some(b'<') {
                    self.advance_char();
                    Ok(SpannedToken {
                        token: Token::ShiftLeft,
                        span,
                    })
                } else if self.peek() == Some(b'=') {
                    self.advance_char();
                    Ok(SpannedToken {
                        token: Token::LessEq,
                        span,
                    })
                } else {
                    Ok(SpannedToken {
                        token: Token::Less,
                        span,
                    })
                }
            }
            b'>' => {
                self.advance_char();
                if self.peek() == Some(b'>') {
                    self.advance_char();
                    Ok(SpannedToken {
                        token: Token::ShiftRight,
                        span,
                    })
                } else if self.peek() == Some(b'=') {
                    self.advance_char();
                    Ok(SpannedToken {
                        token: Token::GreaterEq,
                        span,
                    })
                } else {
                    Ok(SpannedToken {
                        token: Token::Greater,
                        span,
                    })
                }
            }
            b'=' => {
                self.advance_char();
                if self.peek() == Some(b'=') {
                    self.advance_char();
                    Ok(SpannedToken {
                        token: Token::Equal,
                        span,
                    })
                } else {
                    Ok(SpannedToken {
                        token: Token::Assign,
                        span,
                    })
                }
            }
            b'~' => {
                self.advance_char();
                if self.peek() == Some(b'=') {
                    self.advance_char();
                    Ok(SpannedToken {
                        token: Token::NotEqual,
                        span,
                    })
                } else {
                    Ok(SpannedToken {
                        token: Token::Tilde,
                        span,
                    })
                }
            }
            b':' => {
                self.advance_char();
                if self.peek() == Some(b':') {
                    self.advance_char();
                    Ok(SpannedToken {
                        token: Token::DoubleColon,
                        span,
                    })
                } else {
                    Ok(SpannedToken {
                        token: Token::Colon,
                        span,
                    })
                }
            }
            b'.' => {
                self.advance_char();
                if self.peek() == Some(b'.') {
                    self.advance_char();
                    if self.peek() == Some(b'.') {
                        self.advance_char();
                        Ok(SpannedToken {
                            token: Token::DotDotDot,
                            span,
                        })
                    } else {
                        Ok(SpannedToken {
                            token: Token::DotDot,
                            span,
                        })
                    }
                } else if self.peek().is_some_and(|c| c.is_ascii_digit()) {
                    // Number starting with .
                    self.scan_number_after_dot(span)
                } else {
                    Ok(SpannedToken {
                        token: Token::Dot,
                        span,
                    })
                }
            }
            b'[' => {
                if let Some(level) = self.check_long_bracket() {
                    self.scan_long_string(level, span)
                } else {
                    self.advance_char();
                    Ok(SpannedToken {
                        token: Token::LBracket,
                        span,
                    })
                }
            }
            b'"' | b'\'' => self.scan_short_string(span),
            b'0'..=b'9' => self.scan_number(span),
            _ if is_ident_start(ch) => self.scan_name(span),
            _ => {
                self.advance_char();
                // PUC Lua format: "unexpected symbol near '<\X>'" for non-printable,
                // "unexpected symbol near 'c'" for printable chars
                let near_str = if ch.is_ascii_graphic() || ch == b' ' {
                    format!("'{}'", ch as char)
                } else {
                    format!("'<\\{}>'", ch)
                };
                Err(LexError {
                    message: format!("unexpected symbol near {}", near_str),
                    line: span.line,
                    column: span.column,
                })
            }
        }
    }

    fn scan_name(&mut self, span: Span) -> Result<SpannedToken, LexError> {
        let start = self.pos;
        while let Some(ch) = self.peek() {
            if is_ident_continue(ch) {
                self.advance_char();
            } else {
                break;
            }
        }
        let name = &self.source[start..self.pos];
        let name_str = std::str::from_utf8(name).unwrap_or("");

        if let Some(keyword) = Token::keyword_from_str(name_str) {
            Ok(SpannedToken {
                token: keyword,
                span,
            })
        } else {
            let id = self.strings.intern_or_create(name);
            Ok(SpannedToken {
                token: Token::Name(id),
                span,
            })
        }
    }

    fn scan_number(&mut self, span: Span) -> Result<SpannedToken, LexError> {
        let start = self.pos;

        if self.peek() == Some(b'0') && self.peek_at(1).is_some_and(|c| c == b'x' || c == b'X') {
            // Hex number
            self.advance_char(); // 0
            self.advance_char(); // x/X
            self.scan_hex_number(start, span)
        } else {
            self.scan_decimal_number(start, span)
        }
    }

    fn scan_decimal_number(&mut self, start: usize, span: Span) -> Result<SpannedToken, LexError> {
        let mut is_float = false;

        // Integer part
        while let Some(ch) = self.peek() {
            if ch.is_ascii_digit() {
                self.advance_char();
            } else {
                break;
            }
        }

        // Fractional part
        if self.peek() == Some(b'.') && self.peek_at(1) != Some(b'.') {
            is_float = true;
            self.advance_char(); // .
            while let Some(ch) = self.peek() {
                if ch.is_ascii_digit() {
                    self.advance_char();
                } else {
                    break;
                }
            }
        }

        // Exponent
        if let Some(ch) = self.peek() {
            if ch == b'e' || ch == b'E' {
                is_float = true;
                self.advance_char();
                if let Some(s) = self.peek() {
                    if s == b'+' || s == b'-' {
                        self.advance_char();
                    }
                }
                let exp_start = self.pos;
                while let Some(ch) = self.peek() {
                    if ch.is_ascii_digit() {
                        self.advance_char();
                    } else {
                        break;
                    }
                }
                if self.pos == exp_start {
                    return Err(LexError {
                        message: "malformed number: expected exponent digits".to_string(),
                        line: span.line,
                        column: span.column,
                    });
                }
            }
        }

        // After a number, if the next char is a letter or underscore, it's malformed
        if let Some(ch) = self.peek() {
            if ch.is_ascii_alphabetic() || ch == b'_' {
                // Consume the rest of the "word" for better error messages
                while let Some(ch) = self.peek() {
                    if ch.is_ascii_alphanumeric() || ch == b'_' || ch == b'.' {
                        self.advance_char();
                    } else {
                        break;
                    }
                }
                let text = std::str::from_utf8(&self.source[start..self.pos]).unwrap_or("?");
                return Err(LexError {
                    message: format!("malformed number near '{text}'"),
                    line: span.line,
                    column: span.column,
                });
            }
        }

        let text = std::str::from_utf8(&self.source[start..self.pos]).unwrap();

        if is_float {
            match text.parse::<f64>() {
                Ok(f) => Ok(SpannedToken {
                    token: Token::Float(f),
                    span,
                }),
                Err(_) => Err(LexError {
                    message: format!("malformed number: '{text}'"),
                    line: span.line,
                    column: span.column,
                }),
            }
        } else {
            match text.parse::<i64>() {
                Ok(i) => Ok(SpannedToken {
                    token: Token::Integer(i),
                    span,
                }),
                Err(_) => {
                    // Try as float if too large for i64
                    match text.parse::<f64>() {
                        Ok(f) => Ok(SpannedToken {
                            token: Token::Float(f),
                            span,
                        }),
                        Err(_) => Err(LexError {
                            message: format!("malformed number: '{text}'"),
                            line: span.line,
                            column: span.column,
                        }),
                    }
                }
            }
        }
    }

    fn scan_hex_number(&mut self, start: usize, span: Span) -> Result<SpannedToken, LexError> {
        let mut is_float = false;

        let hex_start = self.pos;
        while let Some(ch) = self.peek() {
            if ch.is_ascii_hexdigit() {
                self.advance_char();
            } else {
                break;
            }
        }

        // Fractional part
        if self.peek() == Some(b'.') {
            is_float = true;
            self.advance_char();
            while let Some(ch) = self.peek() {
                if ch.is_ascii_hexdigit() {
                    self.advance_char();
                } else {
                    break;
                }
            }
        }

        // Binary exponent (required for hex float)
        if let Some(ch) = self.peek() {
            if ch == b'p' || ch == b'P' {
                is_float = true;
                self.advance_char();
                if let Some(s) = self.peek() {
                    if s == b'+' || s == b'-' {
                        self.advance_char();
                    }
                }
                let exp_start = self.pos;
                while let Some(ch) = self.peek() {
                    if ch.is_ascii_digit() {
                        self.advance_char();
                    } else {
                        break;
                    }
                }
                if self.pos == exp_start {
                    return Err(LexError {
                        message: "malformed number: expected exponent digits".to_string(),
                        line: span.line,
                        column: span.column,
                    });
                }
            }
        }

        if !is_float && self.pos == hex_start {
            return Err(LexError {
                message: "malformed number: no hex digits after '0x'".to_string(),
                line: span.line,
                column: span.column,
            });
        }

        // After a number, if the next char is a letter or underscore, it's malformed
        if let Some(ch) = self.peek() {
            if ch.is_ascii_alphabetic() || ch == b'_' {
                while let Some(ch) = self.peek() {
                    if ch.is_ascii_alphanumeric() || ch == b'_' || ch == b'.' {
                        self.advance_char();
                    } else {
                        break;
                    }
                }
                let text = std::str::from_utf8(&self.source[start..self.pos]).unwrap_or("?");
                return Err(LexError {
                    message: format!("malformed number near '{text}'"),
                    line: span.line,
                    column: span.column,
                });
            }
        }

        let text = std::str::from_utf8(&self.source[start..self.pos]).unwrap();

        if is_float {
            // Parse hex float manually
            match parse_hex_float(text) {
                Some(f) => Ok(SpannedToken {
                    token: Token::Float(f),
                    span,
                }),
                None => Err(LexError {
                    message: format!("malformed hex float: '{text}'"),
                    line: span.line,
                    column: span.column,
                }),
            }
        } else {
            // Parse hex int: strip 0x prefix, wrapping on overflow (Lua 5.4 behavior)
            let hex_digits = &text[2..];
            let mut val: u64 = 0;
            let mut valid = !hex_digits.is_empty();
            for ch in hex_digits.bytes() {
                if ch.is_ascii_hexdigit() {
                    val = val.wrapping_mul(16).wrapping_add(hex_value(ch) as u64);
                } else {
                    valid = false;
                    break;
                }
            }
            if valid {
                Ok(SpannedToken {
                    token: Token::Integer(val as i64),
                    span,
                })
            } else {
                Err(LexError {
                    message: format!("malformed hex number: '{text}'"),
                    line: span.line,
                    column: span.column,
                })
            }
        }
    }

    /// Scan a number that started with a dot (already consumed).
    fn scan_number_after_dot(&mut self, span: Span) -> Result<SpannedToken, LexError> {
        let start = self.pos - 1; // include the dot
        while let Some(ch) = self.peek() {
            if ch.is_ascii_digit() {
                self.advance_char();
            } else {
                break;
            }
        }
        // Exponent
        if let Some(ch) = self.peek() {
            if ch == b'e' || ch == b'E' {
                self.advance_char();
                if let Some(s) = self.peek() {
                    if s == b'+' || s == b'-' {
                        self.advance_char();
                    }
                }
                let exp_start = self.pos;
                while let Some(ch) = self.peek() {
                    if ch.is_ascii_digit() {
                        self.advance_char();
                    } else {
                        break;
                    }
                }
                if self.pos == exp_start {
                    return Err(LexError {
                        message: "malformed number: expected exponent digits".to_string(),
                        line: span.line,
                        column: span.column,
                    });
                }
            }
        }
        let text = std::str::from_utf8(&self.source[start..self.pos]).unwrap();
        match text.parse::<f64>() {
            Ok(f) => Ok(SpannedToken {
                token: Token::Float(f),
                span,
            }),
            Err(_) => Err(LexError {
                message: format!("malformed number: '{text}'"),
                line: span.line,
                column: span.column,
            }),
        }
    }

    /// Build the "near" token for string error messages.
    /// Shows the string content from `start_pos` to current position.
    /// If `include_current` is true, includes the character at self.pos.
    fn string_near_token(&self, start_pos: usize, include_current: bool) -> String {
        let end = if include_current && self.pos < self.source.len() {
            self.pos + 1
        } else {
            self.pos
        };
        let end = end.min(self.source.len());
        let raw = &self.source[start_pos..end];
        // Truncate to reasonable length
        let truncated = if raw.len() > 50 { &raw[..50] } else { raw };
        let s = String::from_utf8_lossy(truncated);
        format!("'{}'", s)
    }

    fn scan_short_string(&mut self, span: Span) -> Result<SpannedToken, LexError> {
        let string_start = self.pos; // position of the opening quote
        let quote = self.advance_char().unwrap();
        let mut buf = Vec::new();

        loop {
            match self.peek() {
                None => {
                    return Err(LexError {
                        message: "unfinished string near <eof>".to_string(),
                        line: span.line,
                        column: span.column,
                    });
                }
                Some(ch) if ch == b'\n' || ch == b'\r' => {
                    return Err(LexError {
                        message: format!(
                            "unfinished string near {}",
                            self.string_near_token(string_start, false)
                        ),
                        line: span.line,
                        column: span.column,
                    });
                }
                Some(ch) if ch == quote => {
                    self.advance_char();
                    break;
                }
                Some(b'\\') => {
                    self.advance_char(); // consume backslash
                    match self.peek() {
                        Some(b'a') => {
                            self.advance_char();
                            buf.push(0x07);
                        }
                        Some(b'b') => {
                            self.advance_char();
                            buf.push(0x08);
                        }
                        Some(b'f') => {
                            self.advance_char();
                            buf.push(0x0C);
                        }
                        Some(b'n') => {
                            self.advance_char();
                            buf.push(b'\n');
                        }
                        Some(b'r') => {
                            self.advance_char();
                            buf.push(b'\r');
                        }
                        Some(b't') => {
                            self.advance_char();
                            buf.push(b'\t');
                        }
                        Some(b'v') => {
                            self.advance_char();
                            buf.push(0x0B);
                        }
                        Some(b'\\') => {
                            self.advance_char();
                            buf.push(b'\\');
                        }
                        Some(b'\'') => {
                            self.advance_char();
                            buf.push(b'\'');
                        }
                        Some(b'"') => {
                            self.advance_char();
                            buf.push(b'"');
                        }
                        Some(b'\n') => {
                            self.advance_char();
                            buf.push(b'\n');
                        }
                        Some(b'\r') => {
                            self.advance_char();
                            // \r\n already handled in advance_char
                            buf.push(b'\n');
                        }
                        Some(b'x') => {
                            self.advance_char();
                            let h1 = match self.peek() {
                                Some(ch) if ch.is_ascii_hexdigit() => {
                                    self.advance_char();
                                    hex_value(ch)
                                }
                                _ => {
                                    return Err(LexError {
                                        message: format!(
                                            "invalid escape sequence near {}",
                                            self.string_near_token(string_start, true)
                                        ),
                                        line: span.line,
                                        column: span.column,
                                    })
                                }
                            };
                            let h2 = match self.peek() {
                                Some(ch) if ch.is_ascii_hexdigit() => {
                                    self.advance_char();
                                    hex_value(ch)
                                }
                                _ => {
                                    return Err(LexError {
                                        message: format!(
                                            "invalid escape sequence near {}",
                                            self.string_near_token(string_start, true)
                                        ),
                                        line: span.line,
                                        column: span.column,
                                    })
                                }
                            };
                            buf.push((h1 << 4) | h2);
                        }
                        Some(b'u') => {
                            self.advance_char();
                            match self.peek() {
                                Some(b'{') => {
                                    self.advance_char();
                                }
                                _ => {
                                    return Err(LexError {
                                        message: format!(
                                            "invalid escape sequence near {}",
                                            self.string_near_token(string_start, true)
                                        ),
                                        line: span.line,
                                        column: span.column,
                                    })
                                }
                            }
                            let mut code: u64 = 0;
                            let mut count = 0;
                            loop {
                                match self.peek() {
                                    Some(b'}') => {
                                        self.advance_char();
                                        break;
                                    }
                                    Some(ch) if ch.is_ascii_hexdigit() => {
                                        self.advance_char();
                                        code = code * 16 + hex_value(ch) as u64;
                                        count += 1;
                                        if code > 0x7FFF_FFFF {
                                            return Err(LexError {
                                                message: format!(
                                                    "UTF-8 value too large near {}",
                                                    self.string_near_token(string_start, false)
                                                ),
                                                line: span.line,
                                                column: span.column,
                                            });
                                        }
                                    }
                                    _ => {
                                        return Err(LexError {
                                            message: format!(
                                                "invalid escape sequence near {}",
                                                self.string_near_token(string_start, true)
                                            ),
                                            line: span.line,
                                            column: span.column,
                                        });
                                    }
                                }
                            }
                            if count == 0 {
                                return Err(LexError {
                                    message: format!(
                                        "missing unicode value near {}",
                                        self.string_near_token(string_start, true)
                                    ),
                                    line: span.line,
                                    column: span.column,
                                });
                            }
                            // Encode as UTF-8 (Lua 5.4 supports up to 0x7FFFFFFF)
                            encode_utf8_lua(code as u32, &mut buf);
                        }
                        Some(b'z') => {
                            self.advance_char();
                            // Skip following whitespace
                            while let Some(ch) = self.peek() {
                                if ch == b' '
                                    || ch == b'\t'
                                    || ch == b'\n'
                                    || ch == b'\r'
                                    || ch == b'\x0C'
                                    || ch == b'\x0B'
                                {
                                    self.advance_char();
                                } else {
                                    break;
                                }
                            }
                        }
                        Some(ch) if ch.is_ascii_digit() => {
                            // \ddd - up to 3 decimal digits
                            let mut val: u16 = (ch - b'0') as u16;
                            self.advance_char();
                            for _ in 0..2 {
                                if let Some(d) = self.peek() {
                                    if d.is_ascii_digit() {
                                        val = val * 10 + (d - b'0') as u16;
                                        self.advance_char();
                                    } else {
                                        break;
                                    }
                                }
                            }
                            if val > 255 {
                                return Err(LexError {
                                    message: format!(
                                        "decimal escape too large near {}",
                                        self.string_near_token(string_start, true)
                                    ),
                                    line: span.line,
                                    column: span.column,
                                });
                            }
                            buf.push(val as u8);
                        }
                        Some(_ch) => {
                            return Err(LexError {
                                message: format!(
                                    "invalid escape sequence near {}",
                                    self.string_near_token(string_start, true)
                                ),
                                line: span.line,
                                column: span.column,
                            });
                        }
                        None => {
                            return Err(LexError {
                                message: "unfinished string near <eof>".to_string(),
                                line: span.line,
                                column: span.column,
                            });
                        }
                    }
                }
                Some(ch) => {
                    self.advance_char();
                    buf.push(ch);
                }
            }
        }

        let id = self.strings.intern_or_create(&buf);
        Ok(SpannedToken {
            token: Token::String(id),
            span,
        })
    }

    fn scan_long_string(&mut self, level: usize, span: Span) -> Result<SpannedToken, LexError> {
        // Skip opening [=*[
        self.advance_char(); // [
        for _ in 0..level {
            self.advance_char(); // =
        }
        self.advance_char(); // [

        let content = self.scan_long_string_content(level)?;
        let id = self.strings.intern_or_create(&content);
        Ok(SpannedToken {
            token: Token::String(id),
            span,
        })
    }

    fn scan_long_string_content(&mut self, level: usize) -> Result<Vec<u8>, LexError> {
        let mut buf = Vec::new();
        let mut first_newline = true;

        loop {
            match self.peek() {
                None => {
                    return Err(LexError {
                        message: "unfinished long string near <eof>".to_string(),
                        line: self.line,
                        column: self.column,
                    });
                }
                Some(b']') => {
                    if self.check_closing_long_bracket(level) {
                        // Skip closing ]=*]
                        self.advance_char(); // ]
                        for _ in 0..level {
                            self.advance_char(); // =
                        }
                        self.advance_char(); // ]
                        return Ok(buf);
                    }
                    self.advance_char();
                    buf.push(b']');
                }
                Some(b'\n') | Some(b'\r') => {
                    self.advance_char();
                    if first_newline && buf.is_empty() {
                        // Strip first newline of long string
                        first_newline = false;
                        continue;
                    }
                    // Normalize line endings to \n
                    buf.push(b'\n');
                    first_newline = false;
                }
                Some(ch) => {
                    first_newline = false;
                    self.advance_char();
                    buf.push(ch);
                }
            }
        }
    }

    fn check_closing_long_bracket(&self, level: usize) -> bool {
        if self.peek() != Some(b']') {
            return false;
        }
        let mut offset = 1;
        for _ in 0..level {
            if self.peek_at(offset) != Some(b'=') {
                return false;
            }
            offset += 1;
        }
        self.peek_at(offset) == Some(b']')
    }
}

fn is_ident_start(ch: u8) -> bool {
    ch.is_ascii_alphabetic() || ch == b'_'
}

fn is_ident_continue(ch: u8) -> bool {
    ch.is_ascii_alphanumeric() || ch == b'_'
}

/// Encode a Unicode code point as UTF-8 bytes (Lua 5.4 extended: up to 0x7FFFFFFF).
/// Standard UTF-8 goes up to 4 bytes (U+10FFFF), but Lua extends the encoding
/// to 6 bytes for values up to 0x7FFFFFFF.
fn encode_utf8_lua(code: u32, buf: &mut Vec<u8>) {
    if code <= 0x7F {
        buf.push(code as u8);
    } else if code <= 0x7FF {
        buf.push(0xC0 | (code >> 6) as u8);
        buf.push(0x80 | (code & 0x3F) as u8);
    } else if code <= 0xFFFF {
        buf.push(0xE0 | (code >> 12) as u8);
        buf.push(0x80 | ((code >> 6) & 0x3F) as u8);
        buf.push(0x80 | (code & 0x3F) as u8);
    } else if code <= 0x1FFFFF {
        buf.push(0xF0 | (code >> 18) as u8);
        buf.push(0x80 | ((code >> 12) & 0x3F) as u8);
        buf.push(0x80 | ((code >> 6) & 0x3F) as u8);
        buf.push(0x80 | (code & 0x3F) as u8);
    } else if code <= 0x3FFFFFF {
        buf.push(0xF8 | (code >> 24) as u8);
        buf.push(0x80 | ((code >> 18) & 0x3F) as u8);
        buf.push(0x80 | ((code >> 12) & 0x3F) as u8);
        buf.push(0x80 | ((code >> 6) & 0x3F) as u8);
        buf.push(0x80 | (code & 0x3F) as u8);
    } else {
        buf.push(0xFC | (code >> 30) as u8);
        buf.push(0x80 | ((code >> 24) & 0x3F) as u8);
        buf.push(0x80 | ((code >> 18) & 0x3F) as u8);
        buf.push(0x80 | ((code >> 12) & 0x3F) as u8);
        buf.push(0x80 | ((code >> 6) & 0x3F) as u8);
        buf.push(0x80 | (code & 0x3F) as u8);
    }
}

fn hex_value(ch: u8) -> u8 {
    match ch {
        b'0'..=b'9' => ch - b'0',
        b'a'..=b'f' => ch - b'a' + 10,
        b'A'..=b'F' => ch - b'A' + 10,
        _ => unreachable!(),
    }
}

/// Parse a hex float literal like "0x1.0p10".
fn parse_hex_float(text: &str) -> Option<f64> {
    // Use C-style hex float parsing
    let text = if text.starts_with("0x") || text.starts_with("0X") {
        &text[2..]
    } else {
        return None;
    };

    let (mantissa_str, exp_str) = if let Some(p) = text.find(['p', 'P']) {
        (&text[..p], Some(&text[p + 1..]))
    } else {
        (text, None)
    };

    let (int_part, frac_part) = if let Some(dot) = mantissa_str.find('.') {
        (&mantissa_str[..dot], Some(&mantissa_str[dot + 1..]))
    } else {
        (mantissa_str, None)
    };

    // Build mantissa value
    let mut mantissa: f64 = 0.0;
    for ch in int_part.bytes() {
        mantissa = mantissa * 16.0 + hex_value(ch) as f64;
    }
    if let Some(frac) = frac_part {
        let mut place = 1.0 / 16.0;
        for ch in frac.bytes() {
            mantissa += hex_value(ch) as f64 * place;
            place /= 16.0;
        }
    }

    let exponent: i32 = match exp_str {
        Some(s) => s.parse().ok()?,
        None => 0,
    };

    Some(mantissa * (2.0f64).powi(exponent))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex_tokens(source: &str) -> Vec<Token> {
        let mut lexer = Lexer::new(source.as_bytes());
        let mut tokens = Vec::new();
        loop {
            let tok = lexer.advance().unwrap();
            if tok.token == Token::Eof {
                break;
            }
            tokens.push(tok.token);
        }
        tokens
    }

    fn lex_single(source: &str) -> Token {
        let mut lexer = Lexer::new(source.as_bytes());
        lexer.advance().unwrap().token
    }

    fn lex_string(source: &str) -> Vec<u8> {
        let mut lexer = Lexer::new(source.as_bytes());
        let tok = lexer.advance().unwrap();
        match tok.token {
            Token::String(id) => lexer.strings.get_bytes(id).to_vec(),
            _ => panic!("expected string, got {:?}", tok.token),
        }
    }

    fn lex_error(source: &str) -> LexError {
        let mut lexer = Lexer::new(source.as_bytes());
        loop {
            match lexer.advance() {
                Err(e) => return e,
                Ok(tok) if tok.token == Token::Eof => {
                    panic!("expected error, got EOF")
                }
                _ => {}
            }
        }
    }

    // --- Keyword tests ---

    #[test]
    fn test_all_keywords() {
        let keywords = [
            ("and", Token::And),
            ("break", Token::Break),
            ("do", Token::Do),
            ("else", Token::Else),
            ("elseif", Token::ElseIf),
            ("end", Token::End),
            ("false", Token::False),
            ("for", Token::For),
            ("function", Token::Function),
            ("goto", Token::Goto),
            ("if", Token::If),
            ("in", Token::In),
            ("local", Token::Local),
            ("nil", Token::Nil),
            ("not", Token::Not),
            ("or", Token::Or),
            ("repeat", Token::Repeat),
            ("return", Token::Return),
            ("then", Token::Then),
            ("true", Token::True),
            ("until", Token::Until),
            ("while", Token::While),
        ];
        for (src, expected) in &keywords {
            assert_eq!(lex_single(src), *expected, "keyword: {src}");
        }
    }

    #[test]
    fn test_keyword_case_sensitive() {
        // Lua keywords are case-sensitive
        let tok = lex_single("And");
        assert!(matches!(tok, Token::Name(_)));

        let tok = lex_single("IF");
        assert!(matches!(tok, Token::Name(_)));
    }

    #[test]
    fn test_keyword_as_prefix() {
        let mut lexer = Lexer::new(b"dodo");
        let tok = lexer.advance().unwrap();
        // "dodo" is a name, not two "do" keywords
        assert!(matches!(tok.token, Token::Name(_)));
    }

    // --- Number tests ---

    #[test]
    fn test_decimal_integers() {
        assert_eq!(lex_single("0"), Token::Integer(0));
        assert_eq!(lex_single("42"), Token::Integer(42));
        assert_eq!(lex_single("123456789"), Token::Integer(123456789));
    }

    #[test]
    fn test_hex_integers() {
        assert_eq!(lex_single("0xff"), Token::Integer(255));
        assert_eq!(lex_single("0xFF"), Token::Integer(255));
        assert_eq!(lex_single("0x0"), Token::Integer(0));
        assert_eq!(lex_single("0xDEAD"), Token::Integer(0xDEAD));
    }

    #[test]
    fn test_decimal_floats() {
        assert_eq!(lex_single("1.5"), Token::Float(1.5));
        assert_eq!(lex_single("0.5"), Token::Float(0.5));
        assert_eq!(lex_single(".5"), Token::Float(0.5));
        assert_eq!(lex_single("3."), Token::Float(3.0));
    }

    #[test]
    fn test_float_with_exponent() {
        assert_eq!(lex_single("1e10"), Token::Float(1e10));
        assert_eq!(lex_single("1E10"), Token::Float(1e10));
        assert_eq!(lex_single("1e+10"), Token::Float(1e10));
        assert_eq!(lex_single("1e-3"), Token::Float(1e-3));
        assert_eq!(lex_single("3.14e2"), Token::Float(314.0));
    }

    #[test]
    fn test_hex_floats() {
        assert_eq!(lex_single("0x1p0"), Token::Float(1.0));
        assert_eq!(lex_single("0x1p10"), Token::Float(1024.0));
        assert_eq!(lex_single("0x1.0p0"), Token::Float(1.0));
        assert_eq!(lex_single("0xA.0p4"), Token::Float(160.0));
    }

    // --- String tests ---

    #[test]
    fn test_simple_strings() {
        assert_eq!(lex_string(r#""hello""#), b"hello");
        assert_eq!(lex_string("'hello'"), b"hello");
        assert_eq!(lex_string(r#""""#), b"");
    }

    #[test]
    fn test_escape_a() {
        assert_eq!(lex_string(r#""\a""#), &[0x07]);
    }

    #[test]
    fn test_escape_b() {
        assert_eq!(lex_string(r#""\b""#), &[0x08]);
    }

    #[test]
    fn test_escape_f() {
        assert_eq!(lex_string(r#""\f""#), &[0x0C]);
    }

    #[test]
    fn test_escape_n() {
        assert_eq!(lex_string(r#""\n""#), b"\n");
    }

    #[test]
    fn test_escape_r() {
        assert_eq!(lex_string(r#""\r""#), b"\r");
    }

    #[test]
    fn test_escape_t() {
        assert_eq!(lex_string(r#""\t""#), b"\t");
    }

    #[test]
    fn test_escape_v() {
        assert_eq!(lex_string(r#""\v""#), &[0x0B]);
    }

    #[test]
    fn test_escape_backslash() {
        assert_eq!(lex_string(r#""\\""#), b"\\");
    }

    #[test]
    fn test_escape_quotes() {
        assert_eq!(lex_string(r#""\"""#), b"\"");
        assert_eq!(lex_string(r"'\''"), b"'");
    }

    #[test]
    fn test_escape_hex() {
        assert_eq!(lex_string(r#""\x41""#), b"A");
        assert_eq!(lex_string(r#""\x00""#), &[0x00]);
        assert_eq!(lex_string(r#""\xff""#), &[0xFF]);
    }

    #[test]
    fn test_escape_decimal() {
        assert_eq!(lex_string(r#""\65""#), b"A");
        assert_eq!(lex_string(r#""\0""#), &[0x00]);
        assert_eq!(lex_string(r#""\255""#), &[0xFF]);
    }

    #[test]
    fn test_escape_unicode() {
        assert_eq!(lex_string(r#""\u{41}""#), b"A");
        assert_eq!(lex_string(r#""\u{0041}""#), b"A");
        // Multi-byte UTF-8
        assert_eq!(lex_string(r#""\u{4e16}""#), "世".as_bytes());
    }

    #[test]
    fn test_escape_z() {
        assert_eq!(lex_string("\"hello\\z   world\""), b"helloworld");
        assert_eq!(lex_string("\"hello\\z\n   world\""), b"helloworld");
    }

    #[test]
    fn test_escape_newline() {
        assert_eq!(lex_string("\"hello\\\nworld\""), b"hello\nworld");
    }

    // --- Long string tests ---

    #[test]
    fn test_long_string_level0() {
        assert_eq!(lex_string("[[hello]]"), b"hello");
    }

    #[test]
    fn test_long_string_level1() {
        assert_eq!(lex_string("[=[hello]=]"), b"hello");
    }

    #[test]
    fn test_long_string_level2() {
        assert_eq!(lex_string("[==[hello]==]"), b"hello");
    }

    #[test]
    fn test_long_string_strips_first_newline() {
        assert_eq!(lex_string("[[\nhello]]"), b"hello");
        assert_eq!(lex_string("[[\r\nhello]]"), b"hello");
    }

    #[test]
    fn test_long_string_with_brackets() {
        assert_eq!(lex_string("[=[hello]world]=]"), b"hello]world");
    }

    #[test]
    fn test_long_string_no_escapes() {
        assert_eq!(lex_string(r"[[hello\nworld]]"), b"hello\\nworld");
    }

    // --- Operator tests ---

    #[test]
    fn test_all_single_operators() {
        let ops = [
            ("+", Token::Plus),
            ("-", Token::Minus),
            ("*", Token::Star),
            ("/", Token::Slash),
            ("%", Token::Percent),
            ("^", Token::Caret),
            ("#", Token::Hash),
            ("&", Token::Ampersand),
            ("~", Token::Tilde),
            ("|", Token::Pipe),
            ("<", Token::Less),
            (">", Token::Greater),
            ("=", Token::Assign),
            ("(", Token::LParen),
            (")", Token::RParen),
            ("{", Token::LBrace),
            ("}", Token::RBrace),
            ("[", Token::LBracket),
            ("]", Token::RBracket),
            (";", Token::Semi),
            (":", Token::Colon),
            (",", Token::Comma),
        ];
        for (src, expected) in &ops {
            assert_eq!(lex_single(src), *expected, "operator: {src}");
        }
    }

    #[test]
    fn test_multi_char_operators() {
        assert_eq!(lex_single("<<"), Token::ShiftLeft);
        assert_eq!(lex_single(">>"), Token::ShiftRight);
        assert_eq!(lex_single("//"), Token::FloorDiv);
        assert_eq!(lex_single("=="), Token::Equal);
        assert_eq!(lex_single("~="), Token::NotEqual);
        assert_eq!(lex_single("<="), Token::LessEq);
        assert_eq!(lex_single(">="), Token::GreaterEq);
        assert_eq!(lex_single("::"), Token::DoubleColon);
    }

    #[test]
    fn test_dot_disambiguation() {
        assert_eq!(lex_single("."), Token::Dot);
        assert_eq!(lex_single(".."), Token::DotDot);
        assert_eq!(lex_single("..."), Token::DotDotDot);
    }

    #[test]
    fn test_slash_disambiguation() {
        let tokens = lex_tokens("/ //");
        assert_eq!(tokens, vec![Token::Slash, Token::FloorDiv]);
    }

    // --- Comment tests ---

    #[test]
    fn test_short_comment() {
        let tokens = lex_tokens("-- comment\n42");
        assert_eq!(tokens, vec![Token::Integer(42)]);
    }

    #[test]
    fn test_long_comment() {
        let tokens = lex_tokens("--[[comment]]42");
        assert_eq!(tokens, vec![Token::Integer(42)]);
    }

    #[test]
    fn test_long_comment_level1() {
        let tokens = lex_tokens("--[=[comment]=]42");
        assert_eq!(tokens, vec![Token::Integer(42)]);
    }

    // --- Line tracking ---

    #[test]
    fn test_line_tracking() {
        let mut lexer = Lexer::new(b"a\nb\nc");
        let a = lexer.advance().unwrap();
        assert_eq!(a.span.line, 1);
        let b = lexer.advance().unwrap();
        assert_eq!(b.span.line, 2);
        let c = lexer.advance().unwrap();
        assert_eq!(c.span.line, 3);
    }

    #[test]
    fn test_line_tracking_cr() {
        let mut lexer = Lexer::new(b"a\rb");
        let a = lexer.advance().unwrap();
        assert_eq!(a.span.line, 1);
        let b = lexer.advance().unwrap();
        assert_eq!(b.span.line, 2);
    }

    #[test]
    fn test_line_tracking_crlf() {
        let mut lexer = Lexer::new(b"a\r\nb");
        let a = lexer.advance().unwrap();
        assert_eq!(a.span.line, 1);
        let b = lexer.advance().unwrap();
        assert_eq!(b.span.line, 2);
    }

    // --- Error tests ---

    #[test]
    fn test_error_unterminated_string() {
        let err = lex_error("\"hello");
        assert!(err.message.contains("unfinished string"));
    }

    #[test]
    fn test_error_unterminated_long_string() {
        let err = lex_error("[[hello");
        assert!(err.message.contains("unfinished long string"));
    }

    #[test]
    fn test_error_invalid_escape() {
        let err = lex_error(r#""\q""#);
        assert!(err.message.contains("invalid escape"));
    }

    #[test]
    fn test_error_malformed_number() {
        let err = lex_error("1e");
        assert!(err.message.contains("malformed number"));
    }

    #[test]
    fn test_error_decimal_escape_too_large() {
        let err = lex_error(r#""\256""#);
        assert!(err.message.contains("decimal escape too large"));
    }

    #[test]
    fn test_error_hex_no_digits() {
        let err = lex_error("0xZ");
        assert!(err.message.contains("no hex digits"));
    }

    // --- Full program tokenization ---

    #[test]
    fn test_full_program() {
        let src = r#"
local x = 42
if x > 0 then
    print("hello")
end
"#;
        let tokens = lex_tokens(src);
        assert_eq!(
            tokens,
            vec![
                Token::Local,
                Token::Name(selune_core::string::StringId(0)),
                Token::Assign,
                Token::Integer(42),
                Token::If,
                Token::Name(selune_core::string::StringId(0)),
                Token::Greater,
                Token::Integer(0),
                Token::Then,
                Token::Name(selune_core::string::StringId(1)),
                Token::LParen,
                Token::String(selune_core::string::StringId(2)),
                Token::RParen,
                Token::End,
            ]
        );
    }

    #[test]
    fn test_multiline_string_across_lines() {
        let src = "\"hello\\\nworld\"";
        assert_eq!(lex_string(src), b"hello\nworld");
    }

    #[test]
    fn test_name_interning() {
        let mut lexer = Lexer::new(b"foo bar foo");
        let t1 = lexer.advance().unwrap();
        let _t2 = lexer.advance().unwrap();
        let t3 = lexer.advance().unwrap();
        // Same name "foo" should get the same StringId
        assert_eq!(t1.token, t3.token);
    }

    #[test]
    fn test_eof() {
        let mut lexer = Lexer::new(b"");
        let tok = lexer.advance().unwrap();
        assert_eq!(tok.token, Token::Eof);
    }

    #[test]
    fn test_eof_repeated() {
        let mut lexer = Lexer::new(b"42");
        lexer.advance().unwrap(); // 42
        let t1 = lexer.advance().unwrap();
        assert_eq!(t1.token, Token::Eof);
        let t2 = lexer.advance().unwrap();
        assert_eq!(t2.token, Token::Eof);
    }

    #[test]
    fn test_negative_number_is_two_tokens() {
        let tokens = lex_tokens("-42");
        assert_eq!(tokens, vec![Token::Minus, Token::Integer(42)]);
    }

    #[test]
    fn test_adjacent_operators() {
        let tokens = lex_tokens("<=>=~===");
        assert_eq!(
            tokens,
            vec![
                Token::LessEq,
                Token::GreaterEq,
                Token::NotEqual,
                Token::Equal
            ]
        );
    }

    #[test]
    fn test_number_before_dot() {
        let tokens = lex_tokens("3..4");
        assert_eq!(
            tokens,
            vec![Token::Integer(3), Token::DotDot, Token::Integer(4)]
        );
    }
}
