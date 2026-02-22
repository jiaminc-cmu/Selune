#![no_main]

use libfuzzer_sys::fuzz_target;
use selune_compiler::lexer::Lexer;
use selune_core::string::StringInterner;

fuzz_target!(|data: &[u8]| {
    // The lexer must never panic on any input — errors are fine, panics are bugs.
    let mut strings = StringInterner::new();
    let mut lexer = Lexer::new(data, &mut strings);
    loop {
        match lexer.advance() {
            Ok(tok) => {
                if tok.token == selune_compiler::token::Token::Eof {
                    break;
                }
            }
            Err(_) => break,
        }
    }
});
