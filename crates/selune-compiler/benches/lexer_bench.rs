use criterion::{black_box, criterion_group, criterion_main, Criterion};
use selune_compiler::lexer::Lexer;
use selune_compiler::token::Token;

fn lex_all(source: &[u8]) {
    let mut lexer = Lexer::new(source);
    loop {
        match lexer.advance() {
            Ok(tok) if tok.token == Token::Eof => break,
            Ok(_) => {}
            Err(_) => break,
        }
    }
}

fn bench_lex_simple(c: &mut Criterion) {
    let src = b"local x = 42\nreturn x + 1";
    c.bench_function("lex_simple", |b| {
        b.iter(|| lex_all(black_box(src)));
    });
}

fn bench_lex_fibonacci(c: &mut Criterion) {
    let src = br#"
local function fib(n)
    if n <= 1 then
        return n
    end
    return fib(n - 1) + fib(n - 2)
end
return fib(10)
"#;
    c.bench_function("lex_fibonacci", |b| {
        b.iter(|| lex_all(black_box(src)));
    });
}

fn bench_lex_large(c: &mut Criterion) {
    // Generate a large input with many statements
    let mut src = String::new();
    for i in 0..1000 {
        src.push_str(&format!("local x{i} = {i}\n"));
    }
    src.push_str("return x0\n");
    let bytes = src.as_bytes().to_vec();
    c.bench_function("lex_1000_locals", |b| {
        b.iter(|| lex_all(black_box(&bytes)));
    });
}

criterion_group!(
    benches,
    bench_lex_simple,
    bench_lex_fibonacci,
    bench_lex_large
);
criterion_main!(benches);
