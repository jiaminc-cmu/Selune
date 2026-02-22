use criterion::{black_box, criterion_group, criterion_main, Criterion};
use selune_compiler::compiler::compile;

fn bench_compile_simple(c: &mut Criterion) {
    let src = b"local x = 42\nreturn x + 1";
    c.bench_function("compile_simple", |b| {
        b.iter(|| compile(black_box(src), "bench").unwrap());
    });
}

fn bench_compile_fibonacci(c: &mut Criterion) {
    let src = br#"
local function fib(n)
    if n <= 1 then
        return n
    end
    return fib(n - 1) + fib(n - 2)
end
return fib(10)
"#;
    c.bench_function("compile_fibonacci", |b| {
        b.iter(|| compile(black_box(src), "bench").unwrap());
    });
}

fn bench_compile_sieve(c: &mut Criterion) {
    let src = br#"
local function sieve(n)
    local is_prime = {}
    for i = 2, n do
        is_prime[i] = true
    end
    for i = 2, n do
        if is_prime[i] then
            for j = i * i, n, i do
                is_prime[j] = false
            end
        end
    end
    local count = 0
    for i = 2, n do
        if is_prime[i] then
            count = count + 1
        end
    end
    return count
end
return sieve(100)
"#;
    c.bench_function("compile_sieve", |b| {
        b.iter(|| compile(black_box(src), "bench").unwrap());
    });
}

fn bench_compile_many_locals(c: &mut Criterion) {
    let mut src = String::new();
    for i in 0..200 {
        src.push_str(&format!("local x{i} = {i}\n"));
    }
    src.push_str("return x0\n");
    let bytes = src.as_bytes().to_vec();
    c.bench_function("compile_200_locals", |b| {
        b.iter(|| compile(black_box(&bytes), "bench").unwrap());
    });
}

criterion_group!(
    benches,
    bench_compile_simple,
    bench_compile_fibonacci,
    bench_compile_sieve,
    bench_compile_many_locals
);
criterion_main!(benches);
