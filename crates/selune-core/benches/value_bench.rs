use criterion::{black_box, criterion_group, criterion_main, Criterion};
use selune_core::value::TValue;

fn bench_create_integer(c: &mut Criterion) {
    c.bench_function("tvalue_create_integer", |b| {
        b.iter(|| TValue::from_integer(black_box(42)));
    });
}

fn bench_create_float(c: &mut Criterion) {
    c.bench_function("tvalue_create_float", |b| {
        b.iter(|| TValue::from_float(black_box(1.5)));
    });
}

fn bench_create_bool(c: &mut Criterion) {
    c.bench_function("tvalue_create_bool", |b| {
        b.iter(|| TValue::from_bool(black_box(true)));
    });
}

fn bench_extract_integer(c: &mut Criterion) {
    let val = TValue::from_integer(42);
    c.bench_function("tvalue_extract_integer", |b| {
        b.iter(|| black_box(val).as_integer());
    });
}

fn bench_extract_float(c: &mut Criterion) {
    let val = TValue::from_float(1.5);
    c.bench_function("tvalue_extract_float", |b| {
        b.iter(|| black_box(val).as_float());
    });
}

fn bench_is_falsy(c: &mut Criterion) {
    let nil = TValue::nil();
    let truthy = TValue::from_integer(1);
    c.bench_function("tvalue_is_falsy_nil", |b| {
        b.iter(|| black_box(nil).is_falsy());
    });
    c.bench_function("tvalue_is_falsy_int", |b| {
        b.iter(|| black_box(truthy).is_falsy());
    });
}

fn bench_roundtrip(c: &mut Criterion) {
    c.bench_function("tvalue_roundtrip_integer", |b| {
        b.iter(|| {
            let v = TValue::from_integer(black_box(12345));
            v.as_integer()
        });
    });
}

criterion_group!(
    benches,
    bench_create_integer,
    bench_create_float,
    bench_create_bool,
    bench_extract_integer,
    bench_extract_float,
    bench_is_falsy,
    bench_roundtrip
);
criterion_main!(benches);
