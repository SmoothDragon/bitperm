use std::hint::black_box;
use criterion::{criterion_group, criterion_main, Criterion};

fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 1,
        1 => 1,
        n => fibonacci(n-1) + fibonacci(n-2),
    }
}

fn popcnt_simple(n: u64) -> u64 {
    let mut count = 0;
    for ii in 0..64 {
        count += (n >> ii) & 1;
    }
    count
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("popcnt simple", |b| b.iter(|| popcnt_simple(black_box(20))));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
