use std::hint::black_box;
use criterion::{criterion_group, criterion_main, Criterion};

fn popcnt_simple(n: u64) -> u64 {
    let mut count = 0;
    for ii in 0..64 {
        count += (n >> ii) & 1;
    }
    count
}

fn popcnt_intrinsic(n: u64) -> u32 {
    n.count_ones()
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("popcnt simple", |b| b.iter(|| popcnt_simple(black_box(200))));
    c.bench_function("popcnt intrinsic", |b| b.iter(|| popcnt_intrinsic(black_box(200))));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
