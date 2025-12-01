use criterion::*;
use std::time::Duration;

use bitperm::*;

criterion_group! {
    name = benches;
    config = Criterion::default().sample_size(100).measurement_time(Duration::from_secs(2)).warm_up_time(Duration::from_secs(1));
    targets = bitgrid8
}
criterion_main!(benches);

pub fn bitgrid8(c: &mut Criterion) {
    // Global set up here

    c.bench_function("origin_dihedral_all", |b| {
        let piece = BitGrid8::from(0x13);

        b.iter(|| {
            BitGrid8::origin_dihedral_all(piece);
        })
    });

    c.bench_function("origin_dihedral_all_vec", |b| {
        let piece = BitGrid8::from(0x13);

        b.iter(|| {
            BitGrid8::origin_dihedral_all_vec(piece);
        })
    });

}

