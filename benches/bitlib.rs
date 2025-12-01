use criterion::*;
use std::time::Duration;

use bitperm::*;

criterion_group! {
    name = benches;
    config = Criterion::default().sample_size(100).measurement_time(Duration::from_secs(2)).warm_up_time(Duration::from_secs(1));
    targets = bitlib
}
criterion_main!(benches);

pub fn bitlib(c: &mut Criterion) {
    // Global set up here

    c.bench_function("swap_mask_shift_u32", |b| {
        let mut p = 0x01234567_u32;
    
        b.iter(|| {
            swap_mask_shift_u32(&mut p, 0xf0f0, 12);
        })
    });

    c.bench_function("swap_mask_shift_u64", |b| {
        let mut p: u64 = 0xffff_ffff_u64;
    
        b.iter(|| {
            swap_mask_shift_u64(&mut p, 0xffff_ffff_u64, 32);
        })
    });
}
