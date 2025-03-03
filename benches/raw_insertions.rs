use criterion::{criterion_group, criterion_main, Criterion};
use rand::Rng;
use std::hint::black_box;
use vex_prover::imt::order::Order;
use vex_prover::imt::SellIMT;

fn insert_batch(n: u64) {
    let mut imt = SellIMT::new();
    let mut rng = rand::thread_rng();
    let mut time = 1;
    for _ in 0..n {
        let time_inc = rng.gen_range(1..=16);
        time += time_inc;
        let order = Order::new(rng.gen(), rng.gen(), time);
        imt.insert(order).unwrap();
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("insert 2^13", |b| {
        b.iter(|| insert_batch(black_box(1 << 13)))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
