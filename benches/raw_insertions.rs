use criterion::{criterion_group, criterion_main, Criterion};
use rand::Rng;
use std::hint::black_box;
use stwo_prover::core::fields::m31::M31;
use vex_prover::imt::order::Order;
use vex_prover::imt::IndexedMerkleTree;

fn insert_batch(n: u32) {
    let mut imt = IndexedMerkleTree::new();
    let mut rng = rand::thread_rng();
    let orders = (0..n)
        .map(|i| Order::new(M31(i), M31(rng.gen_range(21352332..33333333)), M31(i + 2)))
        .collect::<Vec<_>>();
    for order in orders {
        imt.insert(order);
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("insert 2^16", |b| {
        b.iter(|| insert_batch(black_box(1 << 13)))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
