use criterion::{criterion_group, criterion_main, Criterion};
use rand::Rng;
use std::cell::RefCell;
use std::hint::black_box;
use std::rc::Rc;
use vex_prover::executor::record::ExecutionTrace;
use vex_prover::imt::order::Order;
use vex_prover::imt::{BuyIMT, SellIMT};

fn insert_batch(n: u64) {
    let trace = Rc::new(RefCell::new(ExecutionTrace::new()));
    let mut buy_imt = BuyIMT::new(Rc::clone(&trace));
    let mut sell_imt = SellIMT::new(Rc::clone(&trace));
    let mut rng = rand::thread_rng();
    let mut time = 1;
    for _ in 0..n {
        let time_inc = rng.gen_range(1..=16);
        time += time_inc;
        let buy_order = Order::new(rng.gen(), rng.gen(), time);
        let sell_order = Order::new(rng.gen(), rng.gen(), time);
        buy_imt.insert(buy_order).unwrap();
        sell_imt.insert(sell_order).unwrap();
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("insert 2^13", |b| {
        b.iter(|| insert_batch(black_box(1 << 13)))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
