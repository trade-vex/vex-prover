use criterion::{criterion_group, criterion_main, Criterion};
use rand::Rng;
use std::cell::RefCell;
use std::hint::black_box;
use std::rc::Rc;
use vex_prover::executor::order_book::OrderBook;
use vex_prover::executor::record::ExecutionTrace;
use vex_prover::imt::order::Order;

fn insert_batch(n: u64) {
    let record = Rc::new(RefCell::new(ExecutionTrace::new()));
    let mut order_book = OrderBook::new(Rc::clone(&record));
    let mut rng = rand::thread_rng();
    let mut time = 1;
    for _ in 0..n {
        let time_inc = rng.gen_range(1..=16);
        time += time_inc;
        let buy_order = Order::new(rng.gen_range(1..=50), rng.gen_range(51..=100), time);
        let sell_order = Order::new(rng.gen_range(101..=150), rng.gen_range(151..=200), time);
        order_book.place_buy_order(buy_order).unwrap();
        order_book.place_sell_order(sell_order).unwrap();
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("insert 2^13", |b| {
        b.iter(|| insert_batch(black_box(1 << 13)))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
