RUST_MIN_STACK=33554432 LOG_N_INSTANCES=10 RUST_LOG_SPAN_EVENTS=enter,close RUST_LOG=info     RUSTFLAGS="-C target-cpu=native -C opt-level=3" cargo test test_prove  --release -- --nocapture
