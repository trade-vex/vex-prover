# Vex Prover

**VEX** (Verifiable Exchange) is a performant off-chain trading system with on-chain verifiability. It combines the power of STARKs and a IMT's(Indexed Merkle Tree's) to deliver fast, fair, and verifiable trade execution—without relying on centralized trusted system.

This repository contains the core proving logic for Order Matching System in Vex.

## Key Features

- **Verifiable Order Matching**: Proof generation ensures that each trade executed off-chain can be verified on-chain.
- **High Throughput**: All constraints are reduced to hash operations, allowing fast and scalable proof generation.
- **Benchmarking Tools**: Comprehensive benchmarking harness to measure trace generation, proof generation, and verifier performance.

## Benchmarks

Before getting started, make sure you have installed rust, and shell environment('bash', 'sh')

We've made benchmarking simple. Just run the provided shell script:

```bash
./benchmarks.sh
```

This will run the prover on a simple batch of trades for 4096 orders on both buy and sell side and output timing logs for trace and proof generation. 