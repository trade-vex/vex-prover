![VEX](resources/img/banner.png)

# Vex Prover

**VEX** (Verifiable Exchange) is a performant off-chain trading system with on-chain verifiability. It combines the power of STARKs and a IMT's(Indexed Merkle Tree's) to deliver fast, fair, and verifiable trade execution—without relying on centralized trusted system.

This repository contains the core proving logic for Order Matching System in Vex, now with **CUDA acceleration support** via [NitrooZK-stwo](https://github.com/AntChainOpenLabs/NitrooZK-stwo).

## Key Features

- **Verifiable Order Matching**: Proof generation ensures that each trade executed off-chain can be verified on-chain.
- **High Throughput**: All constraints are reduced to hash operations, allowing fast and scalable proof generation.
- **GPU Acceleration**: Optional CUDA backend for 10-150x faster proof generation on NVIDIA GPUs.
- **Flexible Backend Support**: Choose between SIMD (CPU) or CUDA (GPU) backends based on your hardware.
- **Benchmarking Tools**: Comprehensive benchmarking harness to measure trace generation, proof generation, and verifier performance.

## Backend Support

Vex Prover now supports two backends:

### SIMD Backend (Default - CPU)
- Multi-threaded CPU computation with native SIMD instruction optimization
- No additional hardware requirements
- Suitable for development and moderate workloads

### CUDA Backend (GPU)
- NVIDIA GPU acceleration for substantially faster proof generation
- Requires:
  - NVIDIA GPU with compute capability 7.0 or higher
  - CUDA Toolkit 13.0 or later
- Performance improvements: **10-150x faster** depending on trace size
- Recommended for production deployments

## Usage

### Using SIMD Backend (Default)
```rust
use vex_prover::prover::prove_vex;

let execution_trace = /* your execution trace */;
let proof = prove_vex(execution_trace)?;
```

### Using CUDA Backend
```rust
use vex_prover::prover::prove_vex_cuda;

let execution_trace = /* your execution trace */;
let proof = prove_vex_cuda(execution_trace)?;
```

Both backends produce identical proofs that can be verified using the same `verify_vex()` function.

## Benchmarks

Before getting started, make sure you have installed rust, and shell environment('bash', 'sh')

### SIMD Backend
We've made benchmarking simple. Just run the provided shell script:

```bash
./benchmarks.sh
```

This will run the prover on a simple batch of trades for 4096 orders on both buy and sell side and output timing logs for trace and proof generation.

### CUDA Backend
To benchmark with CUDA acceleration, ensure you have CUDA Toolkit installed and run:

```bash
cargo test --release test_prove_cuda -- --nocapture
```

Expected performance improvements compared to SIMD:
- Small traces (2^16): ~10x speedup
- Medium traces (2^20): ~50x speedup
- Large traces (2^23): ~150x speedup 
