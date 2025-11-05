# Performance Optimization Guide

This document describes performance optimizations applied to vex-prover based on benchmarking insights from [rookie-numbers](https://github.com/clementwalter/rookie-numbers).

## Quick Start - Maximum Performance

For best performance, build with these flags:

```bash
RUSTFLAGS="-C target-cpu=native" cargo build --release --features jemalloc
RUSTFLAGS="-C target-cpu=native" cargo test --release --features jemalloc
```

## Optimizations Applied

### 1. Disabled stwo Internal Parallelization ✅

**What**: Removed the `parallel` feature from `stwo-prover` dependency

**Why**: The benchmarking study found that stwo's internal parallelization can create overhead and thread contention. Disabling it provides better performance for single proof generation.

**Code**: `Cargo.toml:10`
```toml
stwo-prover = { git = "...", rev = "a194fad" }  # No parallel feature
```

### 2. Optional jemalloc Allocator ✅

**What**: Added optional jemalloc allocator via `tikv-jemallocator`

**Why**: jemalloc provides better memory allocation performance than the default system allocator, especially for workloads with many allocations.

**Usage**:
```bash
# Enable jemalloc
cargo build --release --features jemalloc

# Without jemalloc (default)
cargo build --release
```

**Code**: `src/lib.rs:4-9`

### 3. Target-Specific CPU Optimizations ⚡

**What**: Use RUSTFLAGS to enable CPU-specific optimizations

**Why**: Enables SIMD instructions and other CPU-specific features for your processor

**Usage**:
```bash
RUSTFLAGS="-C target-cpu=native" cargo build --release
```

## What NOT To Do ❌

### ❌ Don't Parallelize Within a Single Proof

The benchmarking repo's advice to "split your job" refers to running **multiple separate proofs in parallel**, NOT parallelizing within a single proof.

**Correct** (if generating multiple proofs):
```rust
use rayon::prelude::*;

// Generate multiple proofs in parallel
let proofs: Vec<_> = execution_traces
    .into_par_iter()
    .map(|trace| prove_vex(trace))
    .collect();
```

**Incorrect** (causes 2x+ slowdown):
```rust
// DON'T do this - parallelizing within single proof
rayon::join(
    || bytes::trace(...),
    || poseidon::trace(...),  // This causes overhead!
)
```

**Why**: Internal trace generation has dependencies and shared state that don't parallelize well. The overhead of rayon's work-stealing scheduler outweighs any benefits.

## Performance Testing

### Run the Test Suite

```bash
# Basic performance test
RUSTFLAGS="-C target-cpu=native" cargo test --release test_prove -- --nocapture

# With jemalloc
RUSTFLAGS="-C target-cpu=native" cargo test --release --features jemalloc test_prove -- --nocapture
```

The test output shows:
- Trace sizes for each component
- Instructions proved per second
- Total proving time

### Benchmark Raw Insertions

```bash
RUSTFLAGS="-C target-cpu=native" cargo bench --bench raw_insertions
```

## Expected Performance Gains

Based on the rookie-numbers study:

| Optimization | Expected Speedup | Notes |
|--------------|------------------|-------|
| Disable stwo parallel | 1.5-2x | Main optimization |
| jemalloc allocator | 1.1-1.3x | Depends on workload |
| target-cpu=native | 1.1-1.5x | Depends on CPU features |
| **Combined** | **2-3x** | Best case scenario |

*Note: Actual results vary based on workload characteristics, CPU architecture, and system configuration.*

## System Requirements

- **Minimum**: 4 CPU cores, 8GB RAM
- **Recommended**: 8+ CPU cores, 16GB+ RAM
- **Optimal**: 16+ CPU cores, 32GB+ RAM

Large trace sizes (2^14+ operations) may require 32GB+ RAM.

## Troubleshooting

### Out of Memory (OOM) Errors

If you encounter OOM errors:

1. Reduce the trace size in your tests
2. Close other applications
3. Consider upgrading RAM

### Slower Performance After "Optimization"

If performance gets worse after changes:

1. Check that you're not parallelizing within a single proof (see "What NOT To Do" above)
2. Verify RUSTFLAGS are set: `echo $RUSTFLAGS`
3. Ensure you're building in release mode: `--release`
4. Try with jemalloc: `--features jemalloc`

## References

- [rookie-numbers benchmarking repo](https://github.com/clementwalter/rookie-numbers)
- [stwo prover](https://github.com/starkware-libs/stwo)
- [jemalloc documentation](https://github.com/jemalloc/jemalloc)

## Summary

✅ **Do**:
- Disable stwo's `parallel` feature
- Use `RUSTFLAGS="-C target-cpu=native"`
- Enable `jemalloc` feature for better allocation
- Run multiple proofs in parallel if needed

❌ **Don't**:
- Parallelize trace generation within a single proof
- Use debug builds for performance testing
- Forget to use `--release` flag

---

*Last updated: 2025-11-05*
*Branch: claude/upgrade-prover-performance-011CUpY41QPVuy9kLyrG2vjR*
