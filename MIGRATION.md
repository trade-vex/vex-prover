# Migration Guide: Upgrading to NitrooZK-stwo with CUDA Support

This document describes the changes made to upgrade vex-prover from the standard [stwo](https://github.com/starkware-libs/stwo) library to the CUDA-accelerated [NitrooZK-stwo](https://github.com/AntChainOpenLabs/NitrooZK-stwo) fork.

## Overview

The upgrade adds GPU acceleration support via CUDA while maintaining full backwards compatibility with the existing SIMD backend. The API remains largely unchanged, with new functions added for CUDA backend support.

## What Changed

### 1. Dependencies (`Cargo.toml`)

**Before:**
```toml
[dependencies]
stwo-prover = { git = "https://github.com/starkware-libs/stwo", rev = "a194fad", features = ["parallel"] }
stwo-air-utils = { git = "https://github.com/starkware-libs/stwo", rev = "a194fad" }
```

**After:**
```toml
[dependencies]
stwo-prover = { git = "https://github.com/AntChainOpenLabs/NitrooZK-stwo", rev = "6590e8b", features = ["parallel"] }
stwo-air-utils = { git = "https://github.com/AntChainOpenLabs/NitrooZK-stwo", rev = "6590e8b" }
```

### 2. Prover Implementation (`src/prover.rs`)

#### New Generic Backend Support

A new generic `prove_vex_with_backend<B: Backend>()` function was added that accepts any backend implementation:

```rust
fn prove_vex_with_backend<B: Backend + PolyOps>(
    trace: ExecutionTrace<BaseField>,
) -> Result<VexProof<Blake2sMerkleHasher>, VexProvingError>
```

#### Updated Public API

The existing `prove_vex()` function now wraps the generic implementation:

```rust
// SIMD backend (default, unchanged API)
pub fn prove_vex(
    trace: ExecutionTrace<BaseField>,
) -> Result<VexProof<Blake2sMerkleHasher>, VexProvingError> {
    prove_vex_with_backend::<SimdBackend>(trace)
}
```

A new function for CUDA acceleration:

```rust
// CUDA backend (new)
#[cfg(not(target_arch = "wasm32"))]
pub fn prove_vex_cuda(
    trace: ExecutionTrace<BaseField>,
) -> Result<VexProof<Blake2sMerkleHasher>, VexProvingError> {
    prove_vex_with_backend::<CudaBackend>(trace)
}
```

### 3. Testing

Added new CUDA-specific test:

```rust
#[test_log::test]
#[cfg(not(target_arch = "wasm32"))]
fn test_prove_cuda() {
    // Same test logic as test_prove() but uses prove_vex_cuda()
}
```

## Breaking Changes

**None.** The upgrade is fully backwards compatible. Existing code using `prove_vex()` will continue to work without modification.

## New Features

### 1. CUDA Backend Support

```rust
use vex_prover::prover::prove_vex_cuda;

let proof = prove_vex_cuda(execution_trace)?;
```

### 2. Backend Flexibility

The generic implementation allows for future backend additions (e.g., Metal, Vulkan, etc.) without API changes.

## Performance Comparison

Based on NitrooZK-stwo benchmarks, expected performance improvements with CUDA:

| Trace Size | SIMD Time | CUDA Time | Speedup |
|-----------|-----------|-----------|---------|
| 2^16 | 199ms | 222ms | 0.9x |
| 2^17 | 267ms | 34ms | 7.8x |
| 2^18 | 450ms | 47ms | 9.6x |
| 2^19 | 757ms | 57ms | 13.3x |
| 2^20 | 1390ms | 87ms | 16.0x |
| 2^21 | 2670ms | 139ms | 19.2x |
| 2^22 | 5166ms | 254ms | 20.3x |
| 2^23 | 11014ms | 488ms | 22.6x |

*Note: Performance varies based on hardware configuration*

## Migration Checklist

- [x] Update dependencies in `Cargo.toml`
- [x] Add generic backend support to prover
- [x] Maintain backwards compatibility with SIMD backend
- [x] Add CUDA backend function
- [x] Add CUDA backend test
- [x] Update README with usage instructions
- [x] Create migration guide

## Requirements for CUDA Backend

### Hardware
- NVIDIA GPU with compute capability 7.0 or higher
- Recommended: RTX 3000 series or newer, A100, H100

### Software
- CUDA Toolkit 13.0 or later
- Appropriate NVIDIA drivers

### Installation

1. Install CUDA Toolkit: https://developer.nvidia.com/cuda-downloads
2. Verify installation: `nvcc --version`
3. Build with CUDA support: `cargo build --release`

## Implementation Details

### Trace Generation Strategy

The current implementation generates traces on the CPU (SIMD backend) and transfers them to the appropriate backend for proving. This approach:

1. **Maintains compatibility**: All existing trace generation code works without modification
2. **Simplifies migration**: No need to rewrite trace generation for CUDA
3. **Efficient**: Transfer overhead is negligible compared to proving time

Future optimizations could include:
- Native CUDA trace generation for maximum performance
- Streaming trace generation to GPU

### Backend Selection

The backend is selected at compile time based on the function called:
- `prove_vex()` → `SimdBackend`
- `prove_vex_cuda()` → `CudaBackend`

Both produce identical, verifiable proofs using the same `verify_vex()` function.

## Troubleshooting

### CUDA Backend Not Available

**Error:** CUDA backend compilation fails

**Solution:**
1. Verify CUDA Toolkit installation
2. Check NVIDIA driver version
3. Ensure GPU compute capability ≥ 7.0

### Performance Not Improving

**Issue:** CUDA backend not significantly faster

**Possible causes:**
1. Trace size too small (CUDA has overhead for small traces)
2. GPU memory insufficient
3. CPU-GPU transfer bottleneck

**Recommendations:**
- Use CUDA backend for traces ≥ 2^18
- Monitor GPU utilization
- Ensure adequate VRAM

## Future Work

Potential enhancements:

1. **Native CUDA Trace Generation**: Generate traces directly on GPU
2. **Batch Proving**: Prove multiple traces in parallel on GPU
3. **Mixed Backends**: Use SIMD for small traces, CUDA for large traces
4. **Additional Backends**: Metal (macOS), Vulkan (cross-platform)
5. **Dynamic Backend Selection**: Automatically choose backend based on trace size

## Support

For issues related to:
- **VEX Prover**: Open an issue in this repository
- **NitrooZK-stwo**: Visit https://github.com/AntChainOpenLabs/NitrooZK-stwo
- **CUDA Setup**: Refer to NVIDIA documentation

## Acknowledgments

Special thanks to:
- [AntChain OpenLabs](https://github.com/AntChainOpenLabs) for NitrooZK-stwo
- [StarkWare](https://github.com/starkware-libs) for the original stwo library
- [Nethermind](https://github.com/NethermindEth/stwo-gpu) for inspiring GPU acceleration work
