# Formalizing Equihash

Zcash's proof of work is Equihash. This repository is a Lean 4 proof, release by release, that
the Equihash verifiers Zcash software runs accept exactly the solutions the Zcash protocol
specification (§7.7.1) calls valid, with distinct indices. Each theorem states its hypotheses:

- `zakura-equihash` 4.0.0: for a 140-byte header and nonce. The Lean runs the portable
  leaf-hashing kernel, so it assumes the AVX2/NEON kernels compute the same.
- `equihash` 0.3.0: for an input of any length, and the parameters `zakura-equihash` accepts
  whose solutions are under `2^64` bits long, which include Zcash's. It hashes with the
  `blake2b_simd` crate, which it assumes computes BLAKE2b. Outside those parameters its length
  check wraps where it should overflow, which theorems state for `(448, 63)` and `(520, 64)`: it
  accepts a solution of the wrong length, and then panics.

| Crate             | Version | Status  | Assumes                                   |
|-------------------|---------|---------|-------------------------------------------|
| `zakura-equihash` | 4.0.0   | Proven  | AVX2/NEON kernels match the portable one  |
| `equihash`        | 0.3.0   | Proven  | `blake2b_simd` computes BLAKE2b           |
| `equihash`        | 0.3.1   | Planned |                                           |

The Lean distinguishes a Rust panic from an error. Its model of a panic covers the code's own
checks, indexing and arithmetic in a release build; not running out of memory, overflowing the
stack, or a panic inside `blake2b_simd` other than its checks of the digest and personalization
lengths.

## Verifying the proofs

A successful build is the verification: building re-checks every proof. Install
[elan](https://github.com/leanprover/elan), which reads `lean-toolchain` and installs the
pinned Lean version, then from the repository root:

    lake exe cache get   # one-time: download prebuilt Mathlib
    lake build --wfail   # check every proof; warnings fail, as in CI

## License

Copyright 2026 Julian Abraham (craftsoldier).

All code in this workspace is licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or
   http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

The pinned crates in `rust/` keep their own licenses, and the protocol specification excerpts
in `spec/` are under the MIT license in [`spec/COPYING.rst`](spec/COPYING.rst).

The Lean in `Equihash/Verifier/` transcribes `zakura-equihash`, Copyright (c) The Zakura
Contributors, originally Copyright (c) 2020-2022 The Zcash developers and 2017-2021 The
Electric Coin Company, under MIT OR Apache-2.0; see
[`rust/zakura-equihash-4.0.0/COPYRIGHT`](rust/zakura-equihash-4.0.0/COPYRIGHT). It also
transcribes `equihash` 0.3.0, by Jack Grigg, under MIT OR Apache-2.0; its package carries no
license file, and the `LICENSE-MIT` of zcash/librustzcash at the `equihash-0.3.0` tag reads
Copyright (c) 2017-2021 The Electric Coin Company.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion
in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above,
without any additional terms or conditions.
