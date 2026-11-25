# Formalizing Equihash

Zcash's proof of work is Equihash. This repository is a Lean 4 proof, release by release, that
the Equihash verifiers Zcash software runs accept exactly the solutions the Zcash protocol
specification (§7.7.1) calls valid. Each theorem states its hypotheses:

- `zakura-equihash` 5.4.0, and every release from 4.0.0 to 5.4.0, whose source is the same: for
  a 140-byte header and nonce, under each of its leaf-hashing kernels. The portable, AVX2 and
  NEON kernels are transcribed, the last two on models of the CPU instructions they use, written
  from Intel's and Arm's documentation; the Lean assumes those models, and that the kernel the
  CPU detection picks is one the CPU supports. Of the parameters it accepts, `(480, 59)` and
  `(488, 60)` have solutions of `2^62` bits or more: decoding one wraps a `usize` and panics,
  which a theorem states.
- `equihash` 0.3.0: for an input under `2^64` bytes, as two Rust slices are, and the parameters
  `zakura-equihash` accepts whose solutions are under `2^62` bits long, which include Zcash's.
  It hashes with `blake2b_simd` 1.0.4, whose portable and AVX2 implementations are transcribed,
  the AVX2 one on models of its instructions as for Zakura, and proven to compute BLAKE2b.
  Outside those parameters its length check wraps where it should overflow, which theorems
  state for `(448, 63)` and `(520, 64)`: it accepts a solution of the wrong length, and then
  panics. For `(480, 59)` and `(488, 60)` its length check is exact, and its decoding is
  Zakura's, which panics on them (theorems state both).
- `equihash` 0.3.1: for an input under `2^64` bytes, and the parameters `zakura-equihash` accepts
  whose solutions are under `2^62` bits long, which include Zcash's. Its length check and
  decoding are Zakura's: parameters whose solutions reach `2^64` bits are an error, which
  theorems state for `(448, 63)` and `(520, 64)`, and `(480, 59)` and `(488, 60)` panic as in
  Zakura. On a 140-byte header and nonce it hashes with Zakura's kernels, under the same
  assumptions; its `unsafe-verifier` feature, off by default, enables the AVX2/NEON ones. On any
  other length it hashes with `blake2b_simd`, as 0.3.0 does.

BLAKE2b is the specification's (§5.4.1.2), written from the BLAKE2 paper (ANWW2013) with RFC
7693 where the paper is silent, in `Equihash/Spec/Blake2b.lean`.

| Crate             | Version | Status  | Assumes                                            |
|-------------------|---------|---------|----------------------------------------------------|
| `zakura-equihash` | 5.4.0   | Proven  | The instruction models match Intel's and Arm's docs |
| `equihash`        | 0.3.0   | Proven  | The instruction models match Intel's docs           |
| `equihash`        | 0.3.1   | Proven  | The instruction models match Intel's and Arm's docs |

The Lean distinguishes a Rust panic from an error. Its model of a panic covers the code's own
checks, indexing and arithmetic in a release build; not running out of memory, overflowing the
stack, or undefined behaviour in the kernels' and `blake2b_simd`'s `unsafe` code. In
`blake2b_simd` it covers the checks of the digest and personalization lengths, which panic
exactly on lengths outside `1..=64` and over 16 bytes; its buffer slicing stays in bounds while
the buffer holds at most 128 bytes, which the proofs show, and the transcription takes as given.

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
[`rust/zakura-equihash-5.4.0/COPYRIGHT`](rust/zakura-equihash-5.4.0/COPYRIGHT). It also
transcribes `equihash` 0.3.0 and 0.3.1, by Jack Grigg, under MIT OR Apache-2.0; their packages
carry no license file, and the `LICENSE-MIT` of zcash/librustzcash at the `equihash-0.3.0` tag
and at commit `0ef23a95` reads Copyright (c) 2017-2021 The Electric Coin Company.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion
in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above,
without any additional terms or conditions.
