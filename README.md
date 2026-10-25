# Formalizing Equihash

Zcash's proof of work is Equihash. This repository is a Lean 4 proof, release by release, that
the Equihash verifiers Zcash software runs accept exactly the solutions the Zcash protocol
specification (§7.7.1) calls valid, with distinct indices. Each theorem states its hypotheses;
for `zakura-equihash` 4.0.0, a 140-byte header and nonce. Beyond them, the Lean runs the
portable leaf-hashing kernel, so it assumes the AVX2/NEON kernels compute the same.

| Crate             | Version | Status  |
|-------------------|---------|---------|
| `zakura-equihash` | 4.0.0   | Proven  |
| `equihash`        | 0.3.0   | Planned |
| `equihash`        | 0.3.1   | Planned |

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
[`rust/zakura-equihash-4.0.0/COPYRIGHT`](rust/zakura-equihash-4.0.0/COPYRIGHT).

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion
in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above,
without any additional terms or conditions.
