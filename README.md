# Formalizing Equihash

Zcash's proof of work is Equihash. This repository is a Lean 4 proof that the Equihash
verifiers Zcash nodes use accept exactly the solutions the Zcash protocol specification
(§7.7.1) calls valid. It is equally important to state clearly what is and is not
formally verified.

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

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion
in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above,
without any additional terms or conditions.
