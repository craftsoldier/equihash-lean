/-
Each published crate's `is_valid_solution`, built from the shared verifier pieces.

| Crate             | Version | Verifier                    | Source                        |
|-------------------|---------|-----------------------------|-------------------------------|
| `zakura-equihash` | 4.0.0   | single-pass, 140-byte input | `rust/zakura-equihash-4.0.0/` |
| `equihash`        | 0.3.0   | recursive, any input        | `rust/equihash-0.3.0/`        |
| `equihash`        | 0.3.1   | single-pass, any input      | `rust/equihash-0.3.1/`        |

A Rust panic is `none`; a function returning a Rust `Result` is into `ExceptT Kind Option`
(`Verifier/Error.lean`).
-/
module

public import Equihash.Verifier.LeafHash
public import Equihash.Verifier.Recursive
public import Equihash.Verifier.SinglePass

@[expose] public section

namespace Equihash.Verifier

/-- `zakura-equihash 4.0.0`'s `is_valid_solution` (`src/verify.rs`, lines 269–280) for `soln`, a
    minimally encoded solution for `input ‖ nonce` with parameters `n` and `k`, on a CPU where
    `Kernel::detect()` picks `kernel` (see `LeafHasher.new?`). -/
def isValidSolution? (kernel : Kernel) (n k : ℕ) (input nonce soln : List ℕ) :
    ExceptT Kind Option Unit := do
  let some p := Params.new? n k | throw .InvalidParams
  let some indices ← indicesFromMinimal? p soln | throw .InvalidParams
  let some hasher ← LeafHasher.new? p input nonce kernel | throw .UnsupportedInputLength
  validateTree? p indices fun blocks digests => hasher.hash? blocks digests

/-- `equihash 0.3.0`'s `is_valid_solution` (`src/verify.rs`, lines 243–255) for `soln`, a
    minimally encoded solution for `input ‖ nonce` of any length, with parameters `n` and `k`.

`is_valid_solution_recursive` and the functions it calls (`src/verify.rs`, lines 16–239) have
the bodies of `zakura-equihash 4.0.0`'s test-only copies (`Verifier/Recursive.lean`), but for
two differences: `initialise_state` spells out `"ZcashPoW"` where Zakura names it, and
`Node::new` calls 0.3.0's `expand_array`, which computes what Zakura's does
(`expandArrayAlloc?_eq`). Around them, 0.3.0's `Kind` has no `UnsupportedInputLength`, which
none of them returns, and only visibility, `cfg(test)` and `Node`'s `derive(Clone)` differ. -/
def isValidSolution_equihash_0_3_0? (n k : ℕ) (input nonce soln : List ℕ) :
    ExceptT Kind Option Unit := do
  let some p := Params.newUnbounded? n k | throw .InvalidParams
  let some indices ← indicesFromMinimalWrapping? p soln | throw .InvalidParams
  -- Recursive validation is faster.
  isValidSolutionRecursive? p input nonce indices

/-- The closure `equihash 0.3.1`'s `is_valid_solution` hashes with when `input ‖ nonce` is not
    140 bytes (`src/verify.rs`, lines 276–281): `blake2b_simd`'s digest of each block, from
    `state`, which absorbed `input` then `nonce`, written over the first bytes of its digest;
    `zip` leaves any digests past the blocks as they are.

`digest[..hash.as_bytes().len()]` cannot panic: a `Digest` is `[u8; 64]` and the digest length
is `hash_output`, at most 64. -/
def blake2bSimdHash? (state : Blake2b.State) (blocks : List ℕ) (digests : List (List ℕ)) :
    Option (List (List ℕ)) :=
  pure ((blocks.zip digests).map (fun (block, digest) =>
    let hash := generateHash state block
    hash ++ digest.drop hash.length) ++ digests.drop blocks.length)

/-- `equihash 0.3.1`'s `is_valid_solution` (`src/verify.rs`, lines 258–283) for `soln`, a
    minimally encoded solution for `input ‖ nonce` of any length, with parameters `n` and `k`,
    on a CPU where `Kernel::detect()` picks `kernel`.

0.3.1 is `zakura-equihash 4.0.0`'s verifier backported: its `src/params.rs`, `src/minimal.rs`,
`src/leaf_hash.rs` and `src/verify/tree.rs` are Zakura's files, but for visibility, formatting
and parentheses, `"ZcashPoW"` spelled out in `leaf_hash.rs`, one more test, and the
`unsafe-verifier` feature, which gates the AVX2 and NEON kernels and is off by default: a
default build compiles only `Kernel::Portable`, so `kernel` is `.portable` for it.
`src/verify.rs` keeps 0.3.0's recursive verifier for tests only, and `Kind` has no
`UnsupportedInputLength`. Two differences reach `is_valid_solution`: `Params::new` makes
0.3.0's four checks (`src/params.rs`, lines 9–20; `Params.newUnbounded?`) before Zakura's
checked `solution_bytes` (lines 22–28), and `LeafHasher::new` returning `None`
(`src/leaf_hash.rs`, lines 378–380) is no error: the verifier then hashes with `blake2b_simd`,
through 0.3.0's `initialise_state` and `generate_hash` (lines 129–147), as
`is_valid_solution_recursive` does. -/
def isValidSolution_equihash_0_3_1? (kernel : Kernel) (n k : ℕ) (input nonce soln : List ℕ) :
    ExceptT Kind Option Unit := do
  let some p := Params.newUnbounded? n k | throw .InvalidParams
  let some indices ← indicesFromMinimal? p soln | throw .InvalidParams
  if let some hasher ← LeafHasher.new? p input nonce kernel then
    return ← validateTree? p indices fun blocks digests => hasher.hash? blocks digests
  let mut state ← initialiseState? p.n p.k p.hashOutput
  state := state.update input
  state := state.update nonce
  validateTree? p indices (blake2bSimdHash? state)

end Equihash.Verifier
