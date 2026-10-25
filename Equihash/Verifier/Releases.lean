/-
Each published crate's `is_valid_solution`, built from the shared verifier pieces.

| Crate             | Version | Verifier                    | Source                        |
|-------------------|---------|-----------------------------|-------------------------------|
| `zakura-equihash` | 4.0.0   | single-pass, 140-byte input | `rust/zakura-equihash-4.0.0/` |
| `equihash`        | 0.3.0   | recursive, any input        | `rust/equihash-0.3.0/`        |

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
    minimally encoded solution for `input ‖ nonce` with parameters `n` and `k`.

`LeafHasher::new` runs the portable kernel here (see `LeafHasher.new?`). -/
def isValidSolution? (n k : ℕ) (input nonce soln : List ℕ) : ExceptT Kind Option Unit := do
  let some p := Params.new? n k | throw .InvalidParams
  let some indices ← indicesFromMinimal? p soln | throw .InvalidParams
  let some hasher ← LeafHasher.new? p input nonce | throw .UnsupportedInputLength
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

end Equihash.Verifier
