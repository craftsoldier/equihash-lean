/-
Each published crate's `is_valid_solution`, built from the shared verifier pieces.

| Crate             | Version | Verifier                    | Source                        |
|-------------------|---------|-----------------------------|-------------------------------|
| `zakura-equihash` | 4.0.0   | single-pass, 140-byte input | `rust/zakura-equihash-4.0.0/` |

A Rust panic, and a Rust `Err`, are both `none`: the verifier did not accept.
-/
module

public import Equihash.Verifier.LeafHash
public import Equihash.Verifier.SinglePass

@[expose] public section

namespace Equihash.Verifier

/-- `zakura-equihash 4.0.0`'s `is_valid_solution` (`src/verify.rs`, lines 269–280): `some ()`
    exactly when the Rust returns `Ok(())` for `soln`, a minimally encoded solution for
    `input ‖ nonce` with parameters `n` and `k`.

`LeafHasher::new` runs the portable kernel here (see `LeafHasher.new?`). -/
def isValidSolution? (n k : ℕ) (input nonce soln : List ℕ) : Option Unit := do
  let p ← Params.new? n k
  let indices ← indicesFromMinimal? p soln
  let hasher ← LeafHasher.new? p input nonce
  validateTree? p indices fun blocks digests => hasher.hash? blocks digests

end Equihash.Verifier
