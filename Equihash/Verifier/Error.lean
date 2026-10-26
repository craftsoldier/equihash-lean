/-
`src/verify.rs`: why a solution failed to verify.

A function that returns a Rust `Result` is a Lean function into `ExceptT Kind Option`: `.run` is
`none` where the Rust panics, `some (.error kind)` for `Err(Error(kind))`, and `some (.ok a)` for
`Ok(a)`. `Error` wraps a `Kind` and adds nothing, so both are `Kind` here.
-/
module

@[expose] public section

namespace Equihash.Verifier

/-- `Kind` (`src/verify.rs`, lines 110–118; 0.3.0: 98–105; 0.3.1: 109–115): why a solution
    failed to verify. `UnsupportedInputLength` is `zakura-equihash`'s alone. -/
inductive Kind where
  | InvalidParams
  | Collision
  | OutOfOrder
  | DuplicateIdxs
  | NonZeroRootHash
  | UnsupportedInputLength
  deriving DecidableEq, Repr

end Equihash.Verifier
