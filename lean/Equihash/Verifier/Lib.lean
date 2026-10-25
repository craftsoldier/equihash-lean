/-
`src/lib.rs`: the constant the crate's modules share.
-/
module

public import Mathlib.Data.List.Basic

@[expose] public section

namespace Equihash.Verifier

/-- `BLAKE2B_PERSONALIZATION_PREFIX` (`src/lib.rs`, line 40): `*b"ZcashPoW"`. -/
def BLAKE2B_PERSONALIZATION_PREFIX : List ℕ := [90, 99, 97, 115, 104, 80, 111, 87]

end Equihash.Verifier
