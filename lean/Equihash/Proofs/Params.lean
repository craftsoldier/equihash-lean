/-
The parameters: what `src/params.rs` computes, in terms of `Spec`.
-/
module

public import Equihash.Verifier.Params
public import Equihash.Proofs.Std
public import Equihash.Proofs.Blocks

@[expose] public section

namespace Equihash

/-- The parameters Zakura's verifier accepts. `Params::new` (`src/params.rs`) checks
    `8 ∣ n`, `k ≥ 3`, `k < n`, `(k + 1) ∣ n`, `n ≤ 512` and `8 ≤ n / (k + 1) ≤ 24`: the fields
    below and those of `Spec.Params`, whose other two (`0 < n`, `8 ∣ n · ⌊512/n⌋`) follow
    from them. -/
structure ZakuraParams extends Spec.Params where
  n_dvd_8 : 8 ∣ n
  k_lt : k < n
  digit_ge : 8 ≤ n / (k + 1)
  digit_le : n / (k + 1) ≤ 24

end Equihash

namespace Equihash.Verifier

open Equihash.Spec

/-- A Rust `Params` holding the parameters `p`. -/
def Params.Is (rp : Params) (p : ZakuraParams) : Prop := rp.n = p.n ∧ rp.k = p.k

namespace Params

variable {rp : Params} {p : ZakuraParams} (h : rp.Is p)
include h

/-- `512 / n`: `m`, the hash values per BLAKE2b output. -/
theorem indicesPerHashOutput_eq : rp.indicesPerHashOutput = p.m := by
  simp [indicesPerHashOutput, Spec.Params.m, h.1]

/-- `(512 / n) · n / 8`: the BLAKE2b output length in bytes, `n·m/8`. -/
theorem hashOutput_eq : rp.hashOutput = p.n * p.m / 8 := by
  have hle : p.n * p.m ≤ 512 := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self 512 p.n
  simp only [hashOutput, indicesPerHashOutput_eq h, h.1]
  rw [Nat.mul_comm]
  exact Nat.mod_eq_of_lt (by omega)

/-- `n / (k + 1)`: the digit width. -/
theorem collisionBitLength_eq : rp.collisionBitLength = p.digitBits := by
  simp [collisionBitLength, Spec.Params.digitBits, h.1, h.2]

/-- `⌈(n / (k + 1)) / 8⌉`: bytes per expanded digit. -/
theorem collisionByteLength_eq : rp.collisionByteLength = (p.digitBits + 7) / 8 := by
  rw [collisionByteLength, collisionBitLength_eq h, divCeil_eq _ _ (by norm_num)]
  rfl

end Params

end Equihash.Verifier
