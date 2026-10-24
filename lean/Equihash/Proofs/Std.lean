/-
What the standard library operations in `Verifier/Std.lean` compute.
-/
module

public import Equihash.Verifier.Std
public import Equihash.Spec
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Equihash.Verifier

/-- `div_ceil` is `⌈x / y⌉`: the quotient, plus one when there is a remainder. -/
theorem divCeil_eq (x y : ℕ) (hy : 0 < y) : divCeil x y = (x + y - 1) / y := by
  have hdm := Nat.div_add_mod x y
  have hr := Nat.mod_lt x hy
  simp only [divCeil]
  generalize x / y = q at *
  generalize x % y = r at *
  subst hdm
  split_ifs <;> symm <;> apply Nat.div_eq_of_lt_le <;>
    simp only [Nat.succ_mul, Nat.mul_comm q y] <;> omega

/-- `u32::to_le_bytes` is the specification's `I2LEOSP_32`. -/
theorem u32ToLeBytes_eq (x : ℕ) : (u32ToLeBytes x).map (BitVec.ofNat 8) = Spec.I2LEOSP 32 x := by
  have hmod : ∀ y, BitVec.ofNat 8 (y % 256) = BitVec.ofNat 8 y := fun y => by
    apply BitVec.eq_of_toNat_eq; simp
  simp [u32ToLeBytes, Spec.I2LEOSP, List.range_succ, hmod]

theorem slice?_eq {α : Type} (s : List α) (start «end» : ℕ) (h : start ≤ «end»)
    (h' : «end» ≤ s.length) :
    slice? s start «end» = some ((s.drop start).take («end» - start)) := by
  simp [slice?, h, h']

end Equihash.Verifier
