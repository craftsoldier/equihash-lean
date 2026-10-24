/-
Algebra of `Spec.Bits` (bit sequences) under `Spec.xor` and `Spec.xorAll`.
-/
module

public import Equihash.Spec

@[expose] public section

namespace Equihash.Spec

/-- The all-zero bit sequence of length `n`. -/
abbrev zeros (n : ℕ) : Bits := List.replicate n false

@[simp] theorem length_xor (a b : Bits) : (xor a b).length = min a.length b.length := by
  simp [xor]

theorem length_bitsOfBytes (bs : List Byte) : (bitsOfBytes bs).length = 8 * bs.length := by
  simp [bitsOfBytes, List.length_flatMap, Nat.mul_comm]

theorem xor_comm (a b : Bits) : xor a b = xor b a := by
  simp only [xor]
  exact List.zipWith_comm_of_comm (fun x y => Bool.xor_comm x y)

theorem xor_assoc (a b c : Bits) : xor (xor a b) c = xor a (xor b c) := by
  simp only [xor]
  induction a generalizing b c with
  | nil => simp
  | cons x a ih =>
    cases b with
    | nil => simp
    | cons y b =>
      cases c with
      | nil => simp
      | cons z c => simp [ih]

theorem xor_zeros (a : Bits) : xor a (zeros a.length) = a := by
  induction a with
  | nil => rfl
  | cons x a ih => simp_all [xor, List.replicate_succ]

theorem zeros_xor (a : Bits) : xor (zeros a.length) a = a := by
  rw [xor_comm, xor_zeros]

theorem xor_self (a : Bits) : xor a a = zeros a.length := by
  induction a with
  | nil => rfl
  | cons x a ih => simp_all [xor, List.replicate_succ]

theorem take_xor (c : ℕ) (a b : Bits) : (xor a b).take c = xor (a.take c) (b.take c) := by
  simp [xor, List.take_zipWith]

theorem drop_xor (c : ℕ) (a b : Bits) : (xor a b).drop c = xor (a.drop c) (b.drop c) := by
  simp [xor, List.drop_zipWith]

/-- Two sequences of equal length agree exactly when their XOR is zero. -/
theorem xor_eq_zeros_iff {a b : Bits} (h : a.length = b.length) :
    xor a b = zeros a.length ↔ a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [xor]
  | cons x a ih =>
    cases b with
    | nil => simp at h
    | cons y b =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      have := ih h
      simp only [xor] at this ⊢
      simp [List.replicate_succ, this]

/-- `xorAll` of sequences all of length `n` has length `n`. -/
theorem length_xorAll (n : ℕ) (xs : List Bits) (h : ∀ x ∈ xs, x.length = n) :
    (xorAll n xs).length = n := by
  simp only [xorAll]
  suffices ∀ acc : Bits, acc.length = n → (xs.foldl xor acc).length = n from
    this _ (by simp)
  induction xs with
  | nil => simp
  | cons x xs ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    exact ih (fun y hy => h y (by simp [hy])) _ (by simp [hacc, h x (by simp)])

/-- Folding `xor` from any start `acc` is `acc` XORed with the fold from zero. -/
theorem foldl_xor (n : ℕ) (ys : List Bits) (hys : ∀ y ∈ ys, y.length = n) (acc : Bits)
    (hacc : acc.length = n) : ys.foldl xor acc = xor acc (ys.foldl xor (zeros n)) := by
  induction ys generalizing acc with
  | nil => simpa [hacc] using (xor_zeros acc).symm
  | cons y ys ih =>
    have hy := hys y (by simp)
    have hys' : ∀ z ∈ ys, z.length = n := fun z hz => hys z (by simp [hz])
    have hzy : xor (zeros n) y = y := by simpa [hy] using zeros_xor y
    simp only [List.foldl_cons, hzy]
    rw [ih hys' _ (by simp [hacc, hy]), ih hys' y hy, xor_assoc]

/-- `xorAll` over a concatenation XORs the two parts. -/
theorem xorAll_append (n : ℕ) (xs ys : List Bits) (hxs : ∀ x ∈ xs, x.length = n)
    (hys : ∀ y ∈ ys, y.length = n) :
    xorAll n (xs ++ ys) = xor (xorAll n xs) (xorAll n ys) := by
  simp only [xorAll, List.foldl_append]
  exact foldl_xor n ys hys _ (length_xorAll n xs hxs)

/-! ## Leading zeros -/

theorem hasLeadingZeros_iff {z : ℕ} {x : Bits} (hz : z ≤ x.length) :
    HasLeadingZeros z x ↔ x.take z = zeros z := by
  simp only [HasLeadingZeros, zeros]
  rw [List.eq_replicate_iff]
  simp [hz]

/-- **Zeros accumulate.** If `a` and `b` both start with `m` zero bits, their XOR starts
    with `m + c` zero bits exactly when `a` and `b` agree on the `c` bits after those. -/
theorem hasLeadingZeros_xor {a b : Bits} {n m c : ℕ} (ha : a.length = n) (hb : b.length = n)
    (hmc : m + c ≤ n) (hza : HasLeadingZeros m a) (hzb : HasLeadingZeros m b) :
    HasLeadingZeros (m + c) (xor a b) ↔ (a.drop m).take c = (b.drop m).take c := by
  rw [hasLeadingZeros_iff (by simp [ha, hb]; omega)]
  rw [hasLeadingZeros_iff (by omega)] at hza
  rw [hasLeadingZeros_iff (by omega)] at hzb
  have hlen : ((a.drop m).take c).length = ((b.drop m).take c).length := by
    simp [ha, hb]
  rw [List.take_add, Spec.take_xor, hza, hzb, Spec.xor_self, Spec.drop_xor, Spec.take_xor,
    ← xor_eq_zeros_iff hlen]
  simp only [zeros, List.length_replicate, List.replicate_add, List.append_cancel_left_eq]
  simp [ha, show min c (n - m) = c by omega]

/-- A sequence of `a + b` bits is zero exactly when its first `a` and next `b` bits are. -/
theorem eq_zeros_split (x : Bits) (a b : ℕ) (h : x.length = a + b) :
    x = zeros (a + b) ↔ x.take a = zeros a ∧ (x.drop a).take b = zeros b := by
  have hd : (x.drop a).take b = x.drop a := List.take_of_length_le (by simp [h])
  rw [hd]
  conv_lhs => rw [← List.take_append_drop a x]
  rw [zeros, List.replicate_add]
  constructor
  · intro e; exact List.append_inj e (by simp [h])
  · rintro ⟨h1, h2⟩; rw [h1, h2]

end Equihash.Spec
