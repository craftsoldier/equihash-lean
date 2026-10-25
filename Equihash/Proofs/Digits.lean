/-
The digits of a bit sequence, and their expansion into bytes: how the Rust verifier stores
§7.7.1's hash values.
-/
module

public import Equihash.Proofs.Bits
public import Equihash.Proofs.Expand

@[expose] public section

namespace Equihash.Spec

/-- A bit sequence read as a big-endian number. -/
def bitsVal (b : Bits) : ℕ := b.foldl (fun a x => 2 * a + x.toNat) 0

theorem foldl_bitsVal (b : Bits) (a : ℕ) :
    b.foldl (fun a x => 2 * a + x.toNat) a = a * 2 ^ b.length + bitsVal b := by
  induction b generalizing a with
  | nil => simp [bitsVal]
  | cons x b ih =>
    simp only [List.foldl_cons, bitsVal] at *
    rw [ih, ih (2 * 0 + x.toNat)]
    simp [pow_succ]; ring

theorem bitsVal_append (a b : Bits) : bitsVal (a ++ b) = bitsVal a * 2 ^ b.length + bitsVal b := by
  simp only [bitsVal, List.foldl_append]
  exact foldl_bitsVal b _

theorem bitsVal_lt (b : Bits) : bitsVal b < 2 ^ b.length := by
  induction b using List.reverseRecOn with
  | nil => simp [bitsVal]
  | append_singleton b x ih =>
    rw [bitsVal_append, List.length_append, List.length_singleton, pow_one, pow_succ]
    have : bitsVal [x] ≤ 1 := by cases x <;> simp [bitsVal]
    omega

/-- Big-endian representation is injective on sequences of one length. -/
theorem bitsVal_cons (x : Bool) (a : Bits) :
    bitsVal (x :: a) = x.toNat * 2 ^ a.length + bitsVal a := by
  rw [show x :: a = [x] ++ a from rfl, bitsVal_append]
  simp [bitsVal]

theorem bitsVal_inj {a b : Bits} (h : a.length = b.length) (hv : bitsVal a = bitsVal b) :
    a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons x a ih =>
    cases b with
    | nil => simp at h
    | cons y b =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rw [bitsVal_cons, bitsVal_cons, h] at hv
      have ha := bitsVal_lt a
      have hb := bitsVal_lt b
      rw [h] at ha
      -- The leading bit is the quotient by `2^|b|`.
      have hq : ∀ (z : Bool) (v : ℕ), v < 2 ^ b.length →
          (z.toNat * 2 ^ b.length + v) / 2 ^ b.length = z.toNat := fun z v hv => by
        rw [Nat.mul_comm, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hv, add_zero]
      have hxy : x.toNat = y.toNat := by rw [← hq x _ ha, hv, hq y _ hb]
      rw [hxy] at hv
      rw [ih h (by omega), show x = y by cases x <;> cases y <;> simp_all]

/-- Digit `t` of width `c`: bits `t·c .. (t+1)·c`, as a number. -/
def digitVal (c : ℕ) (B : Bits) (t : ℕ) : ℕ := bitsVal ((B.drop (t * c)).take c)

/-! ## Bits of bytes -/

/-- A byte's bits, most significant first, have the byte's value. -/
theorem bitsVal_byte :
    ∀ b : Byte, bitsVal ((List.range 8).map fun j => b.getMsbD j) = b.toNat := by
  decide

/-- **Bit order.** `bitsOfBytes` reads each byte most significant bit first,
    so the bits of a byte sequence have the value of its big-endian number. -/
theorem bitsVal_bitsOfBytes (bs : List Byte) :
    bitsVal (bitsOfBytes bs) = beNat (bs.map (·.toNat)) := by
  induction bs using List.reverseRecOn with
  | nil => simp [bitsOfBytes, bitsVal]
  | append_singleton bs b ih =>
    rw [bitsOfBytes, List.flatMap_append, ← bitsOfBytes, bitsVal_append, ih, List.map_append,
      List.map_singleton, beNat_append_singleton]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_map,
      List.length_range, bitsVal_byte]
    ring

theorem bitsOfBytes_cons (b : Byte) (bs : List Byte) :
    bitsOfBytes (b :: bs) = ((List.range 8).map fun j => b.getMsbD j) ++ bitsOfBytes bs := rfl

/-- Dropping whole bytes' worth of bits is dropping the bytes. -/
theorem bitsOfBytes_drop (bs : List Byte) (a : ℕ) :
    (bitsOfBytes bs).drop (8 * a) = bitsOfBytes (bs.drop a) := by
  induction a generalizing bs with
  | zero => simp
  | succ a ih =>
    cases bs with
    | nil => simp [bitsOfBytes]
    | cons b bs =>
      rw [bitsOfBytes_cons, Nat.mul_succ, Nat.add_comm, ← List.drop_drop,
        List.drop_left' (by simp), ih]
      rfl

/-- Taking whole bytes' worth of bits is taking the bytes. -/
theorem bitsOfBytes_take (bs : List Byte) (a : ℕ) :
    (bitsOfBytes bs).take (8 * a) = bitsOfBytes (bs.take a) := by
  induction a generalizing bs with
  | zero => simp [bitsOfBytes]
  | succ a ih =>
    cases bs with
    | nil => simp [bitsOfBytes]
    | cons b bs =>
      rw [bitsOfBytes_cons, Nat.mul_succ, Nat.add_comm, List.take_add, List.take_left' (by simp),
        List.drop_left' (by simp), ih]
      rfl

/-- The arithmetic digit `expand_array` extracts is the value of the corresponding bits. -/
theorem digit_eq_digitVal (B : Bits) (c L t : ℕ) (hlen : B.length = 8 * L)
    (h : (t + 1) * c ≤ 8 * L) : digit c L (bitsVal B) t = digitVal c B t := by
  -- Cut `B` after digit `t`.
  have hB := List.take_append_drop ((t + 1) * c) B
  have hdrop : (B.drop ((t + 1) * c)).length = 8 * L - (t + 1) * c := by simp [hlen]
  rw [digit]
  conv_lhs => rw [← hB]
  rw [bitsVal_append, hdrop, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt (by have := bitsVal_lt (B.drop ((t + 1) * c)); rwa [hdrop] at this),
    zero_add]
  -- The first `t + 1` digits are the first `t`, then digit `t`.
  have htake : B.take ((t + 1) * c) = B.take (t * c) ++ (B.drop (t * c)).take c := by
    rw [Nat.succ_mul, List.take_add]
  have hlc : ((B.drop (t * c)).take c).length = c := by
    simp only [List.length_take, List.length_drop, hlen]; rw [Nat.succ_mul] at h; omega
  rw [htake, bitsVal_append, hlc, Nat.add_comm, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (by have := bitsVal_lt ((B.drop (t * c)).take c); rwa [hlc] at this),
    digitVal]

/-! ## Digit algebra -/

theorem digitVal_lt (c : ℕ) (B : Bits) (t : ℕ) : digitVal c B t < 2 ^ c :=
  lt_of_lt_of_le (bitsVal_lt _) (Nat.pow_le_pow_right (by norm_num) (by simp))

theorem digitVal_drop (c : ℕ) (B : Bits) (t : ℕ) :
    digitVal c (B.drop c) t = digitVal c B (t + 1) := by
  simp [digitVal, List.drop_drop, Nat.succ_mul, Nat.add_comm]

/-- Equal first digits are equal first `c` bits. -/
theorem digitVal_zero_eq_iff {A B : Bits} {c : ℕ} (hA : c ≤ A.length) (hB : c ≤ B.length) :
    digitVal c A 0 = digitVal c B 0 ↔ A.take c = B.take c := by
  simp only [digitVal, Nat.zero_mul, List.drop_zero]
  exact ⟨bitsVal_inj (by simp [hA, hB]), fun h => by rw [h]⟩

theorem bitsVal_zeros (n : ℕ) : bitsVal (zeros n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [zeros, List.replicate_succ, bitsVal_cons, ← zeros, ih]; simp

/-- A zero first digit is `c` zero bits. -/
theorem digitVal_zero_eq_zero_iff {B : Bits} {c : ℕ} (hB : c ≤ B.length) :
    digitVal c B 0 = 0 ↔ B.take c = zeros c := by
  simp only [digitVal, Nat.zero_mul, List.drop_zero]
  refine ⟨fun h => bitsVal_inj (by simp [hB]) (by rw [h, bitsVal_zeros]), fun h => ?_⟩
  rw [h, bitsVal_zeros]

theorem testBit_bitsVal_cons (x : Bool) (a : Bits) (i : ℕ) :
    (bitsVal (x :: a)).testBit i = if i = a.length then x else (bitsVal a).testBit i := by
  rw [bitsVal_cons, Nat.mul_comm, Nat.testBit_two_pow_mul_add _ (bitsVal_lt a)]
  rcases lt_trichotomy i a.length with hi | rfl | hi
  · simp [hi, Nat.ne_of_lt hi]
  · cases x <;> simp
  · have h1 : x.toNat.testBit (i - a.length) = false := Nat.testBit_lt_two_pow
      (lt_of_le_of_lt (Bool.toNat_le x) (Nat.one_lt_two_pow (by omega)))
    have h2 : (bitsVal a).testBit i = false := Nat.testBit_lt_two_pow
      (lt_of_lt_of_le (bitsVal_lt a) (Nat.pow_le_pow_right (by norm_num) hi.le))
    simp [show ¬ i < a.length by omega, show i ≠ a.length by omega, h1, h2]

/-- The value of an XOR is the XOR of the values. -/
theorem bitsVal_xor {a b : Bits} (h : a.length = b.length) :
    bitsVal (xor a b) = bitsVal a ^^^ bitsVal b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [xor, bitsVal]
  | cons x a ih =>
    cases b with
    | nil => simp at h
    | cons y b =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      apply Nat.eq_of_testBit_eq
      intro i
      have hx : xor (x :: a) (y :: b) = (x ^^ y) :: xor a b := rfl
      rw [hx, testBit_bitsVal_cons, Nat.testBit_xor, testBit_bitsVal_cons,
        testBit_bitsVal_cons, ih h, Nat.testBit_xor]
      simp [h]
      split_ifs <;> rfl

theorem digitVal_xor {A B : Bits} (h : A.length = B.length) (c t : ℕ) :
    digitVal c (xor A B) t = digitVal c A t ^^^ digitVal c B t := by
  simp only [digitVal, drop_xor, take_xor]
  exact bitsVal_xor (by simp [h])

/-! ## Chunks: a digit written in `w` big-endian bytes -/

/-- The `w` big-endian bytes of `D`. -/
def chunk (w D : ℕ) : List ℕ := (List.range w).map (beByte w D)

/-- A chunk read back as a number is the digit it encodes. -/
theorem beNat_chunk (w D : ℕ) (hD : D < 256 ^ w) : beNat (chunk w D) = D := by
  induction w generalizing D with
  | zero => simp_all [chunk]
  | succ w ih =>
    have hrest : D / 256 < 256 ^ w := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num), ← pow_succ]; exact hD
    have hchunk : chunk (w + 1) D = chunk w (D / 256) ++ [D % 256] := by
      simp only [chunk, List.range_succ, List.map_append, List.map_singleton, beByte,
        Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 8 = 256 by norm_num]
      congr 1
      · apply List.map_congr_left
        intro x hx
        have hx' := List.mem_range.mp hx
        simp only [beByte, Nat.shiftRight_eq_div_pow]
        rw [show w + 1 - 1 - x = (w - 1 - x) + 1 by omega, Nat.mul_succ, pow_add,
          show (2 : ℕ) ^ 8 = 256 by norm_num, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
      · simp
    rw [hchunk, beNat_append_singleton, ih _ hrest]
    exact Nat.div_add_mod D 256

theorem beByte_xor (w D₁ D₂ x : ℕ) :
    beByte w (D₁ ^^^ D₂) x = beByte w D₁ x ^^^ beByte w D₂ x := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [beByte, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_xor]
  by_cases h : i < 8 <;> simp [h]

/-- **Expanded hash.** `bytes` holds the `c`-bit digits of `B`, each in `w` big-endian
    bytes: how the Rust verifier stores a node's hash. -/
def ExpandedN (c w : ℕ) (bytes : List ℕ) (B : Bits) : Prop :=
  bytes.length = B.length / c * w ∧
  ∀ t < B.length / c, ∀ x < w, bytes[t * w + x]? = some (beByte w (digitVal c B t) x)

/-- The first `w` bytes of an expanded hash are its first digit's chunk. -/
theorem ExpandedN.take {c w : ℕ} {bytes : List ℕ} {B : Bits} (h : ExpandedN c w bytes B)
    (hB : 1 ≤ B.length / c) : bytes.take w = chunk w (digitVal c B 0) := by
  apply List.ext_getElem?
  intro x
  rw [List.getElem?_take]
  by_cases hx : x < w
  · simp only [hx, ↓reduceIte, chunk]
    rw [show x = 0 * w + x by simp, h.2 0 hB x hx]
    simp [hx]
  · simp [hx, chunk]

section Operations
variable {c w : ℕ} {ba bb : List ℕ} {A B : Bits}

/-- Chunks determine their digits. -/
theorem chunk_inj (hc : c ≤ 8 * w) {D₁ D₂ : ℕ} (h₁ : D₁ < 2 ^ c) (h₂ : D₂ < 2 ^ c) :
    chunk w D₁ = chunk w D₂ ↔ D₁ = D₂ := by
  have hle : 2 ^ c ≤ 256 ^ w := by
    rw [show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) hc
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  rw [← beNat_chunk w D₁ (by omega), h, beNat_chunk w D₂ (by omega)]

/-- **`has_collision`**: the first `w` bytes of two expanded hashes agree exactly when their
    first digits do. -/
theorem ExpandedN.take_eq_iff (hc : c ≤ 8 * w) (hA : ExpandedN c w ba A) (hB : ExpandedN c w bb B)
    (hA1 : 1 ≤ A.length / c) (hB1 : 1 ≤ B.length / c) (hcA : c ≤ A.length)
    (hcB : c ≤ B.length) :
    ba.take w = bb.take w ↔ A.take c = B.take c := by
  rw [hA.take hA1, hB.take hB1, chunk_inj hc (digitVal_lt _ _ _) (digitVal_lt _ _ _),
    digitVal_zero_eq_iff hcA hcB]

/-- **`is_zero`**: the first `w` bytes of an expanded hash are zero exactly when its first
    digit is. -/
theorem ExpandedN.take_eq_zero_iff (hc : c ≤ 8 * w) (hA : ExpandedN c w ba A)
    (hA1 : 1 ≤ A.length / c) (hcA : c ≤ A.length) :
    ba.take w = List.replicate w 0 ↔ A.take c = zeros c := by
  have h0 : chunk w 0 = List.replicate w 0 := by
    apply List.ext_getElem <;> simp [chunk, beByte]
  rw [hA.take hA1, ← h0, chunk_inj hc (digitVal_lt _ _ _) (by positivity),
    digitVal_zero_eq_zero_iff hcA]

/-- **`from_children`**: XORing two expanded hashes byte by byte and dropping the first
    `w` bytes expands the XOR of the hashes without its first digit. -/
theorem ExpandedN.xor_drop (hA : ExpandedN c w ba A) (hB : ExpandedN c w bb B)
    (hAB : A.length = B.length) :
    ExpandedN c w ((List.zipWith (· ^^^ ·) ba bb).drop w) ((xor A B).drop c) := by
  have hlen : ba.length = bb.length := by rw [hA.1, hB.1, hAB]
  have hq : ((xor A B).drop c).length / c = A.length / c - 1 := by
    simp only [List.length_drop, length_xor, hAB, Nat.min_self]
    rw [← hAB, show A.length - c = A.length - c * 1 by simp, Nat.sub_mul_div]
  refine ⟨?_, fun t ht x hx => ?_⟩
  · rw [List.length_drop, List.length_zipWith, hlen, Nat.min_self, hB.1, hq, ← hAB, Nat.sub_mul,
      one_mul]
  · rw [hq] at ht
    rw [List.getElem?_drop, show w + (t * w + x) = (t + 1) * w + x by ring, List.getElem?_zipWith,
      hA.2 (t + 1) (by omega) x hx, hB.2 (t + 1) (by rw [← hAB]; omega) x hx]
    simp only [digitVal_drop, digitVal_xor hAB, beByte_xor]

end Operations

end Equihash.Spec
