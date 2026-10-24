/-
Big-endian numbers and the digits of a byte sequence: the arithmetic `expand_array`
computes with.
-/
module

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Equihash

/-- A sequence of bytes (each `< 256`) read as one big-endian number. -/
def beNat (l : List ℕ) : ℕ := l.foldl (fun a b => 256 * a + b) 0

@[simp] theorem beNat_nil : beNat [] = 0 := rfl

theorem beNat_append_singleton (l : List ℕ) (b : ℕ) : beNat (l ++ [b]) = 256 * beNat l + b := by
  simp [beNat, List.foldl_append]

theorem foldl_beNat (l : List ℕ) (a : ℕ) :
    l.foldl (fun a b => 256 * a + b) a = a * 256 ^ l.length + beNat l := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons, beNat] at *
    rw [ih, ih (256 * 0 + x)]
    simp [pow_succ]; ring

theorem beNat_append (l₁ l₂ : List ℕ) :
    beNat (l₁ ++ l₂) = beNat l₁ * 256 ^ l₂.length + beNat l₂ := by
  simp only [beNat, List.foldl_append]
  exact foldl_beNat l₂ _

theorem beNat_lt (l : List ℕ) (h : ∀ b ∈ l, b < 256) : beNat l < 256 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l b ih =>
    rw [beNat_append_singleton, List.length_append, List.length_singleton, pow_succ]
    have := ih (fun x hx => h x (by simp [hx]))
    have := h b (by simp)
    nlinarith

/-- Byte `x` of a big-endian number is the `x`-th byte of its encoding. -/
theorem beNat_byte (l : List ℕ) (h : ∀ b ∈ l, b < 256) (x : ℕ) (hx : x < l.length) :
    beNat l / 256 ^ (l.length - 1 - x) % 256 = l[x] := by
  have hsplit := beNat_append (l.take (x + 1)) (l.drop (x + 1))
  rw [List.take_append_drop] at hsplit
  have hd : beNat (l.drop (x + 1)) < 256 ^ (l.drop (x + 1)).length :=
    beNat_lt _ (fun b hb => h b (List.mem_of_mem_drop hb))
  have hlen : (l.drop (x + 1)).length = l.length - 1 - x := by simp; omega
  rw [hlen] at hsplit hd
  rw [hsplit, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hd,
    zero_add]
  have ht : l.take (x + 1) = l.take x ++ [l[x]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hx]; rfl
  rw [ht, beNat_append_singleton, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (h _ (List.getElem_mem hx))

/-- Expansion to `w`-byte chunks leaves `L > 0` bytes the same length only when each digit
    is exactly `w` bytes: `c = 8·w`. -/
theorem eq_of_expanded_len (c w L : ℕ) (hc : 0 < c) (hdiv : c ∣ 8 * L) (hL : 0 < L)
    (h : 8 * w * L / c = L) : c = 8 * w := by
  obtain ⟨m, hm⟩ := hdiv
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hm; omega)
  have : 8 * w * L / c = w * m := by
    rw [show 8 * w * L = w * m * c by rw [Nat.mul_comm 8 w, Nat.mul_assoc, hm]; ring,
      Nat.mul_div_cancel _ hc]
  rw [this] at h
  have : c * m = 8 * w * m := by rw [← hm, ← h]; ring
  exact Nat.eq_of_mul_eq_mul_right hm0 this

/-- **Digit `t`** of width `c` of a `8L`-bit big-endian number `V`: bits `t·c ..
    (t+1)·c` counting from the most significant. -/
def digit (c L V t : ℕ) : ℕ := V / 2 ^ (8 * L - (t + 1) * c) % 2 ^ c

/-- Byte `x` of `D` written big-endian in `w` bytes. -/
def beByte (w D x : ℕ) : ℕ := D >>> (8 * (w - 1 - x)) % 2 ^ 8

/-! ## Bit-level facts behind `expand_array_into` -/

/-- **Accumulate.** Shifting a byte `b` into a 32-bit accumulator keeps its low `a + 8`
    bits equal to its previous low `a` bits followed by `b`. -/
theorem acc_shift_or (v b a : ℕ) (hb : b < 2 ^ 8) (ha : a + 8 ≤ 32) :
    ((v * 2 ^ 8 % 2 ^ 32) ||| b) % 2 ^ (a + 8) = v % 2 ^ a * 2 ^ 8 + b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow,
    Nat.mul_comm (v % 2 ^ a), Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_mod_two_pow]
  rcases Nat.lt_or_ge i 8 with hi | hi
  · simp [hi, show i < a + 8 by omega, show ¬ 8 ≤ i by omega]
  · have eb : b.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hi))
    by_cases h : i < a + 8
    · simp [eb, h, hi, show i < 32 by omega, show ¬ i < 8 by omega, show i - 8 < a by omega]
    · simp [eb, h, show ¬ i < 8 by omega, show ¬ i - 8 < a by omega]

/-- **Emit.** The inner loop's shift and mask extract byte `e` (from the least
    significant) of the digit `⌊v / 2^a⌋ mod 2^c`. -/
theorem emit_byte (v a c e : ℕ) :
    (v >>> (a + 8 * e) &&& ((2 ^ c - 1) >>> (8 * e) &&& (2 ^ 8 - 1))) % 2 ^ 8 =
      (v >>> a % 2 ^ c) >>> (8 * e) % 2 ^ 8 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_and, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one, -Nat.reducePow]
  by_cases hi : i < 8
  · rw [show a + 8 * e + i = a + (8 * e + i) by omega]
    cases v.testBit (a + (8 * e + i)) <;> simp [hi]
  · simp [hi]

/-- The padding bytes of an expanded digit are zero: a digit below `2^c` fits in its last
    `w − pad` bytes when `c ≤ 8·(w − pad)`. -/
theorem beByte_pad (w pad c D x : ℕ) (hD : D < 2 ^ c) (hc : c ≤ 8 * (w - pad)) (hx : x < pad)
    (hpad : pad ≤ w) : beByte w D x = 0 := by
  simp only [beByte, Nat.shiftRight_eq_div_pow]
  rw [Nat.div_eq_of_lt (lt_of_lt_of_le hD (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  rfl

/-- Masking to `a + c` bits, then dropping the low `a`, is dropping the low `a`, then
    masking to `c` bits. -/
theorem mod_shiftRight (x a c : ℕ) : (x % 2 ^ (a + c)) >>> a = (x >>> a) % 2 ^ c := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_shiftRight, Nat.testBit_mod_two_pow]
  by_cases h : i < c <;> simp [h, show (a + i < a + c) = (i < c) by simp]

/-- Shifting a byte into a number, modulo `2^(a+8)`. -/
theorem append_byte_mod (P b a : ℕ) (hb : b < 2 ^ 8) :
    (2 ^ 8 * P + b) % 2 ^ (a + 8) = P % 2 ^ a * 2 ^ 8 + b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_mul_add _ hb, Nat.mul_comm,
    Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_mod_two_pow]
  by_cases hi : i < 8
  · simp [hi, show i < a + 8 by omega]
  · by_cases h : i < a + 8
    · simp [hi, h, show i - 8 < a by omega]
    · simp [hi, h, show ¬ i - 8 < a by omega]

/-- Eight more bits complete at most one `c`-bit digit (`c ≥ 8`): exactly one when the
    pending bits reach `c`. -/
theorem div_mod_add_eight (a c : ℕ) (hc : 8 ≤ c) :
    (c ≤ a % c + 8 → (a + 8) / c = a / c + 1 ∧ (a + 8) % c = a % c + 8 - c) ∧
    (a % c + 8 < c → (a + 8) / c = a / c ∧ (a + 8) % c = a % c + 8) := by
  have hdm := Nat.div_add_mod a c
  have hlt := Nat.mod_lt a (show 0 < c by omega)
  generalize a / c = q at *
  generalize a % c = r at *
  subst hdm
  constructor
  · intro h
    exact (Nat.div_mod_unique (by omega)).mpr
      ⟨by rw [Nat.mul_add, Nat.mul_one]; omega, by omega⟩
  · intro h
    exact (Nat.div_mod_unique (by omega)).mpr ⟨by omega, h⟩

/-- A digit of the whole number is the same digit of a prefix: the bits after the prefix
    are shifted out. -/
theorem div_prefix (P R r a : ℕ) (hR : R < 256 ^ r) :
    (P * 256 ^ r + R) / 2 ^ (8 * r + a) = P / 2 ^ a := by
  rw [pow_add, ← Nat.div_div_eq_div_mul, show (2 : ℕ) ^ (8 * r) = 256 ^ r by
    rw [pow_mul]; norm_num]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hR, zero_add]

end Equihash
