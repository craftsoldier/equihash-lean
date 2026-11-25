/-
RFC 7693's BLAKE2b as `Verifier/Blake2b.lean` computes it: its compression function as
`LeafHash.rounds` between a setup and a finalization, its words of bytes, its initial state,
and its output bytes.
-/
module

public import Equihash.Verifier.LeafHash
public import Equihash.Verifier.Blake2b
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Equihash.Verifier

open Equihash Equihash.Spec LeafHash

/-! ## The compression function -/

theorem g_eq_mix : LeafHash.g (L := UInt64) = Blake2b.mix := rfl

theorem IV_eq : LeafHash.IV = Blake2b.iv := rfl

/-- `SIGMA`'s twelve rows are RFC 7693's ten, the first two repeated. -/
theorem SIGMA_eq : ∀ r < 12, SIGMA[r]! = Blake2b.sigma[r % 10]! := by decide

theorem sigma_lt : ∀ r < 12, ∀ j < 16, (Blake2b.sigma[r % 10]!)[j]! < 16 := by decide

/-- The message words as an array: entry `i` is word `i`. -/
theorem getElem!_words (f : ℕ → UInt64) {i : ℕ} (hi : i < 16) :
    ((List.range 16).toArray.map f)[i]! = f i := by
  simp [hi]

/-- RFC 7693's twelve rounds, as `Blake2b.compress` runs them, are `rounds`. -/
theorem rounds_eq (v : Array UInt64) (m : Array UInt64) (word : ℕ → UInt64)
    (hm : ∀ i < 16, m[i]! = word i) :
    (Id.run do
      let mut v := v
      for i in [0:12] do
        let s := Blake2b.sigma[i % 10]!
        v := Blake2b.mix v 0 4 8 12 m[s[0]!]! m[s[1]!]!
        v := Blake2b.mix v 1 5 9 13 m[s[2]!]! m[s[3]!]!
        v := Blake2b.mix v 2 6 10 14 m[s[4]!]! m[s[5]!]!
        v := Blake2b.mix v 3 7 11 15 m[s[6]!]! m[s[7]!]!
        v := Blake2b.mix v 0 5 10 15 m[s[8]!]! m[s[9]!]!
        v := Blake2b.mix v 1 6 11 12 m[s[10]!]! m[s[11]!]!
        v := Blake2b.mix v 2 7 8 13 m[s[12]!]! m[s[13]!]!
        v := Blake2b.mix v 3 4 9 14 m[s[14]!]! m[s[15]!]!
      return v) = rounds v word := by
  simp only [rounds, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl]
  apply List.foldl_ext
  intro v r hr
  simp only [List.mem_range'_1] at hr
  have hs := sigma_lt r (by omega)
  rw [SIGMA_eq r (by omega), g_eq_mix]
  simp only [hm _ (hs 0 (by omega)), hm _ (hs 1 (by omega)), hm _ (hs 2 (by omega)),
    hm _ (hs 3 (by omega)), hm _ (hs 4 (by omega)), hm _ (hs 5 (by omega)),
    hm _ (hs 6 (by omega)), hm _ (hs 7 (by omega)), hm _ (hs 8 (by omega)),
    hm _ (hs 9 (by omega)), hm _ (hs 10 (by omega)), hm _ (hs 11 (by omega)),
    hm _ (hs 12 (by omega)), hm _ (hs 13 (by omega)), hm _ (hs 14 (by omega)),
    hm _ (hs 15 (by omega))]

/-- RFC 7693's compression, as `rounds` between its setup and its finalization. -/
theorem compress_eq (h : Array UInt64) (block : List ℕ) (t : ℕ) (last : Bool) :
    Blake2b.compress h block t last =
      let v := h ++ Blake2b.iv
      let v := v.set! 12 (v[12]! ^^^ UInt64.ofNat t)
      let v := v.set! 13 (v[13]! ^^^ UInt64.ofNat (t / 2 ^ 64))
      let v := if last then v.set! 14 (~~~v[14]!) else v
      let v := rounds v (Blake2b.word block)
      (List.range 8).toArray.map fun i => h[i]! ^^^ v[i]! ^^^ v[i + 8]! := by
  have hm : ∀ i < 16, ((List.range 16).toArray.map (Blake2b.word block))[i]! =
      Blake2b.word block i := fun i hi => getElem!_words _ hi
  cases last <;>
  · simp only [Blake2b.compress, Bool.false_eq_true, ↓reduceIte]
    rw [← rounds_eq _ _ _ hm]
    rfl

/-- `rounds` reads the message only at words `0 .. 15`. -/
theorem rounds_congr (v : Array UInt64) {w₁ w₂ : ℕ → UInt64} (h : ∀ i < 16, w₁ i = w₂ i) :
    rounds v w₁ = rounds v w₂ := by
  simp only [rounds, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl]
  apply List.foldl_ext
  intro v r hr
  simp only [List.mem_range'_1] at hr
  have hs := sigma_lt r (by omega)
  rw [SIGMA_eq r (by omega)]
  simp only [h _ (hs 0 (by omega)), h _ (hs 1 (by omega)), h _ (hs 2 (by omega)),
    h _ (hs 3 (by omega)), h _ (hs 4 (by omega)), h _ (hs 5 (by omega)),
    h _ (hs 6 (by omega)), h _ (hs 7 (by omega)), h _ (hs 8 (by omega)),
    h _ (hs 9 (by omega)), h _ (hs 10 (by omega)), h _ (hs 11 (by omega)),
    h _ (hs 12 (by omega)), h _ (hs 13 (by omega)), h _ (hs 14 (by omega)),
    h _ (hs 15 (by omega))]

theorem set!_getElem!_self (v : Array UInt64) (i : ℕ) : v.set! i v[i]! = v := by
  rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds_def]
  split_ifs with hi
  · simp [getElem!_pos v i hi]
  · rfl

/-- `u64::from_le_bytes` of a block's bytes `8i .. 8i + 8` is RFC 7693's word `i`. -/
theorem u64FromLeBytes_eq_word (bytes : List ℕ) (i : ℕ) :
    u64FromLeBytes ((bytes.drop (8 * i)).take 8) = Blake2b.word bytes i := by
  simp only [u64FromLeBytes, Blake2b.word]
  apply List.foldr_ext
  intro j hj w
  simp only [List.mem_range] at hj
  simp [List.getD_eq_getElem?_getD, hj]

/-- Updating entries `a .. a + n` in turn, each from its own old value. -/
theorem foldl_set!_xor (c : ℕ → UInt64) (n : ℕ) :
    ∀ (a : ℕ) (h : Array UInt64) (j : ℕ),
      ((List.range' a n).foldl (fun h i => h.set! i (h[i]! ^^^ c i)) h)[j]? =
        if a ≤ j ∧ j < a + n then h[j]?.map (· ^^^ c j) else h[j]? := by
  induction n with
  | zero =>
    intro a h j
    simp only [List.range'_zero, List.foldl_nil]
    split_ifs <;> first | rfl | omega
  | succ n ih =>
    intro a h j
    simp only [List.range'_succ, List.foldl_cons]
    rw [ih (a + 1), Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases haj : a = j
    · subst haj
      by_cases ha : a < h.size <;> simp [ha, getElem!_pos, getElem?_pos]
    · simp only [haj, ↓reduceIte]
      split_ifs <;> first | rfl | omega

/-- The finalization loop of `compress_prefix_block` over an 8-word state. -/
theorem forIn_finalize (h v : Array UInt64) (hh : h.size = 8) :
    (Id.run do
      let mut h := h
      for i in [0:8] do
        h := h.set! i (h[i]! ^^^ (v[i]! ^^^ v[i + 8]!))
      return h) = (List.range 8).toArray.map fun i => h[i]! ^^^ v[i]! ^^^ v[i + 8]! := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, pure_bind, Id.run_pure, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one]
  apply Array.ext_getElem?
  intro j
  rw [foldl_set!_xor (fun i => v[i]! ^^^ v[i + 8]!) 8 0 h j]
  by_cases hj : j < 8
  · simp [hj, hh, getElem?_pos, getElem!_pos, UInt64.xor_assoc]
  · simp [hj, hh]

/-! ## Little-endian words -/

/-- The number bytes denote, least significant first. -/
def leValue (l : List ℕ) : ℕ := l.foldr (fun c a => 256 * a + c) 0

theorem leValue_append (l₁ l₂ : List ℕ) :
    leValue (l₁ ++ l₂) = leValue l₁ + 256 ^ l₁.length * leValue l₂ := by
  induction l₁ with
  | nil => simp [leValue]
  | cons c l ih =>
    simp only [leValue, List.cons_append, List.foldr_cons, List.length_cons] at ih ⊢
    rw [ih, pow_succ]; ring

theorem leValue_lt (l : List ℕ) (hl : ∀ x ∈ l, x < 256) : leValue l < 256 ^ l.length := by
  induction l with
  | nil => simp [leValue]
  | cons c l ih =>
    simp only [leValue, List.foldr_cons, List.length_cons] at ih ⊢
    have := ih fun x hx => hl x (by simp [hx])
    have hc := hl c (by simp)
    rw [pow_succ]
    nlinarith

/-- Shifting a word left by a byte and putting a byte below: its value, while it fits. -/
theorem toNat_foldr_shift (l : List ℕ) (hl : ∀ x ∈ l, x < 256) (hlen : l.length ≤ 8) :
    (l.foldr (fun c (w : UInt64) => (w <<< 8) ||| UInt64.ofNat c) 0).toNat = leValue l := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    simp only [List.length_cons] at hlen
    simp only [List.foldr_cons]
    have hc := hl c (by simp)
    have hv := leValue_lt l fun x hx => hl x (by simp [hx])
    rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, ih (fun x hx => hl x (by simp [hx])) (by omega),
      UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]
    have h56 : 256 ^ l.length ≤ 256 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hfit : leValue l <<< 8 < 2 ^ 64 := by
      rw [Nat.shiftLeft_eq]; norm_num at h56 ⊢; omega
    simp only [show (8 : UInt64).toNat % 64 = 8 from rfl, Nat.mod_eq_of_lt hfit]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by norm_num; omega), Nat.shiftLeft_eq]
    simp only [leValue, List.foldr_cons]
    ring

/-- RFC 7693's word `i`: the little-endian value of bytes `8i .. 8i + 8`. -/
theorem toNat_word (bytes : List ℕ) (hb : ∀ x ∈ bytes, x < 256) (i : ℕ) :
    (Blake2b.word bytes i).toNat =
      leValue ((List.range 8).map fun j => bytes.getD (8 * i + j) 0) := by
  rw [Blake2b.word, ← List.foldr_map (g := fun c (w : UInt64) => (w <<< 8) ||| UInt64.ofNat c),
    toNat_foldr_shift _ _ (by simp)]
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
  rw [List.getD_eq_getElem?_getD]
  rcases h : bytes[8 * i + j]? with _ | y
  · simp
  · exact hb y (List.mem_of_getElem? h)

/-- `u32::to_le_bytes`, read back. -/
theorem leValue_u32ToLeBytes (x : ℕ) : leValue (u32ToLeBytes x) = x % 2 ^ 32 := by
  simp only [leValue, u32ToLeBytes, List.foldr_cons, List.foldr_nil]
  omega

/-- RFC 7693's initial state: the IV with the parameter block, for an `outLen`-byte digest and
    a 16-byte personalization. -/
def initState (outLen : ℕ) (personal : List ℕ) : Array UInt64 :=
  let h := Blake2b.iv
  let h := h.set! 0 (h[0]! ^^^ 0x01010000 ^^^ UInt64.ofNat outLen)
  let h := h.set! 6 (h[6]! ^^^ Blake2b.word personal 0)
  h.set! 7 (h[7]! ^^^ Blake2b.word personal 1)

theorem size_compress (h : Array UInt64) (block : List ℕ) (t : ℕ) (last : Bool) :
    (Blake2b.compress h block t last).size = 8 := by
  rw [compress_eq]; simp

/-- The first `n` of 64 bytes, as `List.ofFn`. -/
theorem take_map_range (f : ℕ → ℕ) (n : ℕ) (hn : n ≤ 64) :
    ((List.range 64).map f).take n = List.ofFn fun i : Fin n => f i := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp

end Equihash.Verifier
