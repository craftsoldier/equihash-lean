/-
The portable leaf hasher computes BLAKE2b: each leaf digest of `LeafHasher` is the BLAKE2b of
`input ‖ nonce` followed by the block index, as `Verifier/Blake2b.lean` computes it.
-/
module

public import Equihash.Verifier.LeafHash
public import Equihash.Proofs.Decode
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace Equihash.Verifier

open Equihash Equihash.Spec LeafHash

/-! ## The compression function -/

theorem g_eq_mix : LeafHash.g = Blake2b.mix := rfl

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

end Equihash.Verifier

namespace Equihash.Verifier

open Equihash Equihash.Spec LeafHash

/-- **`compress_prefix_block`** is RFC 7693's compression of a non-final block. -/
theorem compressPrefixBlock_eq (h : Array UInt64) (hh : h.size = 8) (block : List ℕ) :
    compressPrefixBlock h block (UInt64.ofNat 128) = Blake2b.compress h block 128 false := by
  rw [compress_eq]
  simp only [compressPrefixBlock, Bool.false_eq_true, ↓reduceIte,
    show UInt64.ofNat (128 / 2 ^ 64) = 0 from rfl, UInt64.xor_zero, set!_getElem!_self, IV_eq]
  rw [rounds_congr _ (w₂ := Blake2b.word block) fun i hi => by
    rw [getElem!_words _ hi, u64FromLeBytes_eq_word]]
  generalize rounds _ _ = v
  exact forIn_finalize h v hh

/-! ## The final block -/

/-- `v[i] = h[i]; v[8 + i] = IV[i]` for `i` in `a .. a + n`. -/
theorem foldl_init (h : Array UInt64) (n : ℕ) :
    ∀ a (v : Array UInt64), a + n ≤ 8 → v.size = 16 → ∀ j,
      ((List.range' a n).foldl (fun v i => (v.set! i h[i]!).set! (8 + i) IV[i]!) v)[j]? =
        if a ≤ j ∧ j < a + n then some h[j]!
        else if a + 8 ≤ j ∧ j < a + n + 8 then some IV[j - 8]! else v[j]? := by
  induction n with
  | zero =>
    intro a v _ _ j
    simp only [List.range'_zero, List.foldl_nil]
    split_ifs <;> first | rfl | omega
  | succ n ih =>
    intro a v hn hv j
    simp only [List.range'_succ, List.foldl_cons]
    rw [ih (a + 1) _ (by omega) (by simp [hv])]
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, Array.size_setIfInBounds,
      hv]
    split_ifs <;> first | rfl | omega | (subst_vars; simp_all)

/-- `digest[8i .. 8i + 8] = W(i).to_le_bytes()` for `i` in `a .. a + n`. -/
theorem foldl_digest (W : ℕ → UInt64) (n : ℕ) :
    ∀ a (d : List ℕ), a + n ≤ 8 → d.length = 64 →
      ((List.range' a n).foldl
          (fun d i => d.take (8 * i) ++ u64ToLeBytes (W i) ++ d.drop (8 * i + 8)) d).length = 64 ∧
      ∀ q, ((List.range' a n).foldl
          (fun d i => d.take (8 * i) ++ u64ToLeBytes (W i) ++ d.drop (8 * i + 8)) d)[q]? =
        if 8 * a ≤ q ∧ q < 8 * (a + n) then
          some ((W (q / 8) >>> UInt64.ofNat (8 * (q % 8))).toNat % 256)
        else d[q]? := by
  have hl : ∀ x, (u64ToLeBytes x).length = 8 := fun x => by simp [u64ToLeBytes]
  induction n with
  | zero =>
    intro a d _ hd
    refine ⟨hd, fun q => ?_⟩
    simp only [List.range'_zero, List.foldl_nil]
    split_ifs <;> first | rfl | omega
  | succ n ih =>
    intro a d hn hd
    simp only [List.range'_succ, List.foldl_cons]
    have hd' : (d.take (8 * a) ++ u64ToLeBytes (W a) ++ d.drop (8 * a + 8)).length = 64 := by
      simp [hl, hd]; omega
    obtain ⟨hlen, hget⟩ := ih (a + 1) _ (by omega) hd'
    refine ⟨hlen, fun q => ?_⟩
    rw [hget q]
    by_cases h1 : 8 * (a + 1) ≤ q ∧ q < 8 * (a + 1 + n)
    · have h1' : 8 * a ≤ q ∧ q < 8 * (a + (n + 1)) := ⟨by omega, by omega⟩
      simp only [h1, h1', and_self, ↓reduceIte]
    · simp only [h1, ↓reduceIte]
      simp only [List.append_assoc, List.getElem?_append, List.length_take, hd, hl,
        List.getElem?_take, List.getElem?_drop]
      by_cases h2 : q < 8 * a
      · simp [h2, show q < min (8 * a) 64 by omega, show ¬ (8 * a ≤ q ∧ q < 8 * (a + (n + 1)))
          by omega]
      · by_cases h3 : q < 8 * a + 8
        · have hq8 : q / 8 = a := by omega
          simp [show ¬ q < min (8 * a) 64 by omega, show q % 8 < 8 by omega,
            show 8 * a ≤ q ∧ q < 8 * (a + (n + 1)) by omega, u64ToLeBytes, hq8,
            show q - min (8 * a) 64 = q % 8 by omega]
        · simp [show ¬ q < min (8 * a) 64 by omega, show ¬ q - min (8 * a) 64 < 8 by omega,
            show ¬ (8 * a ≤ q ∧ q < 8 * (a + (n + 1))) by omega,
            show 8 * a + 8 + (q - min (8 * a) 64 - 8) = q by omega]

/-- **`Midstate::compress`**, one lane: the digest of block index `b` is RFC 7693's final
    compression of the prefix's last 12 bytes followed by `b`, written out little-endian. -/
theorem Midstate.compress_eq_blake2b (self : Midstate) (hh : self.h.size = 8) (tail : List ℕ)
    (htl : tail.length = 12) (ht : ∀ x ∈ tail, x < 256)
    (hm0 : self.m0 = u64FromLeBytes (tail.take 8))
    (hm1 : self.m1Low = UInt64.ofNat (u32FromLeBytes ((tail.drop 8).take 4)))
    (hc : self.count = UInt64.ofNat 144) (b : ℕ) (digest : List ℕ) (hd : digest.length = 64) :
    self.compress b digest = (List.range 64).map fun q =>
      ((Blake2b.compress self.h (tail ++ u32ToLeBytes b) 144 true)[q / 8]! >>>
        UInt64.ofNat (8 * (q % 8))).toNat % 256 := by
  rw [compress_eq]
  simp only [Midstate.compress, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, pure_bind, Id.run_pure, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one, ↓reduceIte]
  -- The working vector: `h`, then the IV with the byte count and the final-block flag.
  have hinit := foldl_init self.h 8 0 (Array.replicate 16 0) (by omega) (by simp)
  have hsize : ((List.range' 0 8).foldl (fun v i => (v.set! i self.h[i]!).set! (8 + i) IV[i]!)
      (Array.replicate 16 0)).size = 16 := by
    simp only [List.range', List.foldl, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds,
      Array.size_replicate]
  have hsetup : (((List.range' 0 8).foldl (fun v i => (v.set! i self.h[i]!).set! (8 + i) IV[i]!)
      (Array.replicate 16 0)).set! 12 (IV[4]! ^^^ self.count)).set! 14 (~~~IV[6]!) =
      (((self.h ++ Blake2b.iv).set! 12 ((self.h ++ Blake2b.iv)[12]! ^^^ UInt64.ofNat 144)).set!
        13 (((self.h ++ Blake2b.iv).set! 12
          ((self.h ++ Blake2b.iv)[12]! ^^^ UInt64.ofNat 144))[13]! ^^^
            UInt64.ofNat (144 / 2 ^ 64))).set!
        14 (~~~(((self.h ++ Blake2b.iv).set! 12
          ((self.h ++ Blake2b.iv)[12]! ^^^ UInt64.ofNat 144)).set! 13
          (((self.h ++ Blake2b.iv).set! 12
            ((self.h ++ Blake2b.iv)[12]! ^^^ UInt64.ofNat 144))[13]! ^^^
              UInt64.ofNat (144 / 2 ^ 64)))[14]!) := by
    generalize (List.range' 0 8).foldl (fun v i => (v.set! i self.h[i]!).set! (8 + i) IV[i]!)
      (Array.replicate 16 0) = F at hinit hsize ⊢
    apply Array.ext_getElem?
    intro j
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, Array.size_setIfInBounds,
      hsize, hinit, Array.size_append, hh]
    by_cases hj : j < 16
    · interval_cases j <;> simp [hc, IV_eq, Blake2b.iv, hh, getElem!_pos]
    · have hiv : Blake2b.iv[j - 8]? = none :=
        Array.getElem?_eq_none (by simp only [Blake2b.iv, List.size_toArray]; simp; omega)
      simp [hj, show ¬ j < 8 by omega, Array.getElem?_append, hh, hiv,
        show (14 : ℕ) ≠ j by omega, show (13 : ℕ) ≠ j by omega, show (12 : ℕ) ≠ j by omega]
  rw [hsetup]
  -- The message words: the 12 tail bytes, then `b`, then zeros.
  have hbytes : ∀ x ∈ tail ++ u32ToLeBytes b, x < 256 := fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact ht x hx
    · exact bytes_u32ToLeBytes b x hx
  have hw1 : (List.range 8).map (fun j => (tail ++ u32ToLeBytes b).getD (8 * 1 + j) 0) =
      tail.drop 8 ++ u32ToLeBytes b := by
    apply List.ext_getElem? ; intro j
    by_cases hj : j < 8
    · interval_cases j <;> simp [List.getD_eq_getElem?_getD, List.getElem?_append, htl,
        u32ToLeBytes]
    · simp [hj, List.getElem?_append, htl, u32ToLeBytes]
  rw [rounds_congr _ (w₂ := Blake2b.word (tail ++ u32ToLeBytes b)) fun i hi => ?word]
  case word =>
    match i with
    | 0 =>
      show self.m0 = _
      rw [hm0, ← u64FromLeBytes_eq_word, Nat.mul_zero, List.drop_zero,
        List.take_append_of_le_length (by omega)]
    | 1 =>
      show self.m1Low ||| UInt64.ofNat b <<< 32 = _
      apply UInt64.toNat_inj.mp
      rw [toNat_word _ hbytes, hw1, leValue_append, leValue_u32ToLeBytes, List.length_drop, htl,
        hm1, List.take_of_length_le (by simp [htl]), UInt64.toNat_or, UInt64.toNat_shiftLeft,
        UInt64.toNat_ofNat', UInt64.toNat_ofNat']
      have hX := leValue_lt (tail.drop 8) fun x hx => ht x (List.mem_of_mem_drop hx)
      rw [List.length_drop, htl] at hX
      have hu : u32FromLeBytes (tail.drop 8) = leValue (tail.drop 8) := rfl
      rw [hu, Nat.mod_eq_of_lt (by norm_num at hX ⊢; omega), Nat.or_comm,
        show (b % 2 ^ 64) <<< ((32 : UInt64).toNat % 64) % 2 ^ 64 = (b % 2 ^ 32) <<< 32 by
          simp only [Nat.shiftLeft_eq]; norm_num; omega,
        ← Nat.shiftLeft_add_eq_or_of_lt (by norm_num at hX ⊢; omega), Nat.shiftLeft_eq]
      ring
    | i + 2 =>
      show (0 : UInt64) = _
      apply UInt64.toNat_inj.mp
      rw [toNat_word _ hbytes]
      have hz : (List.range 8).map (fun j => (tail ++ u32ToLeBytes b).getD (8 * (i + 2) + j) 0) =
          List.replicate 8 0 := by
        apply List.ext_getElem? ; intro j
        by_cases hj : j < 8
        · simp only [List.getElem?_replicate, hj, ↓reduceIte]
          simp [hj, List.getD_eq_getElem?_getD, List.getElem?_append, htl, u32ToLeBytes,
            show ¬ 8 * (i + 2) + j < 12 by omega, show ¬ 8 * (i + 2) + j - 12 < 4 by omega]
        · simp [hj]
      rw [hz]
      rfl
  generalize rounds _ _ = v
  -- The digest: the eight state words, little-endian.
  obtain ⟨-, hdig⟩ := foldl_digest (fun i => self.h[i]! ^^^ (v[i]! ^^^ v[i + 8]!)) 8 0 digest
    (by omega) hd
  apply List.ext_getElem?
  intro q
  rw [hdig q]
  by_cases hq : q < 64
  · have hq8 : q / 8 < 8 := by omega
    simp [hq, hq8, UInt64.xor_assoc]
  · simp [hq, List.getElem?_eq_none (by omega : digest.length ≤ q)]

end Equihash.Verifier

namespace Equihash.Verifier

open Equihash Equihash.Spec LeafHash

/-! ## The midstate -/

/-- One pass of `Midstate::new`'s `while` loop (`src/leaf_hash.rs`, lines 204–216): compress a
    full block when more input follows, then copy in what fits. -/
def fillPass (_ : Unit) (s : Array UInt64 × List ℕ × ℕ × UInt64 × List ℕ) :
    Option (ForInStep (Array UInt64 × List ℕ × ℕ × UInt64 × List ℕ)) := do
  let mut h := s.1
  let mut block := s.2.1
  let mut filled := s.2.2.1
  let mut compressed := s.2.2.2.1
  let mut part := s.2.2.2.2
  if !part.isEmpty then
    if filled = BLOCKBYTES then
      compressed := compressed + UInt64.ofNat BLOCKBYTES
      h := compressPrefixBlock h block compressed
      filled := 0
    let take := min part.length (BLOCKBYTES - filled)
    block ← copyFromSlice? block filled (part.take take)
    filled := filled + take
    part := part.drop take
    return .yield (h, block, filled, compressed, part)
  else
    return .done (h, block, filled, compressed, part)

/-- One part (`input`, then `nonce`) of `Midstate::new`'s `for` loop (lines 203–217). -/
def partPass (part : List ℕ) (s : Array UInt64 × List ℕ × ℕ × UInt64) :
    Option (ForInStep (Array UInt64 × List ℕ × ℕ × UInt64)) := do
  let s ← forIn Lean.Loop.mk (s.1, s.2.1, s.2.2.1, s.2.2.2, part) fillPass
  return .yield (s.1, s.2.1, s.2.2.1, s.2.2.2.1)

/-- The parameter block of `Midstate::new` (lines 195–198). -/
def paramBlock (p : Params) : Array UInt64 :=
  let h := IV
  let h := h.set! 0 (h[0]! ^^^ (0x01010000 ||| UInt64.ofNat p.hashOutput))
  let h := h.set! 6 (h[6]! ^^^ u64FromLeBytes BLAKE2B_PERSONALIZATION_PREFIX)
  h.set! 7 (h[7]! ^^^ (UInt64.ofNat p.n ||| UInt64.ofNat p.k <<< 32))

/-- `Midstate::new`, as its loop bodies. -/
theorem Midstate.new?_eq (p : Params) (input nonce : List ℕ) :
    Midstate.new? p input nonce =
      (if input.length + nonce.length ≠ HEADER_BYTES + NONCE_BYTES then some none else do
        let s ← forIn [input, nonce] (paramBlock p, List.replicate BLOCKBYTES 0, 0, 0) partPass
        return some {
          h := s.1
          m0 := u64FromLeBytes (s.2.1.take 8)
          m1Low := UInt64.ofNat (u32FromLeBytes ((s.2.1.drop 8).take 4))
          count := UInt64.ofNat (HEADER_BYTES + NONCE_BYTES + 4) }) := by
  rfl

/-- The midstate after absorbing `P`: while `P` fits in one block it is buffered; after that
    the first block is compressed and the rest buffered. -/
def FillRel (h₀ : Array UInt64) (P : List ℕ) (s : Array UInt64 × List ℕ × ℕ × UInt64) : Prop :=
  s.2.1.length = 128 ∧
  (P.length ≤ 128 → s.1 = h₀ ∧ s.2.2.1 = P.length ∧ s.2.2.2 = 0 ∧ s.2.1.take P.length = P) ∧
  (128 < P.length → s.1 = compressPrefixBlock h₀ (P.take 128) (UInt64.ofNat 128) ∧
    s.2.2.1 = P.length - 128 ∧ s.2.2.2 = UInt64.ofNat 128 ∧
    s.2.1.take (P.length - 128) = P.drop 128)

/-- A pass with a full block: compress it, then copy in what fits. -/
theorem fillPass_full (h : Array UInt64) (block : List ℕ) (compressed : UInt64) (part : List ℕ)
    (hbl : block.length = 128) (hp : part ≠ []) :
    fillPass () (h, block, 128, compressed, part) =
      some (.yield (compressPrefixBlock h block (compressed + UInt64.ofNat 128),
        part.take (min part.length 128) ++ block.drop (min part.length 128),
        min part.length 128, compressed + UInt64.ofNat 128, part.drop (min part.length 128))) := by
  have hne : (!part.isEmpty) = true := by cases part <;> simp_all
  simp only [fillPass, hne, BLOCKBYTES, ↓reduceIte, Nat.sub_zero, copyFromSlice?, Nat.zero_add,
    List.length_take, hbl, Option.pure_def, Option.bind_eq_bind]
  simp [List.take_zero]

/-- A pass with room in the block: copy in what fits. -/
theorem fillPass_room (h : Array UInt64) (block : List ℕ) (filled : ℕ) (compressed : UInt64)
    (part : List ℕ) (hbl : block.length = 128) (hf : filled < 128) (hp : part ≠ []) :
    fillPass () (h, block, filled, compressed, part) =
      some (.yield (h, block.take filled ++ part.take (min part.length (128 - filled)) ++
          block.drop (filled + min part.length (128 - filled)),
        filled + min part.length (128 - filled), compressed,
        part.drop (min part.length (128 - filled)))) := by
  have hne : (!part.isEmpty) = true := by cases part <;> simp_all
  simp only [fillPass, hne, BLOCKBYTES, ↓reduceIte, show filled ≠ 128 by omega, copyFromSlice?,
    List.length_take, hbl, Option.pure_def, Option.bind_eq_bind]
  simp [show filled + min part.length (128 - filled) ≤ 128 by omega]

/-- One pass absorbs at least one more byte of `part`, keeping `FillRel`. -/
theorem fillPass_spec (h₀ : Array UInt64) (P : List ℕ) (s : Array UInt64 × List ℕ × ℕ × UInt64)
    (hs : FillRel h₀ P s) (part : List ℕ) (hp : part ≠ []) (hlen : P.length + part.length ≤ 140) :
    ∃ t s', 1 ≤ t ∧
      fillPass () (s.1, s.2.1, s.2.2.1, s.2.2.2, part) =
        some (.yield (s'.1, s'.2.1, s'.2.2.1, s'.2.2.2, part.drop t)) ∧
      FillRel h₀ (P ++ part.take t) s' := by
  obtain ⟨h, block, filled, compressed⟩ := s
  obtain ⟨hbl, hle, hgt⟩ := hs
  simp only at hbl hle hgt
  have hpl : 1 ≤ part.length := List.length_pos_of_ne_nil hp
  by_cases hP : P.length ≤ 128
  · obtain ⟨hh, hfl, hc, hP'⟩ := hle hP
    subst hfl hc
    by_cases hf : P.length = 128
    · -- A full block, and more input: compress it, then start the next.
      have hblock : block = P := by rw [← hP', hf, List.take_of_length_le (by omega)]
      have ht : min part.length 128 = part.length := by omega
      rw [hf, fillPass_full _ block 0 part hbl hp, ht]
      refine ⟨part.length, (compressPrefixBlock h block (UInt64.ofNat 128),
        part.take part.length ++ block.drop part.length, part.length, UInt64.ofNat 128),
        hpl, rfl, ?_⟩
      simp only [List.take_length]
      refine ⟨by simp [hbl]; omega, fun h' => by simp at h'; omega, fun _ => ?_⟩
      simp only [List.length_append, hf, Nat.add_sub_cancel_left]
      exact ⟨by rw [hh, hblock, List.take_left' hf], trivial, trivial, by
        rw [List.drop_left' hf, List.take_left' rfl]⟩
    · -- Room in the block: copy in what fits; `P` still fits in one block.
      set t := min part.length (128 - P.length) with ht
      rw [fillPass_room h block P.length 0 part hbl (by omega) hp]
      refine ⟨t, (h, block.take P.length ++ part.take t ++ block.drop (P.length + t),
        P.length + t, 0), by omega, rfl, ?_⟩
      have htl : (part.take t).length = t := by simp; omega
      have hxl : (block.take P.length ++ part.take t).length = P.length + t := by
        simp [hbl, htl]; omega
      refine ⟨by simp [hbl, htl]; omega, fun _ => ⟨hh, by simp [htl], rfl, ?_⟩,
        fun h' => by simp [htl] at h'; omega⟩
      rw [List.length_append, htl, List.take_left' hxl, hP']
  · -- After the first block: the rest of `nonce` fits beside the tail.
    have hP2 : 128 < P.length := by omega
    obtain ⟨hh, hfl, hc, hP'⟩ := hgt hP2
    have ht : min part.length (128 - (P.length - 128)) = part.length := by omega
    rw [hfl, fillPass_room _ block (P.length - 128) _ part hbl (by omega) hp, ht]
    refine ⟨part.length, (h, block.take (P.length - 128) ++ part.take part.length ++
      block.drop (P.length - 128 + part.length), P.length - 128 + part.length,
      compressed), hpl, ?eq, ?_⟩
    case eq => rfl
    simp only [List.take_length]
    have hxl : (block.take (P.length - 128) ++ part).length = P.length - 128 + part.length := by
      simp [hbl]; omega
    refine ⟨by simp [hbl]; omega, fun h' => by simp at h'; omega, fun _ => ⟨?_, ?_, hc, ?_⟩⟩
    · rw [hh, List.take_append_of_le_length (by omega)]
    · simp; omega
    · rw [List.length_append, show P.length + part.length - 128 = P.length - 128 + part.length by
        omega, List.take_left' hxl, hP', List.drop_append_of_le_length (by omega)]

/-- **The `while` loop** absorbs all of `part`. -/
theorem forIn_fillPass (h₀ : Array UInt64) (part : List ℕ) :
    ∀ (P : List ℕ) (s : Array UInt64 × List ℕ × ℕ × UInt64), FillRel h₀ P s →
      P.length + part.length ≤ 140 → ∃ s', forIn Lean.Loop.mk (s.1, s.2.1, s.2.2.1, s.2.2.2, part)
        fillPass = some (s'.1, s'.2.1, s'.2.2.1, s'.2.2.2, []) ∧ FillRel h₀ (P ++ part) s' := by
  induction h : part.length using Nat.strong_induction_on generalizing part with
  | _ m ih =>
    intro P s hs hlen
    rcases part with _ | ⟨x, xs⟩
    · refine ⟨s, ?_, by simpa using hs⟩
      rw [loop_unfold]
      simp [fillPass]
    · obtain ⟨t, s', ht, hpass, hs'⟩ := fillPass_spec h₀ P s hs (x :: xs) (by simp)
        (by rw [h]; exact hlen)
      have hlt : ((x :: xs).drop t).length < m := by simp at h ⊢; omega
      obtain ⟨s'', hloop, hs''⟩ := ih _ hlt ((x :: xs).drop t) rfl (P ++ (x :: xs).take t) s' hs'
        (by simp only [List.length_append, List.length_take, List.length_drop] at hlen ⊢; omega)
      refine ⟨s'', ?_, by rwa [List.append_assoc, List.take_append_drop] at hs''⟩
      rw [loop_unfold, hpass]
      simpa using hloop

/-- **`Midstate::new`**: for a 140-byte `input ‖ nonce`, the parameter block with the prefix's
    first 128 bytes compressed into it, and the last 12 bytes kept for the final block. -/
theorem Midstate.new?_spec (p : Params) (input nonce : List ℕ)
    (hlen : input.length + nonce.length = 140) :
    ∃ ms, Midstate.new? p input nonce = some (some ms) ∧
      ms.h = compressPrefixBlock (paramBlock p) ((input ++ nonce).take 128) (UInt64.ofNat 128) ∧
      ms.m0 = u64FromLeBytes ((((input ++ nonce).drop 128)).take 8) ∧
      ms.m1Low = UInt64.ofNat (u32FromLeBytes ((((input ++ nonce).drop 128).drop 8).take 4)) ∧
      ms.count = UInt64.ofNat 144 := by
  have h0 : FillRel (paramBlock p) [] (paramBlock p, List.replicate BLOCKBYTES 0, 0, 0) :=
    ⟨by simp [BLOCKBYTES], fun _ => ⟨rfl, rfl, rfl, rfl⟩, fun h => by simp at h⟩
  obtain ⟨s₁, hl₁, hs₁⟩ := forIn_fillPass (paramBlock p) input [] _ h0 (by simp; omega)
  obtain ⟨s₂, hl₂, hs₂⟩ := forIn_fillPass (paramBlock p) nonce _ s₁ hs₁ (by simp; omega)
  simp only [List.nil_append] at hs₂
  obtain ⟨hbl, -, hgt⟩ := hs₂
  obtain ⟨hh, hf, hc, htail⟩ := hgt (by simp; omega)
  rw [List.length_append, hlen] at htail
  rw [Midstate.new?_eq]
  simp only [HEADER_BYTES, NONCE_BYTES, hlen, ne_eq, not_true_eq_false, ↓reduceIte,
    List.forIn_cons, List.forIn_nil, partPass, Option.bind_eq_bind, Option.pure_def]
  simp only at hl₁
  refine ⟨⟨s₂.1, u64FromLeBytes (s₂.2.1.take 8),
    UInt64.ofNat (u32FromLeBytes ((s₂.2.1.drop 8).take 4)), UInt64.ofNat 144⟩, ?_, hh, ?_, ?_, rfl⟩
  · simp only [hl₁, Option.bind_some, hl₂]
  · rw [← htail, List.take_take]; rfl
  · rw [← htail, List.drop_take]; simp [List.take_take]

/-! ## BLAKE2b of a leaf -/

/-- RFC 7693's initial state: the IV with the parameter block, for an `outLen`-byte digest and
    a 16-byte personalization. -/
def initState (outLen : ℕ) (personal : List ℕ) : Array UInt64 :=
  let h := Blake2b.iv
  let h := h.set! 0 (h[0]! ^^^ 0x01010000 ^^^ UInt64.ofNat outLen)
  let h := h.set! 6 (h[6]! ^^^ Blake2b.word personal 0)
  h.set! 7 (h[7]! ^^^ Blake2b.word personal 1)

/-- The personalization `"ZcashPoW" ‖ n ‖ k`, as `initialise_state` builds it. -/
def personalOf (p : Params) : List ℕ :=
  BLAKE2B_PERSONALIZATION_PREFIX ++ u32ToLeBytes p.n ++ u32ToLeBytes p.k

theorem or_eq_xor_param : ∀ x < 65, (0x01010000 : UInt64) ||| UInt64.ofNat x =
    0x01010000 ^^^ UInt64.ofNat x := by decide

/-- **The parameter block** of `Midstate::new` is RFC 7693's, for `n, k < 2^32` and a digest of
    at most 64 bytes. -/
theorem paramBlock_eq (p : Params) (hn : p.n < 2 ^ 32) (hk : p.k < 2 ^ 32)
    (ho : p.hashOutput < 65) : paramBlock p = initState p.hashOutput (personalOf p) := by
  have hb : ∀ x ∈ personalOf p, x < 256 := fun x hx => by
    simp only [personalOf, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · simp [BLAKE2B_PERSONALIZATION_PREFIX] at hx; omega
    · exact bytes_u32ToLeBytes _ x hx
    · exact bytes_u32ToLeBytes _ x hx
  have h6 : u64FromLeBytes BLAKE2B_PERSONALIZATION_PREFIX = Blake2b.word (personalOf p) 0 := by
    rw [← u64FromLeBytes_eq_word]; rfl
  have h7 : UInt64.ofNat p.n ||| UInt64.ofNat p.k <<< 32 = Blake2b.word (personalOf p) 1 := by
    apply UInt64.toNat_inj.mp
    have hw : (List.range 8).map (fun j => (personalOf p).getD (8 * 1 + j) 0) =
        u32ToLeBytes p.n ++ u32ToLeBytes p.k := by
      apply List.ext_getElem? ; intro j
      by_cases hj : j < 8
      · interval_cases j <;> simp [personalOf, BLAKE2B_PERSONALIZATION_PREFIX, u32ToLeBytes,
          List.getD_eq_getElem?_getD]
      · simp [hj, u32ToLeBytes]
    rw [toNat_word _ hb, hw, leValue_append, leValue_u32ToLeBytes, leValue_u32ToLeBytes,
      UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega : p.n < 2 ^ 64), Nat.mod_eq_of_lt hn, Nat.or_comm,
      show (p.k % 2 ^ 64) <<< ((32 : UInt64).toNat % 64) % 2 ^ 64 = p.k <<< 32 by
        simp only [Nat.shiftLeft_eq]; norm_num; omega,
      ← Nat.shiftLeft_add_eq_or_of_lt hn, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hk]
    simp [u32ToLeBytes]
    ring
  simp only [paramBlock, initState, IV_eq, or_eq_xor_param _ ho, h6, h7, UInt64.xor_assoc]

/-- RFC 7693's BLAKE2b of 144 bytes: two blocks. -/
theorem finalState_144 (outLen : ℕ) (personal input : List ℕ) (hlen : input.length = 144) :
    Blake2b.finalState outLen personal input =
      Blake2b.compress (Blake2b.compress (initState outLen personal) (input.take 128) 128 false)
        (input.drop 128) 144 true := by
  simp only [Blake2b.finalState, hlen, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, List.forIn_pure_yield_eq_foldl, pure_bind, Id.run_pure,
    show max 1 ((144 + 127) / 128) = 2 by norm_num, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    List.range', List.foldl]
  simp [initState, List.take_of_length_le (show (input.drop 128).length ≤ 128 by simp [hlen])]

theorem size_compress (h : Array UInt64) (block : List ℕ) (t : ℕ) (last : Bool) :
    (Blake2b.compress h block t last).size = 8 := by
  rw [compress_eq]; simp

/-- The first `n` of 64 bytes, as `List.ofFn`. -/
theorem take_map_range (f : ℕ → ℕ) (n : ℕ) (hn : n ≤ 64) :
    ((List.range 64).map f).take n = List.ofFn fun i : Fin n => f i := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp

/-- **The leaf hasher computes BLAKE2b.** For a 140-byte `input ‖ nonce` and parameters Zakura
    accepts, `LeafHasher` gives each block index `b` the BLAKE2b digest of `input ‖ nonce`
    followed by `b`, personalized by `"ZcashPoW" ‖ n ‖ k`, zero-padded to 64 bytes. -/
theorem leafHasher_spec {rp : Params} {p : ZakuraParams} (h : rp.Is p) (input nonce : List ℕ)
    (hin : Bytes input) (hnon : Bytes nonce) (hlen : input.length + nonce.length = 140) :
    ∃ lh, LeafHasher.new? rp input nonce = some (some lh) ∧
      ∀ bs ds, ds.length = bs.length → (∀ d ∈ ds, d.length = 64) →
        lh.hash? bs ds = some (bs.map fun b =>
          Blake2b.blake2b rp.hashOutput (personalOf rp) (input ++ nonce ++ u32ToLeBytes b) ++
            List.replicate (64 - rp.hashOutput) 0) := by
  -- The parameters fit the word arithmetic.
  have hn : rp.n < 2 ^ 32 := by have := p.n_le; rw [h.1]; omega
  have hk : rp.k < 2 ^ 32 := by have := p.k_lt; have := p.n_le; rw [h.2]; omega
  have ho : rp.hashOutput ≤ 64 := by
    rw [Params.hashOutput_eq h]; exact genHashParams_len_le p.toParams
  obtain ⟨ms, hms, hmh, hm0, hm1, hc⟩ := Midstate.new?_spec rp input nonce hlen
  refine ⟨⟨ms, rp.hashOutput⟩, by simp [LeafHasher.new?, hms], fun bs ds hl hd => ?_⟩
  -- The prefix: its first block is compressed, its last 12 bytes are the tail.
  set P := input ++ nonce with hP
  have hPl : P.length = 140 := by simp [hP, hlen]
  have hPb : Bytes P := hin.append hnon
  have hpb : (paramBlock rp).size = 8 := by simp [paramBlock, IV]
  have hmh' : ms.h = Blake2b.compress (initState rp.hashOutput (personalOf rp)) (P.take 128) 128
      false := by
    rw [hmh, compressPrefixBlock_eq _ hpb, paramBlock_eq rp hn hk (by omega)]
  have hhs : ms.h.size = 8 := by rw [hmh']; exact size_compress _ _ _ _
  -- Each digest.
  have hdig : ∀ b d, d.length = 64 →
      (ms.compress b d).take rp.hashOutput ++
        List.replicate ((ms.compress b d).length - rp.hashOutput) 0 =
      Blake2b.blake2b rp.hashOutput (personalOf rp) (P ++ u32ToLeBytes b) ++
        List.replicate (64 - rp.hashOutput) 0 := by
    intro b d hd64
    rw [Midstate.compress_eq_blake2b ms hhs (P.drop 128) (by simp [hPl])
      (fun x hx => hPb x (List.mem_of_mem_drop hx)) hm0 hm1 hc b d hd64, take_map_range _ _ ho,
      List.length_map, List.length_range, Blake2b.blake2b,
      finalState_144 rp.hashOutput (personalOf rp) (P ++ u32ToLeBytes b)
        (by simp [hPl, u32ToLeBytes]),
      List.take_append_of_le_length (by omega : 128 ≤ P.length),
      List.drop_append_of_le_length (by omega : 128 ≤ P.length), hmh']
  -- The batch: one lane, so every block is hashed by the portable kernel.
  simp only [LeafHasher.hash?, hl, guard_true, Nat.div_one, Nat.mul_one, List.take_length,
    List.drop_length, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
    Midstate.compressPortable, List.zip_nil_left, List.map_nil, List.append_nil,
    List.take_of_length_le (show ds.length ≤ bs.length by omega)]
  congr 1
  induction bs generalizing ds with
  | nil => cases ds <;> simp
  | cons b bs ih =>
    rcases ds with _ | ⟨d, ds⟩
    · simp at hl
    · simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq]
      exact ⟨hdig b d (hd d (by simp)), ih ds (by simpa using hl)
        (fun d' hd' => hd d' (by simp [hd']))⟩

end Equihash.Verifier
