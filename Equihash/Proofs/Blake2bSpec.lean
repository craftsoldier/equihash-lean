/-
RFC 7693's BLAKE2b, as `Verifier.Blake2b` computes it on 64-bit integers, is §5.4.1.2's
`BLAKE2b-ℓ(p, x)`, as `Spec.Blake2b` defines it on bit vectors.
-/
module

public import Equihash.Proofs.Blake2b
public import Equihash.Spec.Blake2b

@[expose] public section

namespace Equihash.Verifier.Blake2b

open Equihash.Spec.Blake2b (Word)

/-! ## Words -/

/-- An array of 64-bit integers holds the words of `V`. -/
def Holds {n : ℕ} (v : Array UInt64) (V : Vector Word n) : Prop :=
  v.size = n ∧ ∀ i (hi : i < n), v[i]!.toBitVec = V[i]

/-- A byte widened to a word. -/
theorem toBitVec_ofNat_toNat (b : Byte) : (UInt64.ofNat b.toNat).toBitVec = b.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq; simp

/-- RFC 7693's word `i` of bytes is the specification's. -/
theorem toBitVec_word (bs : List Byte) (i : ℕ) :
    (word (bs.map BitVec.toNat) i).toBitVec = Spec.Blake2b.word bs i := by
  simp only [word, Spec.Blake2b.word]
  induction List.range 8 with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldr_cons, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, ih]
    congr 1
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases bs[8 * i + j]? <;> simp [toBitVec_ofNat_toNat]

/-- `rotr` by `0 < n < 64` is rotation right. -/
theorem toBitVec_rotr (x : UInt64) (n : ℕ) (h0 : 0 < n) (h64 : n < 64) :
    (rotr x (UInt64.ofNat n)).toBitVec = x.toBitVec.rotateRight n := by
  rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt h64]
  simp only [rotr, UInt64.toBitVec_or, UInt64.toBitVec_shiftRight, UInt64.toBitVec_shiftLeft,
    BitVec.shiftLeft_eq', BitVec.ushiftRight_eq']
  have h1 : ((UInt64.ofNat n).toBitVec % 64).toNat = n := by simp; omega
  have h2 : ((64 - UInt64.ofNat n).toBitVec % 64).toNat = 64 - n := by
    simp [UInt64.toBitVec_sub]; omega
  rw [h1, h2]

/-- The four rotations of `G`. -/
theorem rot32 (x : UInt64) : (rotateRight x 32).toBitVec = x.toBitVec.rotateRight 32 :=
  toBitVec_rotr x 32 (by decide) (by decide)
theorem rot24 (x : UInt64) : (rotateRight x 24).toBitVec = x.toBitVec.rotateRight 24 :=
  toBitVec_rotr x 24 (by decide) (by decide)
theorem rot16 (x : UInt64) : (rotateRight x 16).toBitVec = x.toBitVec.rotateRight 16 :=
  toBitVec_rotr x 16 (by decide) (by decide)
theorem rot63 (x : UInt64) : (rotateRight x 63).toBitVec = x.toBitVec.rotateRight 63 :=
  toBitVec_rotr x 63 (by decide) (by decide)

/-! ## `G` -/

/-- RFC 7693's `G` on four words, with message words `x` and `y`. -/
def G4 (x y : UInt64) (s : UInt64 × UInt64 × UInt64 × UInt64) :
    UInt64 × UInt64 × UInt64 × UInt64 :=
  let (a, b, c, d) := s
  let a := a + b + x
  let d := rotateRight (d ^^^ a) 32
  let c := c + d
  let b := rotateRight (b ^^^ c) 24
  let a := a + b + y
  let d := rotateRight (d ^^^ a) 16
  let c := c + d
  let b := rotateRight (b ^^^ c) 63
  (a, b, c, d)

/-- Four entries of `v` set to the four words of `s`. -/
def set4 (v : Array UInt64) (a b c d : ℕ) (s : UInt64 × UInt64 × UInt64 × UInt64) :
    Array UInt64 :=
  (((v.set! a s.1).set! b s.2.1).set! c s.2.2.1).set! d s.2.2.2

/-- `mix` is `G` on four distinct words of the state. -/
theorem mix_eq_set4 (v : Array UInt64) {a b c d : ℕ} (ha : a < v.size) (hb : b < v.size)
    (hc : c < v.size) (hd : d < v.size) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (x y : UInt64) :
    mix v a b c d x y = set4 v a b c d (G4 x y (v[a]!, v[b]!, v[c]!, v[d]!)) := by
  simp only [mix, rotr, set4, G4, rotateRight, Array.set!_eq_setIfInBounds, getElem!_pos,
    Array.size_setIfInBounds,
    ha, hb, hc, hd, Array.getElem_setIfInBounds, hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm,
    had.symm, hbc.symm, hbd.symm, hcd.symm, ↓reduceIte]
  apply Array.ext_getElem?
  intro i
  simp only [Array.getElem?_setIfInBounds]
  have := hab.symm; have := hac.symm; have := had.symm; have := hbc.symm; have := hbd.symm
  have := hcd.symm
  by_cases hia : i = a
  · simp [*]
  by_cases hib : i = b
  · simp [*]
  by_cases hic : i = c
  · simp [*]
  by_cases hid : i = d
  · simp [*]
  simp [Ne.symm hia, Ne.symm hib, Ne.symm hic, Ne.symm hid]

/-- Entry `i` of the specification's `G`. -/
theorem G_getElem (V : Vector Word 16) (a b c d : Fin 16) (x y : Word) (i : ℕ) (hi : i < 16) :
    (Spec.Blake2b.G V a b c d x y)[i] =
      let va := V[a] + V[b] + x
      let vd := (V[d] ^^^ va).rotateRight 32
      let vc := V[c] + vd
      let vb := (V[b] ^^^ vc).rotateRight 24
      let va := va + vb + y
      let vd := (vd ^^^ va).rotateRight 16
      let vc := vc + vd
      let vb := (vb ^^^ vc).rotateRight 63
      if d.val = i then vd else if c.val = i then vc else if b.val = i then vb
      else if a.val = i then va else V[i] := by
  simp only [Spec.Blake2b.G, Vector.getElem_set]

/-- `mix` on distinct positions is the specification's `G`. -/
theorem holds_mix {v : Array UInt64} {V : Vector Word 16} (h : Holds v V) (a b c d : Fin 16)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val) (hbc : b.val ≠ c.val)
    (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) (x y : UInt64) :
    Holds (mix v a b c d x y) (Spec.Blake2b.G V a b c d x.toBitVec y.toBitVec) := by
  obtain ⟨hs, hv⟩ := h
  have e : mix v a b c d x y =
      set4 v a b c d (G4 x y (v[a.val]!, v[b.val]!, v[c.val]!, v[d.val]!)) :=
    mix_eq_set4 v (by omega) (by omega) (by omega) (by omega) hab hac had hbc hbd hcd x y
  have ha := hv a a.isLt; have hb := hv b b.isLt; have hc := hv c c.isLt; have hd := hv d d.isLt
  generalize v[a.val]! = A at ha e
  generalize v[b.val]! = B at hb e
  generalize v[c.val]! = C at hc e
  generalize v[d.val]! = D at hd e
  rw [e]
  refine ⟨by simp [set4, hs], fun i hi => ?_⟩
  have hvi := hv i hi
  rw [G_getElem _ _ _ _ _ _ _ i hi]
  simp only [set4, G4, Array.set!_eq_setIfInBounds]
  rw [getElem!_pos _ _ (by simp [hs, hi])]
  have := Ne.symm hab; have := Ne.symm hac; have := Ne.symm had; have := Ne.symm hbc
  have := Ne.symm hbd; have := Ne.symm hcd
  simp only [Fin.getElem_fin, ← ha, ← hb, ← hc, ← hd]
  by_cases hid : d.val = i
  · subst hid; simp [*, rot32, rot24, rot16]
  by_cases hic : c.val = i
  · subst hic; simp [*, rot32, rot24, rot16]
  by_cases hib : b.val = i
  · subst hib; simp [*, rot32, rot24, rot16, rot63]
  by_cases hia : a.val = i
  · subst hia; simp [*, rot32, rot24]
  rw [getElem!_pos v i (by omega)] at hvi
  simp [*]

/-! ## Rounds -/

/-- `SIGMA`'s row `r` is the specification's `σ_{r mod 10}`. -/
theorem SIGMA_getElem (r : ℕ) (hr : r < 12) (j : ℕ) (hj : j < 16) :
    (LeafHash.SIGMA[r]!)[j]! =
      ((Spec.Blake2b.sigma[r % 10]'(Nat.mod_lt _ (by decide)))[j]'hj).val := by
  interval_cases r <;> interval_cases j <;> rfl

/-- The twelve rounds agree, on message words that agree. -/
theorem holds_rounds {v : Array UInt64} {V : Vector Word 16} (h : Holds v V) (w : ℕ → UInt64)
    (M : Vector Word 16) (hm : ∀ j (hj : j < 16), (w j).toBitVec = M[j]) :
    Holds (LeafHash.rounds v w)
      ((List.range 12).foldl (fun V r => Spec.Blake2b.round M r V) V) := by
  simp only [LeafHash.rounds, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, ← List.range_eq_range']
  have hl : ∀ r ∈ List.range 12, r < 12 := fun r hr => List.mem_range.mp hr
  generalize List.range 12 = L at hl ⊢
  induction L generalizing v V with
  | nil => exact h
  | cons r L ih =>
    simp only [List.foldl_cons]
    apply ih _ fun r' hr' => hl r' (List.mem_cons_of_mem _ hr')
    have hr := hl r List.mem_cons_self
    have e : ∀ j (hj : j < 16), (w (LeafHash.SIGMA[r]![j]!)).toBitVec =
        M[(Spec.Blake2b.sigma[r % 10]'(Nat.mod_lt _ (by decide)))[j]'hj] := fun j hj => by
      rw [SIGMA_getElem r hr j hj, hm _ (Fin.isLt _), Fin.getElem_fin]
    simp only [Spec.Blake2b.round, g_eq_mix]
    rw [← e 0 (by decide), ← e 1 (by decide), ← e 2 (by decide), ← e 3 (by decide),
      ← e 4 (by decide), ← e 5 (by decide), ← e 6 (by decide), ← e 7 (by decide),
      ← e 8 (by decide), ← e 9 (by decide), ← e 10 (by decide), ← e 11 (by decide),
      ← e 12 (by decide), ← e 13 (by decide), ← e 14 (by decide), ← e 15 (by decide)]
    have m := fun {v V} (h : Holds v V) (a b c d : Fin 16)
        (hd : [a.val, b.val, c.val, d.val].Nodup) =>
      holds_mix h a b c d (by simp_all) (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all)
    exact m (m (m (m (m (m (m (m h 0 4 8 12 (by decide) _ _) 1 5 9 13 (by decide) _ _)
      2 6 10 14 (by decide) _ _) 3 7 11 15 (by decide) _ _) 0 5 10 15 (by decide) _ _)
      1 6 11 12 (by decide) _ _) 2 7 8 13 (by decide) _ _) 3 4 9 14 (by decide) _ _

/-! ## Compression -/

/-- RFC 7693's `IV` is the specification's. -/
theorem iv_getElem (k : ℕ) (hk : k < 8) : iv[k]!.toBitVec = Spec.Blake2b.iv[k] := by
  interval_cases k <;> rfl

/-- RFC 7693's compression is the specification's. -/
theorem holds_compress {h : Array UInt64} {H : Vector Word 8} (hh : Holds h H) (block : List ℕ)
    (M : Vector Word 16) (hm : ∀ j (hj : j < 16), (word block j).toBitVec = M[j]) (t : ℕ)
    (last : Bool) : Holds (compress h block t last) (Spec.Blake2b.compress H M t last) := by
  obtain ⟨hs, hv⟩ := hh
  rw [compress_eq]
  simp only [Spec.Blake2b.compress]
  have hinit : Holds (n := 8 + 8)
      (let v := h ++ iv
       let v := v.set! 12 (v[12]! ^^^ UInt64.ofNat t)
       let v := v.set! 13 (v[13]! ^^^ UInt64.ofNat (t / 2 ^ 64))
       if last then v.set! 14 (~~~v[14]!) else v)
      (H ++ #v[Spec.Blake2b.iv[0], Spec.Blake2b.iv[1], Spec.Blake2b.iv[2], Spec.Blake2b.iv[3],
        BitVec.ofNat 64 t ^^^ Spec.Blake2b.iv[4],
        BitVec.ofNat 64 (t / 2 ^ 64) ^^^ Spec.Blake2b.iv[5],
        (if last then BitVec.allOnes 64 else 0) ^^^ Spec.Blake2b.iv[6], Spec.Blake2b.iv[7]]) := by
    refine ⟨by cases last <;> simp [hs, iv], fun i hi => ?_⟩
    have hv' : ∀ i (hi : i < 8), (h[i]'(by omega)).toBitVec = H[i] := fun i hi => by
      rw [← hv i hi, getElem!_pos]
    rw [Vector.getElem_append]
    interval_cases i <;> cases last <;>
      simp [Array.set!_eq_setIfInBounds, getElem!_pos, hs, hv', iv, Spec.Blake2b.iv,
        UInt64.toBitVec_ofNat', BitVec.xor_comm]
  obtain ⟨hrs, hrv⟩ := holds_rounds hinit (word block) M hm
  generalize LeafHash.rounds _ (word block) = r at hrs hrv
  generalize (List.range 12).foldl (fun V r => Spec.Blake2b.round M r V) _ = R at hrv
  refine ⟨by simp, fun i hi => ?_⟩
  rw [getElem!_pos _ _ (by simp [hi])]
  simp only [Array.getElem_map, List.getElem_toArray, List.getElem_range, UInt64.toBitVec_xor,
    Vector.getElem_ofFn]
  rw [hv i hi, hrv i (by omega), hrv (i + 8) (by omega)]
  rfl

/-! ## The parameter block -/

/-- A word inside `l` is a word of `l`. -/
theorem word_append_left (l q : List Byte) (i : ℕ) (h : 8 * i + 8 ≤ l.length) :
    Spec.Blake2b.word (l ++ q) i = Spec.Blake2b.word l i := by
  simp only [Spec.Blake2b.word]
  apply List.foldr_ext
  intro j hj w
  simp only [List.mem_range] at hj
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by omega)]

/-- A word after `l`, of `8k` bytes, is a word of what follows it. -/
theorem word_append_right (l q : List Byte) (k : ℕ) (hl : l.length = 8 * k) (i : ℕ) :
    Spec.Blake2b.word (l ++ q) (k + i) = Spec.Blake2b.word q i := by
  simp only [Spec.Blake2b.word]
  apply List.foldr_ext
  intro j hj w
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega), hl, show 8 * (k + i) + j - 8 * k = 8 * i + j by omega]

/-- Word 0 of the parameter block: digest length, key length 0, fanout 1, depth 1. -/
theorem word_paramBlock_zero (len : ℕ) (hlen : len ≤ 64) (p : List.Vector Byte 16) :
    Spec.Blake2b.word (Spec.Blake2b.paramBlock len p) 0 =
      ((0x01010000 : UInt64) ^^^ UInt64.ofNat len).toBitVec := by
  rw [Spec.Blake2b.paramBlock, word_append_left _ _ _ (by simp)]
  interval_cases len <;> decide +kernel

/-- Words 1 to 5 of the parameter block are zero. -/
theorem word_paramBlock_mid (len : ℕ) (p : List.Vector Byte 16) (k : ℕ) (hk : k < 5) :
    Spec.Blake2b.word (Spec.Blake2b.paramBlock len p) (1 + k) = 0 := by
  rw [Spec.Blake2b.paramBlock, show List.replicate 44 (0 : Byte) =
    List.replicate 4 0 ++ List.replicate 40 0 by rw [List.replicate_append_replicate],
    ← List.append_assoc, word_append_left _ _ _ (by simp; omega),
    word_append_right _ _ 1 (by simp)]
  interval_cases k <;> decide +kernel

/-- Words 6 and 7 of the parameter block are the personalization. -/
theorem word_paramBlock_personal (len : ℕ) (p : List.Vector Byte 16) (k : ℕ) :
    Spec.Blake2b.word (Spec.Blake2b.paramBlock len p) (6 + k) = Spec.Blake2b.word p.toList k :=
  word_append_right _ _ 6 (by simp) k

/-- RFC 7693's initial state is `IV ⊕ P`. -/
theorem holds_initState (len : ℕ) (hlen : len ≤ 64) (p : List.Vector Byte 16) :
    Holds (initState len (p.toList.map BitVec.toNat)) (Vector.ofFn fun i : Fin 8 =>
      Spec.Blake2b.iv[i] ^^^ Spec.Blake2b.word (Spec.Blake2b.paramBlock len p) i) := by
  have hmid : ∀ k, 1 ≤ k → k ≤ 5 → Spec.Blake2b.word (Spec.Blake2b.paramBlock len p) k = 0 :=
    fun k h1 h5 => by
      have := word_paramBlock_mid len p (k - 1) (by omega)
      rwa [show 1 + (k - 1) = k by omega] at this
  have h6 := word_paramBlock_personal len p 0
  have h7 := word_paramBlock_personal len p 1
  have hw0 := toBitVec_word p.toList 0
  have hw1 := toBitVec_word p.toList 1
  have hz := word_paramBlock_zero len hlen p
  refine ⟨by simp [initState, iv], fun i hi => ?_⟩
  interval_cases i <;>
    simp [initState, Array.set!_eq_setIfInBounds, getElem!_pos, iv, Spec.Blake2b.iv, hmid, h6, h7,
      hw0, hw1, hz, ← BitVec.xor_assoc]

/-! ## The final state -/

/-- The counter: the data bytes in blocks `0 … i`. -/
theorem counter_eq (len i n : ℕ) (hn : n = max 1 ((len + 127) / 128)) (hi : i < n) :
    (if (i + 1 == n) = true then len else 128 * (i + 1)) = min (128 * (i + 1)) len := by
  by_cases h : i + 1 = n
  · simp only [h, beq_self_eq_true, ↓reduceIte]; omega
  · simp only [beq_iff_eq, h, ↓reduceIte]; omega

/-- Compressing blocks in turn agrees, block by block. -/
theorem holds_foldl_blocks (x : List Byte) (L : List ℕ)
    (hL : ∀ i ∈ L, i < max 1 ((x.length + 127) / 128)) {h : Array UInt64} {H : Vector Word 8}
    (hh : Holds h H) :
    Holds (L.foldl (fun b a => compress b ((((x.map BitVec.toNat).drop (128 * a))).take 128)
        (if (a + 1 == max 1 ((x.length + 127) / 128)) = true then x.length else 128 * (a + 1))
        (a + 1 == max 1 ((x.length + 127) / 128))) h)
      (L.foldl (fun h i => Spec.Blake2b.compress h (Spec.Blake2b.block x i)
        (min (128 * (i + 1)) x.length) (i + 1 == max 1 ((x.length + 127) / 128))) H) := by
  induction L generalizing h H with
  | nil => exact hh
  | cons i L ih =>
    simp only [List.foldl_cons]
    apply ih fun j hj => hL j (List.mem_cons_of_mem _ hj)
    rw [counter_eq x.length i _ rfl (hL i List.mem_cons_self)]
    refine holds_compress hh _ _ (fun j hj => ?_) _ _
    rw [← List.map_drop, ← List.map_take, toBitVec_word]
    simp [Spec.Blake2b.block]

/-- RFC 7693's final state is the specification's. -/
theorem holds_finalState (len : ℕ) (hlen : len ≤ 64) (p : List.Vector Byte 16) (x : List Byte) :
    Holds (finalState len (p.toList.map BitVec.toNat) (x.map BitVec.toNat))
      (Spec.Blake2b.finalState len p x) := by
  simp only [finalState, Spec.Blake2b.finalState, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, List.forIn_pure_yield_eq_foldl, ← List.range_eq_range', List.length_map,
    pure_bind, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  exact holds_foldl_blocks x _ (fun i hi => List.mem_range.mp hi) (holds_initState len hlen p)

/-! ## The output -/

/-- Byte `s / 8` of a word, little-endian. -/
theorem byte_eq (u : UInt64) (s : ℕ) (hs : s < 64) :
    BitVec.ofNat 8 ((u >>> UInt64.ofNat s).toNat % 256) = (u.toBitVec >>> s).setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mod_eq_of_lt hs]

/-- **RFC 7693's BLAKE2b, as `Verifier.Blake2b` computes it, is §5.4.1.2's `BLAKE2b-ℓ(p, x)`.** -/
theorem hashFn_eq : hashFn = Spec.Blake2b.hashFn := by
  funext p x
  obtain ⟨hs, hv⟩ := holds_finalState p.len p.len_le p.personal x
  apply Subtype.ext
  simp only [hashFn, Spec.Blake2b.hashFn, Spec.Blake2b.blake2b, blake2b, List.map_ofFn]
  congr 1
  funext k
  simp only [Function.comp_apply]
  have := p.len_le; have := k.isLt
  rw [byte_eq _ _ (by omega), hv _ (by omega)]

end Equihash.Verifier.Blake2b
