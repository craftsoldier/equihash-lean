/-
`blake2b_simd 1.0.4`'s AVX2 `compress_block` is its portable one: the four rows of the state in
four vectors, `g1` then `g2` as `G` on each lane, the diagonals one lane over, and each `b0` the
message words `SIGMA` names. So `State`, on either implementation, computes the specification's
`BLAKE2b-ℓ(p, x)` (`finalize_foldl_update_spec`).
-/
module

public import Equihash.Proofs.Blake2bSimd
public import Equihash.Proofs.Blake2bSpec

@[expose] public section

namespace Equihash.Verifier.Blake2b

open X86_64

/-! ## Words of the vector operations -/

/-- Word `w` of a vector built from words. -/
theorem word_ofWords (f : ℕ → UInt64) {w : ℕ} (hw : w < 4) : (M256i.ofWords f).word w = f w := by
  interval_cases w <;> rfl

/-- A word is its two 32-bit halves. -/
theorem halves (u : UInt64) :
    (u >>> UInt64.ofNat 0 &&& (0xffffffff : UInt64)) |||
      (u >>> UInt64.ofNat 32 &&& (0xffffffff : UInt64)) <<< (32 : UInt64) = u := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hm : ∀ j, Nat.testBit 4294967295 j = decide (j < 32) := fun j => by
    simpa using Nat.testBit_two_pow_sub_one 32 j
  by_cases h : i < 32
  · simp [h, hi, BitVec.getLsbD_ofNat, hm]
  · have hmL : ∀ j, (4294967295#64).getLsbD j = (decide (j < 64) && decide (j < 32)) :=
      fun j => by rw [BitVec.getLsbD_ofNat, hm]
    have e1 : (4294967295#64)[i] = false := by
      rw [← BitVec.getLsbD_eq_getElem, hmL]; simp; omega
    have e2 : (4294967295#64)[i - 32]'(by omega) = true := by
      rw [← BitVec.getLsbD_eq_getElem, hmL]; simp; omega
    simp [h, hi, Nat.add_sub_cancel' (show 32 ≤ i by omega), e1, e2]

/-- `_mm256_blend_epi32` with both bits of a word's two halves the same: that word, from `b` or
    from `a`. -/
theorem word_blend (imm8 : ℕ) (a b : M256i) {w : ℕ} (hw : w < 4)
    (h : (imm8 >>> (2 * w)) % 2 = (imm8 >>> (2 * w + 1)) % 2) :
    (mm256BlendEpi32 imm8 a b).word w =
      if (imm8 >>> (2 * w)) % 2 = 1 then b.word w else a.word w := by
  rw [mm256BlendEpi32, word_ofWords _ hw]
  simp only [← h]
  split_ifs <;>
  · simp only [vecDword, show 2 * w / 2 = w by omega, show (2 * w + 1) / 2 = w by omega,
      show 2 * w % 2 = 0 by omega, show (2 * w + 1) % 2 = 1 by omega, Nat.mul_zero, Nat.mul_one]
    exact halves _

/-- `_mm256_shuffle_epi32(a, _MM_SHUFFLE!(1, 0, 3, 2))`: the two words of each 128-bit lane
    swapped. -/
theorem word_swap (a : M256i) {w : ℕ} (hw : w < 4) :
    (mm256ShuffleEpi32 78 a).word w = a.word (if w % 2 = 0 then w + 1 else w - 1) := by
  rw [mm256ShuffleEpi32, word_ofWords _ hw]
  interval_cases w <;> simp [vecDword] <;> exact halves _

/-- A word is its eight bytes. -/
theorem bytes (u : UInt64) :
    u &&& (255 : UInt64) ||| (u >>> (8 : UInt64) &&& 255) <<< (8 : UInt64) |||
      (u >>> (16 : UInt64) &&& 255) <<< (16 : UInt64) |||
      (u >>> (24 : UInt64) &&& 255) <<< (24 : UInt64) |||
      (u >>> (32 : UInt64) &&& 255) <<< (32 : UInt64) |||
      (u >>> (40 : UInt64) &&& 255) <<< (40 : UInt64) |||
      (u >>> (48 : UInt64) &&& 255) <<< (48 : UInt64) |||
      (u >>> (56 : UInt64) &&& 255) <<< (56 : UInt64) = u := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases i <;> simp

/-- `_mm256_alignr_epi8(a, b, 8)`: in each 128-bit lane, `b`'s high word, then `a`'s low word. -/
theorem word_alignr (a b : M256i) {w : ℕ} (hw : w < 4) :
    (mm256AlignrEpi8 8 a b).word w = if w % 2 = 0 then b.word (w + 1) else a.word (w - 1) := by
  rw [mm256AlignrEpi8, word_ofWords _ hw]
  interval_cases w <;> simp [wordOfBytes, vecByte] <;> exact bytes _

/-! ## `G` on four words -/

/-- `_mm256_add_epi64` adds word by word. -/
theorem word_add (a b : M256i) {w : ℕ} (hw : w < 4) :
    (mm256AddEpi64 a b).word w = a.word w + b.word w := word_ofWords _ hw

/-- `_mm256_xor_si256` xors word by word. -/
theorem word_xor (a b : M256i) {w : ℕ} (hw : w < 4) :
    (mm256XorSi256 a b).word w = a.word w ^^^ b.word w := word_ofWords _ hw

/-- `rot n` rotates each word right by `n`. -/
theorem word_rot (n : ℕ) (hn : 0 < n) (hn' : n < 64) (x : M256i) {w : ℕ} (hw : w < 4) :
    (Avx2.rot n x).word w = rotateRight (x.word w) (UInt64.ofNat n) := by
  simp only [Avx2.rot, mm256OrSi256, mm256SrliEpi64, mm256SlliEpi64, word_ofWords _ hw,
    show ¬n > 63 by omega, show ¬64 - n > 63 by omega, ↓reduceIte, rotateRight]
  congr 2
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_sub, UInt64.toNat_ofNat]
  omega

/-- `(a + m) + b = (a + b) + m`: `g1` adds the message word first, `G` last. -/
theorem add_right_comm' (a m b : UInt64) : a + m + b = a + b + m := by
  rw [UInt64.add_assoc, UInt64.add_comm m, ← UInt64.add_assoc]

/-- **`g1` then `g2` is `G` on each lane**: lane `w` of the rows, with message words lane `w` of
    `m₁` and of `m₂`. -/
theorem g2_g1 (a b c d m₁ m₂ : M256i) {w : ℕ} (hw : w < 4) :
    let s := Avx2.g2 (Avx2.g1 (a, b, c, d) m₁) m₂
    (s.1.word w, s.2.1.word w, s.2.2.1.word w, s.2.2.2.word w) =
      G4 (m₁.word w) (m₂.word w) (a.word w, b.word w, c.word w, d.word w) := by
  simp only [Avx2.g1, Avx2.g2, G4, word_add _ _ hw, word_xor _ _ hw,
    word_rot 32 (by omega) (by omega) _ hw, word_rot 24 (by omega) (by omega) _ hw,
    word_rot 16 (by omega) (by omega) _ hw, word_rot 63 (by omega) (by omega) _ hw,
    show UInt64.ofNat 32 = 32 from rfl, show UInt64.ofNat 24 = 24 from rfl,
    show UInt64.ofNat 16 = 16 from rfl, show UInt64.ofNat 63 = 63 from rfl]
  rw [add_right_comm' (a.word w) (m₁.word w) (b.word w), add_right_comm' _ (m₂.word w)]

/-- **The portable `g` is `G` on four words of the state.** -/
theorem portable_g_eq_set4 (v : Array UInt64) {a b c d : ℕ} (ha : a < v.size) (hb : b < v.size)
    (hc : c < v.size) (hd : d < v.size) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (x y : UInt64) :
    Portable.g v a b c d x y = set4 v a b c d (G4 x y (v[a]!, v[b]!, v[c]!, v[d]!)) :=
  mix_eq_set4 v ha hb hc hd hab hac had hbc hbd hcd x y

/-- Four lanes of four words, as the rows `a`, `b`, `c`, `d`. -/
def rowsOfLanes (f : ℕ → UInt64 × UInt64 × UInt64 × UInt64) : M256i × M256i × M256i × M256i :=
  (⟨(f 0).1, (f 1).1, (f 2).1, (f 3).1⟩, ⟨(f 0).2.1, (f 1).2.1, (f 2).2.1, (f 3).2.1⟩,
    ⟨(f 0).2.2.1, (f 1).2.2.1, (f 2).2.2.1, (f 3).2.2.1⟩,
    ⟨(f 0).2.2.2, (f 1).2.2.2, (f 2).2.2.2, (f 3).2.2.2⟩)

/-- Vectors with equal words are equal. -/
theorem M256i.eq_of_word {x y : M256i} (h : ∀ w < 4, x.word w = y.word w) : x = y := by
  obtain ⟨x0, x1, x2, x3⟩ := x
  obtain ⟨y0, y1, y2, y3⟩ := y
  simp only [M256i.mk.injEq]
  exact ⟨h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)⟩

/-- `g1` then `g2`, as rows: `G` on each lane. -/
theorem g2_g1_rows (a b c d m₁ m₂ : M256i) :
    Avx2.g2 (Avx2.g1 (a, b, c, d) m₁) m₂ =
      rowsOfLanes fun w => G4 (m₁.word w) (m₂.word w) (a.word w, b.word w, c.word w, d.word w) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> apply M256i.eq_of_word <;> intro w hw
  · have h := congrArg Prod.fst (g2_g1 a b c d m₁ m₂ hw)
    interval_cases w <;> exact h
  · have h := congrArg (fun t => t.2.1) (g2_g1 a b c d m₁ m₂ hw)
    interval_cases w <;> exact h
  · have h := congrArg (fun t => t.2.2.1) (g2_g1 a b c d m₁ m₂ hw)
    interval_cases w <;> exact h
  · have h := congrArg (fun t => t.2.2.2) (g2_g1 a b c d m₁ m₂ hw)
    interval_cases w <;> exact h

/-- Rows of equal lanes are equal. -/
theorem rowsOfLanes_congr {f g : ℕ → UInt64 × UInt64 × UInt64 × UInt64}
    (h : ∀ w < 4, f w = g w) : rowsOfLanes f = rowsOfLanes g := by
  simp only [rowsOfLanes, h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]

/-- `g1` then `g2` on rows given as lanes. -/
theorem g2_g1_lanes (f : ℕ → UInt64 × UInt64 × UInt64 × UInt64) (m₁ m₂ : M256i) :
    Avx2.g2 (Avx2.g1 (rowsOfLanes f) m₁) m₂ =
      rowsOfLanes fun w => G4 (m₁.word w) (m₂.word w) (f w) := by
  rw [rowsOfLanes, g2_g1_rows]
  apply rowsOfLanes_congr
  intro w hw
  interval_cases w <;> rfl

/-- `diagonalize`: row `a` one lane over, `c` three, `d` two; `b` in place. -/
theorem diagonalize_lanes (f : ℕ → UInt64 × UInt64 × UInt64 × UInt64) :
    Avx2.diagonalize (rowsOfLanes f) = rowsOfLanes fun w =>
      ((f ((w + 3) % 4)).1, (f w).2.1, (f ((w + 1) % 4)).2.2.1, (f ((w + 2) % 4)).2.2.2) := by
  rfl

/-- `undiagonalize`: the lanes back. -/
theorem undiagonalize_lanes (f : ℕ → UInt64 × UInt64 × UInt64 × UInt64) :
    Avx2.undiagonalize (rowsOfLanes f) = rowsOfLanes fun w =>
      ((f ((w + 1) % 4)).1, (f w).2.1, (f ((w + 3) % 4)).2.2.1, (f ((w + 2) % 4)).2.2.2) := by
  rfl

/-! ## The message words of each `b0` -/

/-- Which message word a `Shuffle` puts in lane `i`, the message vector `k` holding words
    `2k`, `2k + 1` in each 128-bit lane. -/
def Avx2.Shuffle.idx : Avx2.Shuffle → ℕ → ℕ
  | .lo x y, i => if i % 2 = 0 then 2 * x else 2 * y
  | .hi x y, i => if i % 2 = 0 then 2 * x + 1 else 2 * y + 1
  | .alignr x y, i => if i % 2 = 0 then 2 * y + 1 else 2 * x
  | .blend x y, i => if i % 2 = 0 then 2 * y else 2 * x + 1
  | .swap x, i => if i % 2 = 0 then 2 * x + 1 else 2 * x

/-- The message vectors of `x` and `y` that a `Shuffle` reads. -/
def Avx2.Shuffle.vecs : Avx2.Shuffle → List ℕ
  | .lo x y | .hi x y | .alignr x y | .blend x y => [x, y]
  | .swap x => [x]

/-- Word `i` of a shuffle of the message vectors is message word `sh.idx i`. -/
theorem word_apply (M : ℕ → UInt64) (mv : Array M256i)
    (hmv : ∀ k < 8, mv[k]! = ⟨M (2 * k), M (2 * k + 1), M (2 * k), M (2 * k + 1)⟩)
    (sh : Avx2.Shuffle) (hsh : ∀ k ∈ sh.vecs, k < 8) {i : ℕ} (hi : i < 4) :
    (sh.apply mv).word i = M (sh.idx i) := by
  cases sh with
  | lo x y =>
    simp only [Avx2.Shuffle.apply, mm256UnpackloEpi64, Avx2.Shuffle.idx,
      hmv x (hsh x (by simp [Avx2.Shuffle.vecs])), hmv y (hsh y (by simp [Avx2.Shuffle.vecs]))]
    interval_cases i <;> rfl
  | hi x y =>
    simp only [Avx2.Shuffle.apply, mm256UnpackhiEpi64, Avx2.Shuffle.idx,
      hmv x (hsh x (by simp [Avx2.Shuffle.vecs])), hmv y (hsh y (by simp [Avx2.Shuffle.vecs]))]
    interval_cases i <;> rfl
  | alignr x y =>
    simp only [Avx2.Shuffle.apply, word_alignr _ _ hi, Avx2.Shuffle.idx,
      hmv x (hsh x (by simp [Avx2.Shuffle.vecs])), hmv y (hsh y (by simp [Avx2.Shuffle.vecs]))]
    interval_cases i <;> rfl
  | blend x y =>
    simp only [Avx2.Shuffle.apply, word_blend 0x33 _ _ hi (by interval_cases i <;> decide),
      Avx2.Shuffle.idx, hmv x (hsh x (by simp [Avx2.Shuffle.vecs])),
      hmv y (hsh y (by simp [Avx2.Shuffle.vecs]))]
    interval_cases i <;> rfl
  | swap x =>
    simp only [Avx2.Shuffle.apply, show Avx2.mmShuffle 1 0 3 2 = 78 by decide, word_swap _ hi,
      Avx2.Shuffle.idx,
      hmv x (hsh x (by simp [Avx2.Shuffle.vecs]))]
    interval_cases i <;> rfl

/-- `b0`: lanes 0 and 1 from `t0`, 2 and 3 from `t1`. -/
theorem word_b0 (M : ℕ → UInt64) (mv : Array M256i)
    (hmv : ∀ k < 8, mv[k]! = ⟨M (2 * k), M (2 * k + 1), M (2 * k), M (2 * k + 1)⟩)
    (t : Avx2.Shuffle × Avx2.Shuffle) (ht : ∀ k ∈ t.1.vecs ++ t.2.vecs, k < 8) {i : ℕ}
    (hi : i < 4) :
    (Avx2.b0 mv t).word i = M (if i < 2 then t.1.idx i else t.2.idx i) := by
  rw [Avx2.b0, word_blend 0xF0 _ _ hi (by interval_cases i <;> decide)]
  have h₁ := fun j (hj : j < 4) =>
    word_apply M mv hmv t.1 (fun k hk => ht k (List.mem_append_left _ hk)) hj
  have h₂ := fun j (hj : j < 4) =>
    word_apply M mv hmv t.2 (fun k hk => ht k (List.mem_append_right _ hk)) hj
  interval_cases i <;> simp [h₁, h₂]

/-- Where `G`'s message words sit in `SIGMA`'s row, for `b0` number `q` and lane `i`: the
    columns' `x` and `y`, then the diagonals', one lane over. -/
def sigmaPos (q i : ℕ) : ℕ :=
  match q with
  | 0 => 2 * i
  | 1 => 2 * i + 1
  | 2 => 8 + 2 * ((i + 3) % 4)
  | _ => 8 + 2 * ((i + 3) % 4) + 1

/-- **The table of shuffles is `SIGMA`**: every round's `b0`s hold the message words `SIGMA`
    names, and read only the eight message vectors. -/
theorem rounds_sigma : ∀ r < 12, ∀ q < 4,
    (∀ k ∈ (Avx2.rounds[r]![q]!).1.vecs ++ (Avx2.rounds[r]![q]!).2.vecs, k < 8) ∧
    ∀ i < 4, (if i < 2 then (Avx2.rounds[r]![q]!).1.idx i else (Avx2.rounds[r]![q]!).2.idx i) =
      (SIGMA[r]!)[sigmaPos q i]! := by
  decide

/-! ## A round -/

/-- The rows of a 16-word state: row `a` is words 0–3, `b` 4–7, `c` 8–11, `d` 12–15. -/
def rowsOf (v : Array UInt64) : Avx2.Rows :=
  rowsOfLanes fun w => (v[w]!, v[4 + w]!, v[8 + w]!, v[12 + w]!)

/-- `SIGMA` names message words `0 … 15`. -/
theorem SIGMA_lt : ∀ r < 12, ∀ j < 16, (SIGMA[r]!)[j]! < 16 := by decide

/-- `g` keeps the state's size. -/
theorem size_portable_g (v : Array UInt64) (a b c d : ℕ) (x y : UInt64) :
    (Portable.g v a b c d x y).size = v.size := by
  simp [Portable.g]

/-- `set4` keeps the state's size. -/
theorem size_set4 (v : Array UInt64) (a b c d : ℕ) (s : UInt64 × UInt64 × UInt64 × UInt64) :
    (set4 v a b c d s).size = v.size := by
  simp [set4]

set_option maxHeartbeats 2000000 in
/-- **An AVX2 round is a portable round**, on the rows of the state, the message vectors
    holding the message words `M`. -/
theorem avx2_round_eq (v : Array UInt64) (hv : v.size = 16) (M : ℕ → UInt64) (m : Array UInt64)
    (hm : ∀ j < 16, m[j]! = M j) (mv : Array M256i)
    (hmv : ∀ k < 8, mv[k]! = ⟨M (2 * k), M (2 * k + 1), M (2 * k), M (2 * k + 1)⟩)
    (r : ℕ) (hr : r < 12) :
    Avx2.round mv (Avx2.rounds[r]!) (rowsOf v) = rowsOf (Portable.round r m v) := by
  have hb : ∀ q < 4, Avx2.b0 mv (Avx2.rounds[r]![q]!) =
      ⟨M ((SIGMA[r]!)[sigmaPos q 0]!), M ((SIGMA[r]!)[sigmaPos q 1]!),
        M ((SIGMA[r]!)[sigmaPos q 2]!), M ((SIGMA[r]!)[sigmaPos q 3]!)⟩ := by
    intro q hq
    obtain ⟨hk, hi⟩ := rounds_sigma r hr q hq
    apply M256i.eq_of_word
    intro i hi'
    rw [word_b0 M mv hmv _ hk hi', hi i hi']
    interval_cases i <;> rfl
  have hs := SIGMA_lt r hr
  have hmS : ∀ j < 16, m[(SIGMA[r]!)[j]!]! = M ((SIGMA[r]!)[j]!) := fun j hj => hm _ (hs j hj)
  rw [Avx2.round, hb 0 (by omega), hb 1 (by omega), hb 2 (by omega), hb 3 (by omega), rowsOf,
    g2_g1_lanes, diagonalize_lanes, g2_g1_lanes, undiagonalize_lanes]
  simp only [Portable.round]
  rw [portable_g_eq_set4 _ (by simp [size_portable_g, hv]) (by simp [size_portable_g, hv])
      (by simp [size_portable_g, hv]) (by simp [size_portable_g, hv]) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide),
    portable_g_eq_set4 _ (by simp [size_portable_g, hv]) (by simp [size_portable_g, hv])
      (by simp [size_portable_g, hv]) (by simp [size_portable_g, hv]) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide),
    portable_g_eq_set4 _ (by simp [size_portable_g, hv]) (by simp [size_portable_g, hv])
      (by simp [size_portable_g, hv]) (by simp [size_portable_g, hv]) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide),
    portable_g_eq_set4 _ (by simp [size_portable_g, hv]) (by simp [size_portable_g, hv])
      (by simp [size_portable_g, hv]) (by simp [size_portable_g, hv]) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide),
    portable_g_eq_set4 _ (by simp [size_portable_g, hv]) (by simp [size_portable_g, hv])
      (by simp [size_portable_g, hv]) (by simp [size_portable_g, hv]) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide),
    portable_g_eq_set4 _ (by simp [size_portable_g, hv]) (by simp [size_portable_g, hv])
      (by simp [size_portable_g, hv]) (by simp [size_portable_g, hv]) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide),
    portable_g_eq_set4 _ (by simp [size_portable_g, hv]) (by simp [size_portable_g, hv])
      (by simp [size_portable_g, hv]) (by simp [size_portable_g, hv]) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide),
    portable_g_eq_set4 _ (by simp [hv]) (by simp [hv])
      (by simp [hv]) (by simp [hv]) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]
  apply rowsOfLanes_congr
  intro w hw
  interval_cases w <;>
    simp [set4, Array.set!_eq_setIfInBounds, getElem!_pos, Array.size_setIfInBounds,
      hv, hmS, sigmaPos, M256i.word]

/-! ## `compress_block` -/

/-- Eight words or'd together, in reverse order. -/
theorem or_rev8 (a b c d e f g h : UInt64) :
    a ||| b ||| c ||| d ||| e ||| f ||| g ||| h = h ||| g ||| f ||| e ||| d ||| c ||| b ||| a := by
  have lc : ∀ x y z : UInt64, x ||| (y ||| z) = y ||| (x ||| z) := fun x y z => by
    rw [← UInt64.or_assoc, UInt64.or_comm x y, UInt64.or_assoc]
  simp only [UInt64.or_comm, lc]

/-- Two left shifts, by less than 64 in all, are one. -/
theorem shl_shl (x a b : UInt64) (h : a.toNat + b.toNat < 64) : (x <<< a) <<< b = x <<< (a + b) :=
  (UInt64.shiftLeft_add_of_toNat_lt h).symm

/-- The word bytes `8j … 8j + 7` of `p` make, as `_mm_loadu_si128` reads them, is
    `u64::from_le_bytes` of them. -/
theorem wordOfBytes_eq (p : List ℕ) (j : ℕ) :
    wordOfBytes (fun k => UInt64.ofNat (p.getD k 0)) j =
      u64FromLeBytes ((p.drop (8 * j)).take 8) := by
  rw [u64FromLeBytes_eq_word]
  simp only [wordOfBytes, word, List.range_succ, List.range_zero, List.nil_append,
    List.foldr_append, List.foldr_cons, List.foldr_nil, UInt64.zero_shiftLeft, UInt64.zero_or,
    UInt64.shiftLeft_or]
  have h : ∀ (x n : UInt64), n.toNat + 8 < 64 → (x <<< n) <<< 8 = x <<< (n + 8) :=
    fun x n hn => shl_shl x n 8 hn
  have h8 : ∀ x : UInt64, (x <<< 8) <<< 8 = x <<< 16 := fun x => h x 8 (by decide)
  have h16 : ∀ x : UInt64, (x <<< 16) <<< 8 = x <<< 24 := fun x => h x 16 (by decide)
  have h24 : ∀ x : UInt64, (x <<< 24) <<< 8 = x <<< 32 := fun x => h x 24 (by decide)
  have h32 : ∀ x : UInt64, (x <<< 32) <<< 8 = x <<< 40 := fun x => h x 32 (by decide)
  have h40 : ∀ x : UInt64, (x <<< 40) <<< 8 = x <<< 48 := fun x => h x 40 (by decide)
  have h48 : ∀ x : UInt64, (x <<< 48) <<< 8 = x <<< 56 := fun x => h x 48 (by decide)
  simp only [h8, h16, h24, h32, h40, h48, Nat.add_zero]
  exact or_rev8 _ _ _ _ _ _ _ _

/-- A round keeps the state's size. -/
theorem size_portable_round (r : ℕ) (m v : Array UInt64) :
    (Portable.round r m v).size = v.size := by
  simp [Portable.round, size_portable_g]

/-- `rounds` is its twelve rows. -/
theorem rounds_eq_map : Avx2.rounds = (List.range 12).map (Avx2.rounds[·]!) := rfl

/-- The twelve rounds, AVX2 and portable, on rows. -/
theorem foldl_rounds (M : ℕ → UInt64) (m : Array UInt64) (hm : ∀ j < 16, m[j]! = M j)
    (mv : Array M256i)
    (hmv : ∀ k < 8, mv[k]! = ⟨M (2 * k), M (2 * k + 1), M (2 * k), M (2 * k + 1)⟩) :
    ∀ k ≤ 12, ∀ v : Array UInt64, v.size = 16 →
      ((List.range k).map (Avx2.rounds[·]!)).foldl (fun s r => Avx2.round mv r s) (rowsOf v) =
        rowsOf ((List.range k).foldl (fun v r => Portable.round r m v) v) := by
  intro k
  induction k with
  | zero => intro _ v _; rfl
  | succ k ih =>
    intro hk v hv
    rw [List.range_succ, List.map_append, List.foldl_append, List.foldl_append, ih (by omega) v hv]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    exact avx2_round_eq _ (by
      clear ih; induction k generalizing v with
      | zero => simpa using hv
      | succ k ih' =>
        rw [List.range_succ, List.foldl_append]; simp only [List.foldl_cons, List.foldl_nil]
        rw [size_portable_round]; exact ih' (by omega) v hv) M m hm mv hmv k (by omega)

/-- The message vectors of the AVX2 `compress_block` hold the portable one's message words. -/
theorem msgvecs (block : List ℕ) (k : ℕ) (hk : k < 8) :
    ((List.range 8).toArray.map fun k =>
        mm256Broadcastsi128Si256 (mmLoaduSi128 ((block.drop (16 * k)).take 16)))[k]! =
      ⟨u64FromLeBytes ((block.drop (8 * (2 * k))).take 8),
        u64FromLeBytes ((block.drop (8 * (2 * k + 1))).take 8),
        u64FromLeBytes ((block.drop (8 * (2 * k))).take 8),
        u64FromLeBytes ((block.drop (8 * (2 * k + 1))).take 8)⟩ := by
  have hdrop : ∀ n < 2, (((block.drop (16 * k)).take 16).drop (8 * n)).take 8 =
      (block.drop (8 * (2 * k + n))).take 8 := fun n hn => by
    rw [List.drop_take, List.drop_drop, List.take_take]
    congr 1
    · omega
    · congr 1; omega
  have he : ((List.range 8).toArray.map fun k =>
      mm256Broadcastsi128Si256 (mmLoaduSi128 ((block.drop (16 * k)).take 16)))[k]! =
      mm256Broadcastsi128Si256 (mmLoaduSi128 ((block.drop (16 * k)).take 16)) := by simp [hk]
  rw [he]
  simp only [mm256Broadcastsi128Si256, mmLoaduSi128, wordOfBytes_eq]
  rw [show 8 * 0 = 8 * 0 from rfl, hdrop 0 (by omega), show 8 * 1 = 8 * 1 from rfl,
    hdrop 1 (by omega)]
  simp

/-- The AVX2 `compress_block`'s first rows are the portable one's first state. -/
theorem avx2_init_eq (words : Array UInt64) (hw : words.size = 8) (count : ℕ)
    (lastBlock lastNode : UInt64) :
    (mm256LoaduSi256 (words.extract 0 4), mm256LoaduSi256 (words.extract 4 8),
      mm256LoaduSi256 (IV.extract 0 4),
      mm256XorSi256 (mm256LoaduSi256 (IV.extract 4 8))
        (mm256SetrEpi64x (countLow count) (countHigh count) lastBlock lastNode)) =
    rowsOf (words ++ #[IV[0]!, IV[1]!, IV[2]!, IV[3]!, IV[4]! ^^^ countLow count,
      IV[5]! ^^^ countHigh count, IV[6]! ^^^ lastBlock, IV[7]! ^^^ lastNode]) := by
  simp only [rowsOf, rowsOfLanes, mm256LoaduSi256, mm256XorSi256, mm256SetrEpi64x, M256i.ofWords,
    M256i.word, Prod.mk.injEq, M256i.mk.injEq]
  simp [hw, IV]

/-- Three words xored, in another order. -/
theorem xor3 (a b c : UInt64) : a ^^^ b ^^^ c = c ^^^ a ^^^ b := by
  rw [UInt64.xor_comm _ c, UInt64.xor_assoc]

/-- **The AVX2 `compress_block` is the portable one.** -/
theorem avx2_compressBlock_eq (block : List ℕ) (words : Array UInt64) (hw : words.size = 8)
    (count : ℕ) (lastBlock lastNode : UInt64) :
    Avx2.compressBlock block words count lastBlock lastNode =
      Portable.compressBlock block words count lastBlock lastNode := by
  have hv0 : (words ++ #[IV[0]!, IV[1]!, IV[2]!, IV[3]!, IV[4]! ^^^ countLow count,
      IV[5]! ^^^ countHigh count, IV[6]! ^^^ lastBlock, IV[7]! ^^^ lastNode]).size = 16 := by
    simp [hw]
  have hm : ∀ j < 16, ((List.range 16).toArray.map
      fun i => u64FromLeBytes ((block.drop (8 * i)).take 8))[j]! =
      u64FromLeBytes ((block.drop (8 * j)).take 8) := fun j hj => by simp [hj]
  simp only [Avx2.compressBlock, Portable.compressBlock]
  rw [avx2_init_eq words hw count lastBlock lastNode, rounds_eq_map,
    foldl_rounds _ _ hm _ (msgvecs block) 12 le_rfl _ hv0]
  simp only [rowsOf, rowsOfLanes, mm256XorSi256, mm256StoreuSi256, mm256LoaduSi256,
    M256i.ofWords, M256i.word]
  apply Array.ext_getElem?
  intro i
  by_cases hi : i < 8
  · interval_cases i <;> simp [hw] <;> exact xor3 _ _ _
  · simp [hi]

/-! ## Every implementation -/

/-- Both implementations' `compress_block` are RFC 7693's compression. -/
theorem compressOk (impl : Implementation) : CompressOk impl.compressBlock := by
  cases impl with
  | portable => exact compressOk_portable
  | avx2 =>
    intro block words hw count last
    rw [Implementation.compressBlock, avx2_compressBlock_eq _ _ hw]
    exact compressOk_portable block words hw count last

/-- **`blake2b_simd`'s `State` computes the specification's `BLAKE2b-ℓ(p, x)`**, on either
    implementation: `to_state` from the parameters `ℓ/8` and `p`, `update` with each piece of
    `xs`, then `finalize`, give `BLAKE2b-ℓ(p, x)` of the bytes of `xs`, fewer than `2^128`. -/
theorem finalize_foldl_update_spec (impl : Implementation) (hp : HashParams)
    (xs : List (List Byte)) (hlen : xs.flatten.length < 2 ^ 128) :
    ((xs.map (·.map BitVec.toNat)).foldl State.update
        (Params.toState ⟨hp.len, hp.personal.toList.map BitVec.toNat, impl⟩)).finalize.map
      (BitVec.ofNat 8) = (Spec.Blake2b.hashFn hp xs.flatten).toList := by
  have e : (xs.map (·.map BitVec.toNat)).flatten = xs.flatten.map BitVec.toNat :=
    (List.map_flatten ..).symm
  rw [finalize_foldl_update _ (compressOk impl) hp.len_le _
    (by rw [e, List.length_map]; exact hlen), e, ← hashFn_eq]
  rfl

-- The build fails if the theorem rests on anything beyond Lean's three axioms.
/--
info: 'Equihash.Verifier.Blake2b.finalize_foldl_update_spec' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms finalize_foldl_update_spec

end Equihash.Verifier.Blake2b
