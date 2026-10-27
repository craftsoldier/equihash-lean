/-
The AVX2 and NEON kernels compute what the portable kernel does. `Midstate::compress` is one
program over a type of `Lanes`; on a type whose operations act on each lane as `u64`'s do, lane
`j` of its result is the one-lane result for block `j`. So `LeafHasher::hash` returns the same
digests under every `Kernel`, and the leaf hasher's proof covers them all.
-/
module

public import Equihash.Verifier.LeafHash
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace Equihash.Verifier

open LeafHash Lanes X86_64 Aarch64

/-! ## Lanes seen one at a time -/

/-- `L` holds `LANES` lanes, `lane x j` the `j`-th word of `x`, and each `Lanes` operation acts
    on every lane as `u64`'s does. `load` and `store` see the first `LANES` words of a
    `[u64; MAX_LANES]`. -/
structure LaneView (L : Type) [Lanes L] [Inhabited L] where
  lane : L → ℕ → UInt64
  lanes_le : LANES L ≤ MAX_LANES
  lane_default : ∀ j, lane default j = 0
  lane_splat : ∀ j < LANES L, ∀ x, lane (splat x) j = x
  lane_load : ∀ j < LANES L, ∀ words : Array UInt64, words.size = MAX_LANES →
    lane (load words) j = words[j]!
  size_store : ∀ (x : L) (words : Array UInt64), words.size = MAX_LANES →
    (store x words).size = MAX_LANES
  getElem!_store : ∀ (x : L) (words : Array UInt64), words.size = MAX_LANES →
    ∀ j < LANES L, (store x words)[j]! = lane x j
  lane_add : ∀ j < LANES L, ∀ x y, lane (add x y) j = add (lane x j) (lane y j)
  lane_xor : ∀ j < LANES L, ∀ x y, lane (xor x y) j = xor (lane x j) (lane y j)
  lane_xorRotr32 : ∀ j < LANES L, ∀ x y, lane (xorRotr32 x y) j = xorRotr32 (lane x j) (lane y j)
  lane_xorRotr24 : ∀ j < LANES L, ∀ x y, lane (xorRotr24 x y) j = xorRotr24 (lane x j) (lane y j)
  lane_xorRotr16 : ∀ j < LANES L, ∀ x y, lane (xorRotr16 x y) j = xorRotr16 (lane x j) (lane y j)
  lane_xorRotr63 : ∀ j < LANES L, ∀ x y, lane (xorRotr63 x y) j = xorRotr63 (lane x j) (lane y j)

variable {L : Type} [Lanes L] [Inhabited L]

/-- `u64`'s `xor`. -/
theorem Lanes.xor_u64 (x y : UInt64) : xor x y = x ^^^ y := rfl

/-- Lane `j` of each state word. -/
def LaneView.proj (V : LaneView L) (j : ℕ) (v : Array L) : Array UInt64 := v.map (V.lane · j)

theorem LaneView.getElem!_proj (V : LaneView L) (j : ℕ) (v : Array L) (i : ℕ) :
    (V.proj j v)[i]! = V.lane v[i]! j := by
  simp only [proj, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases v[i]? <;> simp [V.lane_default, show (default : UInt64) = 0 from rfl]

theorem LaneView.proj_set! (V : LaneView L) (j : ℕ) (v : Array L) (i : ℕ) (x : L) :
    V.proj j (v.set! i x) = (V.proj j v).set! i (V.lane x j) := by
  simp only [proj, Array.set!_eq_setIfInBounds, Array.map_setIfInBounds]

theorem LaneView.proj_replicate (V : LaneView L) (j : ℕ) (hj : j < LANES L) (n : ℕ) (x : UInt64) :
    V.proj j (Array.replicate n (splat x)) = Array.replicate n x := by
  simp [proj, V.lane_splat j hj]

/-- **`g` lane by lane.** -/
theorem LaneView.proj_g (V : LaneView L) (j : ℕ) (hj : j < LANES L) (v : Array L) (a b c d : ℕ)
    (x y : L) : V.proj j (g v a b c d x y) = g (V.proj j v) a b c d (V.lane x j) (V.lane y j) := by
  simp only [g, V.lane_add j hj, V.lane_xorRotr32 j hj, V.lane_xorRotr24 j hj,
    V.lane_xorRotr16 j hj, V.lane_xorRotr63 j hj, ← getElem!_proj, proj_set!]

/-- **`rounds` lane by lane.** -/
theorem LaneView.proj_rounds (V : LaneView L) (j : ℕ) (hj : j < LANES L) (v : Array L)
    (word : ℕ → L) : V.proj j (rounds v word) = rounds (V.proj j v) fun i => V.lane (word i) j := by
  simp only [rounds, Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  refine (List.foldl_hom (V.proj j) ?_).symm
  intro v r
  simp only [V.proj_g j hj]

/-! ## The three kernels' lanes -/

/-- `u64`: one lane, itself. -/
def u64View : LaneView UInt64 where
  lane x _ := x
  lanes_le := by decide
  lane_default _ := rfl
  lane_splat _ _ _ := rfl
  lane_load j hj words _ := by
    have : j = 0 := by simp only [LANES] at hj; omega
    subst this; rfl
  size_store _ _ h := by simp [store, h]
  getElem!_store x words h j hj := by
    have : j = 0 := by simp only [LANES] at hj; omega
    subst this
    simp [store, h, MAX_LANES]
  lane_add _ _ _ _ := rfl
  lane_xor _ _ _ _ := rfl
  lane_xorRotr32 _ _ _ _ := rfl
  lane_xorRotr24 _ _ _ _ := rfl
  lane_xorRotr16 _ _ _ _ := rfl
  lane_xorRotr63 _ _ _ _ := rfl

theorem M256i.word_ofWords (f : ℕ → UInt64) (j : ℕ) (hj : j < 4) :
    (M256i.ofWords f).word j = f j := by
  interval_cases j <;> rfl

/-- Words are equal when their bits are: how each rotation identity below is checked, one bit
    position at a time. -/
theorem UInt64.ext_bit {a b : UInt64}
    (h : ∀ i < 64, a.toBitVec.getLsbD i = b.toBitVec.getLsbD i) : a = b :=
  UInt64.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq h)

/-- `x + x` is `x << 1`. -/
theorem UInt64.add_self_eq_shiftLeft (x : UInt64) : x + x = x <<< 1 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add, UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]
  simp only [show (1 : UInt64).toNat % 64 = 1 from rfl]
  omega

/-- `_mm256_shuffle_epi32` with `0b10_11_00_01` swaps the halves of each 64-bit element. -/
theorem avx2_rotr32 (a : M256i) :
    mm256ShuffleEpi32 0b10110001 a = .ofWords fun w => rotateRight (a.word w) 32 := by
  simp [mm256ShuffleEpi32, M256i.ofWords, vecDword, M256i.word, rotateRight]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · apply UInt64.ext_bit
    intro i hi
    interval_cases i <;> simp +decide

/-- `_mm256_shuffle_epi8` with `xor_rotr24`'s table rotates each 64-bit element right by 24. -/
theorem avx2_rotr24 (a : M256i) :
    mm256ShuffleEpi8 a (mm256SetrEpi8 [3, 4, 5, 6, 7, 0, 1, 2, 11, 12, 13, 14, 15, 8, 9, 10,
      3, 4, 5, 6, 7, 0, 1, 2, 11, 12, 13, 14, 15, 8, 9, 10]) =
      .ofWords fun w => rotateRight (a.word w) 24 := by
  simp [mm256ShuffleEpi8, mm256SetrEpi8, M256i.ofWords, wordOfBytes, vecByte, M256i.word,
    List.getD, rotateRight]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · apply UInt64.ext_bit
    intro i hi
    simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
      UInt64.toBitVec_ofNat, BitVec.getLsbD_or]
    interval_cases i <;> simp +decide

/-- `_mm256_shuffle_epi8` with `xor_rotr16`'s table rotates each 64-bit element right by 16. -/
theorem avx2_rotr16 (a : M256i) :
    mm256ShuffleEpi8 a (mm256SetrEpi8 [2, 3, 4, 5, 6, 7, 0, 1, 10, 11, 12, 13, 14, 15, 8, 9,
      2, 3, 4, 5, 6, 7, 0, 1, 10, 11, 12, 13, 14, 15, 8, 9]) =
      .ofWords fun w => rotateRight (a.word w) 16 := by
  simp [mm256ShuffleEpi8, mm256SetrEpi8, M256i.ofWords, wordOfBytes, vecByte, M256i.word,
    List.getD, rotateRight]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · apply UInt64.ext_bit
    intro i hi
    simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
      UInt64.toBitVec_ofNat, BitVec.getLsbD_or]
    interval_cases i <;> simp +decide

/-- `x >> 63 | (x + x)` rotates each 64-bit element right by 63: `x + x` is `x << 1`. -/
theorem avx2_rotr63 (x : M256i) :
    mm256OrSi256 (mm256SrliEpi64 63 x) (mm256AddEpi64 x x) =
      .ofWords fun w => rotateRight (x.word w) 63 := by
  simp [mm256OrSi256, mm256SrliEpi64, mm256AddEpi64, M256i.ofWords, M256i.word, rotateRight,
    UInt64.add_self_eq_shiftLeft]

/-- `__m256i`: four lanes, its words. -/
def avx2View : LaneView M256i where
  lane x j := x.word j
  lanes_le := by decide
  lane_default j := by
    show (default : M256i).word j = 0
    match j with
    | 0 | 1 | 2 | 3 => rfl
    | _ + 4 => rfl
  lane_splat j hj x := M256i.word_ofWords _ j hj
  lane_load j hj words _ := M256i.word_ofWords _ j hj
  size_store _ _ _ := rfl
  getElem!_store x _ _ j hj := by
    show (mm256StoreuSi256 x)[j]! = x.word j
    have hj : j < 4 := hj
    interval_cases j <;> rfl
  lane_add j hj x y := M256i.word_ofWords _ j hj
  lane_xor j hj x y := M256i.word_ofWords _ j hj
  lane_xorRotr32 j hj x y := by
    show (mm256ShuffleEpi32 _ _).word j = rotateRight (x.word j ^^^ y.word j) 32
    rw [avx2_rotr32, M256i.word_ofWords _ j hj]
    exact congrArg (rotateRight · 32) (M256i.word_ofWords _ j hj)
  lane_xorRotr24 j hj x y := by
    show (mm256ShuffleEpi8 _ _).word j = rotateRight (x.word j ^^^ y.word j) 24
    rw [avx2_rotr24, M256i.word_ofWords _ j hj]
    exact congrArg (rotateRight · 24) (M256i.word_ofWords _ j hj)
  lane_xorRotr16 j hj x y := by
    show (mm256ShuffleEpi8 _ _).word j = rotateRight (x.word j ^^^ y.word j) 16
    rw [avx2_rotr16, M256i.word_ofWords _ j hj]
    exact congrArg (rotateRight · 16) (M256i.word_ofWords _ j hj)
  lane_xorRotr63 j hj x y := by
    show (mm256OrSi256 _ _).word j = rotateRight (x.word j ^^^ y.word j) 63
    rw [avx2_rotr63, M256i.word_ofWords _ j hj]
    exact congrArg (rotateRight · 63) (M256i.word_ofWords _ j hj)

theorem Uint64x2.word_ofWords (f : ℕ → UInt64) (j : ℕ) (hj : j < 2) :
    (Uint64x2.ofWords f).word j = f j := by
  interval_cases j <;> rfl

/-- Both `rotr32` bodies rotate each 64-bit element of `a ^ b` right by 32. -/
theorem neonRotr32_eq (sha3 : Bool) (a b : Uint64x2) :
    neonRotr32 sha3 a b = .ofWords fun w => rotateRight (a.word w ^^^ b.word w) 32 := by
  cases sha3
  · simp [neonRotr32, vreinterpretqU64U32, vreinterpretqU32U64, vrev64qU32, veorqU64,
      Uint64x2.ofWords, vecDword, Uint64x2.word, rotateRight]
    refine ⟨?_, ?_⟩ <;>
    · apply UInt64.ext_bit
      intro i hi
      interval_cases i <;> simp +decide
  · rfl

/-- Both `rotr24` bodies rotate each 64-bit element of `a ^ b` right by 24. -/
theorem neonRotr24_eq (sha3 : Bool) (a b : Uint64x2) :
    neonRotr24 sha3 a b = .ofWords fun w => rotateRight (a.word w ^^^ b.word w) 24 := by
  cases sha3
  · simp [neonRotr24, vreinterpretqU64U8, vreinterpretqU8U64, vqtbl1qU8, vld1qU8, veorqU64, ROTR24,
      Uint64x2.ofWords, wordOfBytes, vecByte, Uint64x2.word, List.getD, rotateRight]
    refine ⟨?_, ?_⟩ <;>
    · apply UInt64.ext_bit
      intro i hi
      interval_cases i <;> simp +decide
  · rfl

/-- Both `rotr16` bodies rotate each 64-bit element of `a ^ b` right by 16. -/
theorem neonRotr16_eq (sha3 : Bool) (a b : Uint64x2) :
    neonRotr16 sha3 a b = .ofWords fun w => rotateRight (a.word w ^^^ b.word w) 16 := by
  cases sha3
  · simp [neonRotr16, vreinterpretqU64U8, vreinterpretqU8U64, vqtbl1qU8, vld1qU8, veorqU64, ROTR16,
      Uint64x2.ofWords, wordOfBytes, vecByte, Uint64x2.word, List.getD, rotateRight]
    refine ⟨?_, ?_⟩ <;>
    · apply UInt64.ext_bit
      intro i hi
      interval_cases i <;> simp +decide
  · rfl

/-- Both `rotr63` bodies rotate each 64-bit element of `a ^ b` right by 63. -/
theorem neonRotr63_eq (sha3 : Bool) (a b : Uint64x2) :
    neonRotr63 sha3 a b = .ofWords fun w => rotateRight (a.word w ^^^ b.word w) 63 := by
  cases sha3
  · simp [neonRotr63, vsriqNU64, vaddqU64, veorqU64, Uint64x2.ofWords, Uint64x2.word, rotateRight,
      UInt64.add_self_eq_shiftLeft]
    refine ⟨?_, ?_⟩ <;>
    · apply UInt64.ext_bit
      intro i hi
      interval_cases i <;> simp +decide
  · rfl

/-- Lane `j` of a `NeonLanes`: word `j % 2` of vector `j / 2`. -/
def NeonLanes.lane {sha3 : Bool} (x : NeonLanes sha3) : ℕ → UInt64
  | 0 => x.v0.w0
  | 1 => x.v0.w1
  | 2 => x.v1.w0
  | 3 => x.v1.w1
  | _ => 0

/-- `NeonLanes` and `NeonSha3Lanes`: four lanes, the words of their two vectors. -/
def neonView (sha3 : Bool) : LaneView (NeonLanes sha3) where
  lane := NeonLanes.lane
  lanes_le := Nat.le_refl _
  lane_default j := by
    match j with
    | 0 | 1 | 2 | 3 => rfl
    | _ + 4 => rfl
  lane_splat j hj x := by
    have hj : j < 4 := hj
    interval_cases j <;> rfl
  lane_load j hj words _ := by
    have hj : j < 4 := hj
    interval_cases j <;> rfl
  size_store _ _ h := by simp [store, vst1qU64, h]
  getElem!_store x words h j hj := by
    have hj : j < 4 := hj
    interval_cases j <;> simp [store, vst1qU64, NeonLanes.lane, Array.set!_eq_setIfInBounds,
      Array.size_setIfInBounds, h, MAX_LANES]
  lane_add j hj x y := by
    have hj : j < 4 := hj
    interval_cases j <;> rfl
  lane_xor j hj x y := by
    have hj : j < 4 := hj
    interval_cases j <;> rfl
  lane_xorRotr32 j hj x y := by
    have hj : j < 4 := hj
    interval_cases j <;> simp [xorRotr32, NeonLanes.lane, neonRotr32_eq, Uint64x2.ofWords,
      Uint64x2.word]
  lane_xorRotr24 j hj x y := by
    have hj : j < 4 := hj
    interval_cases j <;> simp [xorRotr24, NeonLanes.lane, neonRotr24_eq, Uint64x2.ofWords,
      Uint64x2.word]
  lane_xorRotr16 j hj x y := by
    have hj : j < 4 := hj
    interval_cases j <;> simp [xorRotr16, NeonLanes.lane, neonRotr16_eq, Uint64x2.ofWords,
      Uint64x2.word]
  lane_xorRotr63 j hj x y := by
    have hj : j < 4 := hj
    interval_cases j <;> simp [xorRotr63, NeonLanes.lane, neonRotr63_eq, Uint64x2.ofWords,
      Uint64x2.word]

/-! ## `compress` lane by lane -/

/-- `compress`'s first loop (lines 235–238): the lanes' second message words. -/
def compressWords (self : Midstate) (blocks : List ℕ) : Array UInt64 := Id.run do
  let mut words : Array UInt64 := Array.replicate MAX_LANES 0
  for (block, j) in blocks.zipIdx do
    words := words.set! j (self.m1Low ||| UInt64.ofNat block <<< 32)
  return words

open Lanes in
/-- `compress`'s message, its state setup and its rounds (lines 239–256). -/
def compressRounds (self : Midstate) (words : Array UInt64) : Array L := Id.run do
  let zero : L := splat 0
  let m0 : L := splat self.m0
  let m1 : L := load words
  let word := fun i => match i with
    | 0 => m0
    | 1 => m1
    | _ => zero
  let mut v := Array.replicate 16 zero
  for i in [0:8] do
    v := v.set! i (splat self.h[i]!)
    v := v.set! (8 + i) (splat IV[i]!)
  v := v.set! 12 (splat (IV[4]! ^^^ self.count))
  v := v.set! 14 (splat (~~~IV[6]!))
  return rounds v word

open Lanes in
/-- `compress`'s last loop (lines 258–265): the digests written from the state. -/
def compressOut (self : Midstate) (v : Array L) (words : Array UInt64) (out : List (List ℕ)) :
    List (List ℕ) := Id.run do
  let mut words := words
  let mut out := out
  for i in [0:8] do
    words := store (xor (splat self.h[i]!) (xor v[i]! v[i + 8]!)) words
    out := (out.zip words.toList).map fun (digest, word) =>
      digest.take (8 * i) ++ u64ToLeBytes word ++ digest.drop (8 * i + 8)
  return out

/-- `compress` is its three phases in turn. -/
theorem Midstate.compress_phases (self : Midstate) (blocks : List ℕ) (out : List (List ℕ)) :
    self.compress (L := L) blocks out =
      compressOut self (compressRounds (L := L) self (compressWords self blocks))
        (compressWords self blocks) out := by
  simp only [Midstate.compress, compressWords, compressRounds, compressOut, Id.run_bind,
    Id.run_pure]
  rfl

/-- The message of one lane: `m0`, `m1`, then zeros. -/
def laneWord (self : Midstate) (m1 : UInt64) : ℕ → UInt64
  | 0 => self.m0
  | 1 => m1
  | _ => 0

/-- One lane's state after the rounds, with second message word `m1`: `compress::<u64>`'s. -/
def laneRounds (self : Midstate) (m1 : UInt64) : Array UInt64 := Id.run do
  let mut v := Array.replicate 16 (0 : UInt64)
  for i in [0:8] do
    v := v.set! i self.h[i]!
    v := v.set! (8 + i) IV[i]!
  v := v.set! 12 (IV[4]! ^^^ self.count)
  v := v.set! 14 (~~~IV[6]!)
  return rounds v (laneWord self m1)

/-- One lane's digest from its state `v`: `compress::<u64>`'s last loop. -/
def laneDigest (self : Midstate) (v : Array UInt64) (digest : List ℕ) : List ℕ := Id.run do
  let mut digest := digest
  for i in [0:8] do
    let word := self.h[i]! ^^^ (v[i]! ^^^ v[i + 8]!)
    digest := digest.take (8 * i) ++ u64ToLeBytes word ++ digest.drop (8 * i + 8)
  return digest

/-- Setting entries from an indexed list: entry `j` gets the value for position `j - k`. -/
theorem foldl_set!_zipIdx (f : ℕ → UInt64) (bs : List ℕ) :
    ∀ (k : ℕ) (words : Array UInt64),
      ((bs.zipIdx k).foldl (fun w (a : ℕ × ℕ) => w.set! a.2 (f a.1)) words).size = words.size ∧
      ∀ j, ((bs.zipIdx k).foldl (fun w (a : ℕ × ℕ) => w.set! a.2 (f a.1)) words)[j]? =
        if k ≤ j ∧ j < k + bs.length ∧ j < words.size then some (f bs[j - k]!) else words[j]? := by
  induction bs with
  | nil =>
    intro k words
    refine ⟨rfl, fun j => ?_⟩
    simp only [List.zipIdx_nil, List.foldl_nil, List.length_nil, Nat.add_zero]
    split_ifs <;> first | rfl | omega
  | cons b bs ih =>
    intro k words
    simp only [List.zipIdx_cons, List.foldl_cons]
    obtain ⟨hs, hg⟩ := ih (k + 1) (words.set! k (f b))
    refine ⟨by rw [hs, Array.size_set!], fun j => ?_⟩
    rw [hg j]
    simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, Array.getElem?_setIfInBounds,
      List.length_cons]
    by_cases hkj : k = j
    · subst hkj
      simp only [Nat.sub_self, List.getElem!_cons_zero]
      split_ifs <;> first | rfl | omega | (symm; exact Array.getElem?_eq_none (by omega))
    · simp only [hkj, ↓reduceIte]
      split_ifs with h1 h2 h2
      · rw [show j - k = j - (k + 1) + 1 by omega, List.getElem!_cons_succ]
      · omega
      · omega
      · rfl

theorem size_compressWords (self : Midstate) (blocks : List ℕ) :
    (compressWords self blocks).size = MAX_LANES := by
  simp only [compressWords, Id.run, List.forIn_pure_yield_eq_foldl]
  show (List.foldl _ (Array.replicate MAX_LANES 0) blocks.zipIdx).size = MAX_LANES
  exact (foldl_set!_zipIdx (fun block => self.m1Low ||| UInt64.ofNat block <<< 32) blocks 0
    _).1.trans Array.size_replicate

/-- Word `j` of `compress`'s words: `m1_low | blocks[j] << 32`, zero past the blocks. -/
theorem getElem!_compressWords (self : Midstate) (blocks : List ℕ) (j : ℕ)
    (hj : j < blocks.length) (hm : j < MAX_LANES) :
    (compressWords self blocks)[j]! = self.m1Low ||| UInt64.ofNat blocks[j]! <<< 32 := by
  simp only [compressWords, Id.run, List.forIn_pure_yield_eq_foldl]
  show (List.foldl _ (Array.replicate MAX_LANES 0) blocks.zipIdx)[j]! = _
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    (foldl_set!_zipIdx (fun block => self.m1Low ||| UInt64.ofNat block <<< 32) blocks 0 _).2 j]
  simp [hj, hm]

/-- **The rounds lane by lane:** lane `j` of the state is the one-lane state for word `j`. -/
theorem proj_compressRounds (V : LaneView L) (j : ℕ) (hj : j < LANES L) (self : Midstate)
    (words : Array UInt64) (hw : words.size = MAX_LANES) :
    V.proj j (compressRounds (L := L) self words) = laneRounds self words[j]! := by
  simp only [compressRounds, laneRounds, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, List.forIn_pure_yield_eq_foldl, Id.run_bind, Id.run_pure, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [V.proj_rounds j hj, V.proj_set!, V.proj_set!, V.lane_splat j hj, V.lane_splat j hj]
  -- `congr` would first try `rfl`, unfolding the rounds.
  apply congrArg₂ rounds
  · refine congrArg (fun v => (Array.set! v 12 _).set! 14 _) ?_
    refine (List.foldl_hom (V.proj j)
      (g₂ := fun (v : Array UInt64) i => (v.set! i self.h[i]!).set! (8 + i) IV[i]!)
      ?_).symm.trans ?_
    · intro v i
      simp only [V.proj_set!, V.lane_splat j hj]
    · rw [V.proj_replicate j hj]
  · funext i
    match i with
    | 0 => exact V.lane_splat j hj _
    | 1 => exact V.lane_load j hj words hw
    | _ + 2 => exact V.lane_splat j hj _

/-- The last loop over any run of positions: each digest, lane by lane. -/
theorem foldl_store_zip (V : LaneView L) (X : ℕ → L) (is : List ℕ) :
    ∀ (words : Array UInt64) (out : List (List ℕ)), words.size = MAX_LANES →
      out.length ≤ LANES L →
      let r := is.foldl (fun (b : Array UInt64 × List (List ℕ)) a =>
        (store (X a) b.1, (b.2.zip (store (X a) b.1).toList).map fun x =>
          x.1.take (8 * a) ++ u64ToLeBytes x.2 ++ x.1.drop (8 * a + 8))) (words, out)
      r.1.size = MAX_LANES ∧ ∀ j, r.2[j]? = out[j]?.map fun d =>
        is.foldl (fun d a => d.take (8 * a) ++ u64ToLeBytes (V.lane (X a) j) ++ d.drop (8 * a + 8))
          d := by
  induction is with
  | nil =>
    intro words out hw _
    exact ⟨hw, fun j => by simp⟩
  | cons a is ih =>
    intro words out hw ho
    simp only [List.foldl_cons]
    have hw' := V.size_store (X a) words hw
    have hlen : ((out.zip (store (X a) words).toList).map fun x =>
        x.1.take (8 * a) ++ u64ToLeBytes x.2 ++ x.1.drop (8 * a + 8)).length = out.length := by
      simp only [List.length_map, List.length_zip, Array.length_toList, hw']
      have := V.lanes_le
      omega
    obtain ⟨hs, hg⟩ := ih (store (X a) words) _ hw' (hlen ▸ ho)
    refine ⟨hs, fun j => ?_⟩
    rw [hg j]
    by_cases hj : j < out.length
    · rw [List.getElem?_eq_getElem (hlen ▸ hj), List.getElem?_eq_getElem hj]
      simp only [Option.map_some, List.getElem_map, List.getElem_zip, Array.getElem_toList]
      have := V.lanes_le
      rw [← getElem!_pos (store (X a) words) j (by omega),
        V.getElem!_store (X a) words hw j (by omega)]
    · rw [List.getElem?_eq_none_iff.mpr (by omega), List.getElem?_eq_none_iff.mpr (by omega)]
      rfl

/-- **The digests lane by lane:** digest `j` is the one-lane digest from lane `j` of the state. -/
theorem getElem?_compressOut (V : LaneView L) (self : Midstate) (v : Array L)
    (words : Array UInt64) (hw : words.size = MAX_LANES) (out : List (List ℕ))
    (ho : out.length ≤ LANES L) (j : ℕ) :
    (compressOut self v words out)[j]? = out[j]?.map fun d => laneDigest self (V.proj j v) d := by
  simp only [compressOut, laneDigest, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, List.forIn_pure_yield_eq_foldl, Id.run_bind, Id.run_pure, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [(foldl_store_zip V (fun i => xor (splat self.h[i]!) (xor v[i]! v[i + 8]!)) _ words out hw
    ho).2 j]
  by_cases hj : j < LANES L
  · simp only [V.lane_xor j hj, V.lane_splat j hj, Lanes.xor_u64, ← V.getElem!_proj]
  · rw [List.getElem?_eq_none_iff.mpr (by omega), Option.map_none, Option.map_none]

/-- **`compress` lane by lane:** with as many blocks as digests, at most `LANES`, digest `j`
    is the one-lane digest of block `j`. -/
theorem Midstate.compress_closed (V : LaneView L) (self : Midstate) (blocks : List ℕ)
    (out : List (List ℕ)) (hbo : blocks.length = out.length) (ho : out.length ≤ LANES L)
    (j : ℕ) :
    (self.compress (L := L) blocks out)[j]? = out[j]?.map
      (laneDigest self (laneRounds self (self.m1Low ||| UInt64.ofNat blocks[j]! <<< 32))) := by
  rw [Midstate.compress_phases, getElem?_compressOut V _ _ _ (size_compressWords self blocks) _ ho]
  by_cases hj : j < out.length
  · have := V.lanes_le
    rw [proj_compressRounds V j (by omega) self _ (size_compressWords self blocks),
      getElem!_compressWords self blocks j (by omega) (by omega)]
  · rw [List.getElem?_eq_none_iff.mpr (by omega)]
    rfl

/-- **One lane:** `compress::<u64>` on one block and one digest. -/
theorem Midstate.compress_u64 (self : Midstate) (block : ℕ) (digest : List ℕ) :
    self.compress (L := UInt64) [block] [digest] =
      [laneDigest self (laneRounds self (self.m1Low ||| UInt64.ofNat block <<< 32)) digest] := by
  have h := Midstate.compress_closed u64View self [block] [digest] rfl (Nat.le_refl _)
  have h1 := h 1
  have h0 := h 0
  simp only [List.getElem!_cons_zero, List.getElem?_cons_zero, Option.map_some,
    List.getElem?_cons_succ, List.getElem?_nil, Option.map_none] at h0 h1
  match hc : self.compress (L := UInt64) [block] [digest] with
  | [] => simp [hc] at h0
  | [d] => simp only [hc, List.getElem?_cons_zero, Option.some.injEq] at h0; rw [h0]
  | _ :: _ :: _ => simp [hc] at h1

/-- **Every kernel computes the portable kernel's digests:** on `LANES` blocks and digests,
    `compress` on `L` is `compress_portable`. -/
theorem Midstate.compress_eq_portable (V : LaneView L) (self : Midstate) (blocks : List ℕ)
    (out : List (List ℕ)) (hb : blocks.length = LANES L) (ho : out.length = LANES L) :
    self.compress (L := L) blocks out = self.compressPortable blocks out := by
  apply List.ext_getElem?
  intro j
  rw [Midstate.compress_closed V self blocks out (hb.trans ho.symm) ho.le j]
  simp only [Midstate.compressPortable, Midstate.compress_u64]
  rw [show (fun (x : ℕ × List ℕ) => [laneDigest self
      (laneRounds self (self.m1Low ||| UInt64.ofNat x.1 <<< 32)) x.2]) =
      fun x => [(fun (x : ℕ × List ℕ) => laneDigest self
        (laneRounds self (self.m1Low ||| UInt64.ofNat x.1 <<< 32)) x.2) x] from rfl,
    ← List.map_eq_flatMap, List.getElem?_map, List.zip_eq_zipWith, List.getElem?_zipWith]
  by_cases hj : j < out.length
  · rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem (by omega : j < blocks.length),
      getElem!_pos blocks j (by omega)]
    rfl
  · rw [List.getElem?_eq_none_iff.mpr (by omega), List.getElem?_eq_none_iff.mpr (by omega)]
    rfl

/-! ## `LeafHasher::hash` under every kernel -/

/-- `compress_portable` on concatenations. -/
theorem Midstate.compressPortable_append (self : Midstate) (b₁ b₂ : List ℕ)
    (d₁ d₂ : List (List ℕ)) (h : b₁.length = d₁.length) :
    self.compressPortable (b₁ ++ b₂) (d₁ ++ d₂) =
      self.compressPortable b₁ d₁ ++ self.compressPortable b₂ d₂ := by
  simp only [Midstate.compressPortable, List.zip_append h, List.flatMap_append]

/-- A kernel's chunk hash. -/
def Kernel.compress (kernel : Kernel) (midstate : Midstate) (blocks : List ℕ)
    (out : List (List ℕ)) : List (List ℕ) :=
  match kernel with
  | .portable => midstate.compressPortable blocks out
  | .avx2 => compressAvx2 midstate blocks out
  | .neon => compressNeon midstate blocks out
  | .neonSha3 => compressNeonSha3 midstate blocks out

/-- Each kernel, on a chunk of its lane count, computes `compress_portable`. -/
theorem Kernel.compress_eq_portable (kernel : Kernel) (midstate : Midstate) (blocks : List ℕ)
    (out : List (List ℕ)) (hb : blocks.length = kernel.lanes) (ho : out.length = kernel.lanes) :
    kernel.compress midstate blocks out = midstate.compressPortable blocks out := by
  cases kernel
  · rfl
  · exact Midstate.compress_eq_portable avx2View midstate blocks out hb ho
  · exact Midstate.compress_eq_portable (neonView false) midstate blocks out hb ho
  · exact Midstate.compress_eq_portable (neonView true) midstate blocks out hb ho

/-- Chunks of `lanes` blocks and digests, each hashed by `F`, which on such chunks computes
    `compress_portable`, and joined: `compress_portable` of the whole, when the whole is a
    multiple of `lanes`. -/
theorem flatMap_chunks_compress (midstate : Midstate) (lanes : ℕ) (hl : 1 ≤ lanes)
    (F : List ℕ × List (List ℕ) → List (List ℕ))
    (hF : ∀ p : List ℕ × List (List ℕ), p.1.length = lanes → p.2.length = lanes →
      F p = midstate.compressPortable p.1 p.2) (bs : List ℕ) :
    ∀ ds : List (List ℕ), bs.length = ds.length → lanes ∣ bs.length →
      ((chunksSucc (lanes - 1) bs).zip (chunksSucc (lanes - 1) ds)).flatMap F =
        midstate.compressPortable bs ds := by
  induction h : bs.length using Nat.strong_induction_on generalizing bs with
  | _ n ih =>
    intro ds hbd hdvd
    subst h
    rcases bs with _ | ⟨b, bs⟩
    · rcases ds with _ | ⟨d, ds⟩
      · rw [chunksSucc, List.zip_nil_left, List.flatMap_nil]
        rfl
      · exact absurd hbd (by simp)
    · rcases ds with _ | ⟨d, ds⟩
      · exact absurd hbd (by simp)
      · rw [chunksSucc, chunksSucc, List.zip_cons_cons, List.flatMap_cons]
        have hlen : lanes ≤ (b :: bs).length := Nat.le_of_dvd (by simp) hdvd
        have hdvd' : lanes ∣ ((b :: bs).drop (lanes - 1 + 1)).length := by
          rw [List.length_drop, Nat.sub_add_cancel hl]
          exact Nat.dvd_sub hdvd (dvd_refl _)
        rw [ih _ (by simp only [List.length_drop]; omega) _ rfl _
            (by simp only [List.length_drop, hbd]) hdvd',
          hF _ (by simp only [List.length_take]; omega) (by simp only [List.length_take]; omega),
          ← Midstate.compressPortable_append _ _ _ _ _
            (by simp only [List.length_take]; omega),
          List.take_append_drop, List.take_append_drop]

/-- **`LeafHasher::hash` under every kernel** is the portable kernel's digests, each with its
    bytes past the digest length zero. -/
theorem LeafHasher.hash?_eq (lh : LeafHasher) (blocks : List ℕ) (out : List (List ℕ))
    (hl : blocks.length = out.length) :
    lh.hash? blocks out = some ((lh.midstate.compressPortable blocks out).map fun digest =>
      digest.take lh.hashLen ++ List.replicate (digest.length - lh.hashLen) 0) := by
  have hl1 : 1 ≤ lh.kernel.lanes := by cases lh.kernel <;> decide
  simp only [LeafHasher.hash?, hl, guard_true, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some, Option.some.injEq]
  rw [flatMap_chunks_compress lh.midstate lh.kernel.lanes hl1 _ ?_ _ _ (by simp [hl])
    (by rw [List.length_take, hl, min_eq_left (Nat.div_mul_le_self _ _)]
        exact Nat.dvd_mul_left _ _),
    ← Midstate.compressPortable_append _ _ _ _ _ (by simp [hl]), List.take_append_drop,
    List.take_append_drop]
  intro p h1 h2
  exact Kernel.compress_eq_portable lh.kernel lh.midstate p.1 p.2 h1 h2

end Equihash.Verifier
