/-
`blake2b_simd 1.0.4` computes RFC 7693's BLAKE2b: its compression loops, each implementation's
`compress_block`, and `State`'s buffering.
-/
module

public import Equihash.Verifier.Blake2bSimd
public import Equihash.Proofs.Blake2b

@[expose] public section

namespace Equihash.Verifier.Blake2b

/-! ## The compression loop -/

/-- `finalize`'s loop: at most one block of input, compressed once, zero-padded and flagged. -/
theorem compress1Loop_final
    (f : List ℕ → Array UInt64 → ℕ → UInt64 → UInt64 → Array UInt64) (input : List ℕ)
    (h : input.length ≤ BLOCKBYTES) (words : Array UInt64) (count : ℕ) :
    compress1Loop f input words count true =
      f (input ++ List.replicate (BLOCKBYTES - input.length) 0) words
        ((count + input.length) % 2 ^ 128) (flagWord true) (flagWord false) := by
  have h0 : (input.length - 1) - (input.length - 1) % BLOCKBYTES = 0 := by
    simp only [BLOCKBYTES] at h ⊢; omega
  simp only [compress1Loop, h0, finalBlock, Nat.zero_div, zero_add, List.range_one,
    List.foldl_cons, List.foldl_nil, Nat.mul_zero, List.drop_zero, ite_true]
  by_cases hb : input.length ≥ BLOCKBYTES
  · have : input.length = BLOCKBYTES := by omega
    simp [this, List.take_of_length_le (Nat.le_of_eq this)]
  · simp [hb]

/-- `update`'s loop: `k` whole blocks, each compressed in turn, none flagged. -/
theorem compress1Loop_blocks
    (f : List ℕ → Array UInt64 → ℕ → UInt64 → UInt64 → Array UInt64) (input : List ℕ) (k : ℕ)
    (hk : 0 < k) (h : input.length = BLOCKBYTES * k) (words : Array UInt64) (count : ℕ) :
    compress1Loop f input words count false =
      ((List.range k).foldl (fun s j =>
        (f ((input.drop (BLOCKBYTES * j)).take BLOCKBYTES) s.1 ((s.2 + BLOCKBYTES) % 2 ^ 128)
          (flagWord false) (flagWord false), (s.2 + BLOCKBYTES) % 2 ^ 128)) (words, count)).1 := by
  have hfin : (input.length - 1) - (input.length - 1) % BLOCKBYTES = BLOCKBYTES * (k - 1) := by
    simp only [BLOCKBYTES] at h ⊢; omega
  have hn : BLOCKBYTES * (k - 1) / BLOCKBYTES + 1 = k := by simp only [BLOCKBYTES]; omega
  have hlast : (input.drop (min (BLOCKBYTES * (k - 1)) input.length)).length ≥ BLOCKBYTES := by
    simp only [List.length_drop, BLOCKBYTES] at h ⊢; omega
  simp only [compress1Loop, hfin, hn, finalBlock, hlast, ite_true]
  congr 1
  apply List.foldl_ext
  intro s j _
  by_cases hj : BLOCKBYTES * j = BLOCKBYTES * (k - 1)
  · have hmin : min (BLOCKBYTES * (k - 1)) input.length = BLOCKBYTES * j := by
      simp only [BLOCKBYTES] at h hj ⊢; omega
    simp [hj, hmin]
  · simp [hj]

/-! ## The portable `compress_block` -/

/-- The portable `g` is the leaf-hashing kernels' `g`. -/
theorem portable_g_eq : Portable.g = LeafHash.g (L := UInt64) := rfl

/-- `SIGMA` is the leaf-hashing kernels'. -/
theorem SIGMA_eq_leafHash : SIGMA = LeafHash.SIGMA := rfl

/-- The portable `round` is a round of `LeafHash.rounds`, on the message words `m`. -/
theorem portable_rounds_eq (v m : Array UInt64) (word : ℕ → UInt64)
    (hm : ∀ i < 16, m[i]! = word i) :
    (List.range 12).foldl (fun v r => Portable.round r m v) v = LeafHash.rounds v word := by
  simp only [LeafHash.rounds, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, List.forIn_pure_yield_eq_foldl, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one, ← List.range_eq_range']
  apply List.foldl_ext
  intro v r hr
  rw [List.mem_range] at hr
  have hs := sigma_lt r hr
  rw [Portable.round, SIGMA_eq_leafHash, portable_g_eq]
  simp only [hm _ (hs 0 (by omega)), hm _ (hs 1 (by omega)), hm _ (hs 2 (by omega)),
    hm _ (hs 3 (by omega)), hm _ (hs 4 (by omega)), hm _ (hs 5 (by omega)),
    hm _ (hs 6 (by omega)), hm _ (hs 7 (by omega)), hm _ (hs 8 (by omega)),
    hm _ (hs 9 (by omega)), hm _ (hs 10 (by omega)), hm _ (hs 11 (by omega)),
    hm _ (hs 12 (by omega)), hm _ (hs 13 (by omega)), hm _ (hs 14 (by omega)),
    hm _ (hs 15 (by omega)), SIGMA_eq r hr]

/-- The portable `compress_block`'s first state is RFC 7693's: the words, `IV`, the count, and
    the final-block flag. -/
theorem portable_init_eq (words : Array UInt64) (hw : words.size = 8) (count : ℕ) (last : Bool) :
    words ++ #[IV[0]!, IV[1]!, IV[2]!, IV[3]!, IV[4]! ^^^ countLow count,
      IV[5]! ^^^ countHigh count, IV[6]! ^^^ flagWord last, IV[7]! ^^^ flagWord false] =
    (let v := words ++ iv
     let v := v.set! 12 (v[12]! ^^^ UInt64.ofNat count)
     let v := v.set! 13 (v[13]! ^^^ UInt64.ofNat (count / 2 ^ 64))
     if last then v.set! 14 (~~~v[14]!) else v) := by
  apply Array.ext_getElem?
  intro i
  by_cases hi : i < 16
  · interval_cases i <;> cases last <;>
      simp [hw, iv, IV, countLow, countHigh, flagWord, Array.set!_eq_setIfInBounds]
  · cases last <;>
      (rw [Array.getElem?_eq_none, Array.getElem?_eq_none] <;>
        simp [hw, iv, Array.set!_eq_setIfInBounds] <;> omega)

/-- **The portable `compress_block` is RFC 7693's compression.** -/
theorem portable_compressBlock_eq (block : List ℕ) (words : Array UInt64) (hw : words.size = 8)
    (count : ℕ) (last : Bool) :
    Portable.compressBlock block words count (flagWord last) (flagWord false) =
      compress words block count last := by
  rw [compress_eq]
  simp only [Portable.compressBlock]
  rw [portable_init_eq words hw count last, portable_rounds_eq _ _ (word block) fun i hi => by
    rw [getElem!_words _ hi, u64FromLeBytes_eq_word]]

/-! ## `State` -/

/-- An implementation whose `compress_block` is RFC 7693's compression. -/
def CompressOk (f : List ℕ → Array UInt64 → ℕ → UInt64 → UInt64 → Array UInt64) : Prop :=
  ∀ block (words : Array UInt64), words.size = 8 → ∀ count last,
    f block words count (flagWord last) (flagWord false) = compress words block count last

/-- The portable `compress_block` is RFC 7693's compression. -/
theorem compressOk_portable : CompressOk Portable.compressBlock :=
  fun block words hw count last => portable_compressBlock_eq block words hw count last

/-- RFC 7693's state after blocks `0 … k − 1` of `x`, none final, from `h`. -/
def prefixWords (h : Array UInt64) (x : List ℕ) (k : ℕ) : Array UInt64 :=
  (List.range k).foldl (fun h i => compress h ((x.drop (128 * i)).take 128) (128 * (i + 1)) false) h

/-- One block more. -/
theorem prefixWords_succ (h : Array UInt64) (x : List ℕ) (k : ℕ) :
    prefixWords h x (k + 1) =
      compress (prefixWords h x k) ((x.drop (128 * k)).take 128) (128 * (k + 1)) false := by
  simp [prefixWords, List.range_succ, List.foldl_append]

/-- The state stays 8 words. -/
theorem size_prefixWords (h : Array UInt64) (hh : h.size = 8) (x : List ℕ) (k : ℕ) :
    (prefixWords h x k).size = 8 := by
  cases k with
  | zero => simpa [prefixWords] using hh
  | succ k => rw [prefixWords_succ]; exact size_compress _ _ _ _

/-- Blocks past the first `k` do not change the state after `k` blocks. -/
theorem prefixWords_append (h : Array UInt64) (x y : List ℕ) (k : ℕ) (hk : 128 * k ≤ x.length) :
    prefixWords h (x ++ y) k = prefixWords h x k := by
  simp only [prefixWords]
  apply List.foldl_ext
  intro h i hi
  rw [List.mem_range] at hi
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length
    (by simp; omega)]

/-- `st` represents the bytes `z`, for an `ℓ`-byte digest personalized by `p`: the count is the
    whole blocks compressed, the buffer the bytes after them, the words RFC 7693's state after
    those blocks. -/
structure Rep (ℓ : ℕ) (p z : List ℕ) (st : State) : Prop where
  hashLength : st.hashLength = ℓ
  buf_length : st.buf.length = 128
  buflen_le : st.buflen ≤ 128
  count : st.count + st.buflen = z.length
  count_dvd : 128 ∣ st.count
  buf : st.buf.take st.buflen = z.drop st.count
  words : st.words = prefixWords (initState ℓ p) z (st.count / 128)

/-- `st` has absorbed `z`: it represents `z`, and holds back at least one byte of it. -/
structure Absorbed (ℓ : ℕ) (p z : List ℕ) (st : State) : Prop extends Rep ℓ p z st where
  buflen_pos : z ≠ [] → 0 < st.buflen

/-- RFC 7693's initial state is 8 words. -/
theorem size_initState (ℓ : ℕ) (p : List ℕ) : (initState ℓ p).size = 8 := by
  simp [initState, iv]

/-- A represented state has 8 words. -/
theorem Rep.size_words {ℓ : ℕ} {p z : List ℕ} {st : State} (h : Rep ℓ p z st) :
    st.words.size = 8 := by
  rw [h.words]; exact size_prefixWords _ (size_initState ℓ p) _ _

/-- `fill_buf` moves as much of `y` as fits into the buffer. -/
theorem Rep.fillBuf {ℓ : ℕ} {p z : List ℕ} {st : State} (h : Rep ℓ p z st) (y : List ℕ) :
    Rep ℓ p (z ++ y.take (min (BLOCKBYTES - st.buflen) y.length)) (st.fillBuf y).1 := by
  obtain ⟨hl, hb, hle, hc, hd, hbuf, hw⟩ := h
  have ht : (y.take (min (BLOCKBYTES - st.buflen) y.length)).length =
      min (BLOCKBYTES - st.buflen) y.length := by simp
  simp only [BLOCKBYTES] at ht ⊢
  refine ⟨hl, ?_, ?_, ?_, hd, ?_, ?_⟩
  · simp [State.fillBuf, BLOCKBYTES, hb]; omega
  · simp [State.fillBuf, BLOCKBYTES]; omega
  · simp [State.fillBuf, BLOCKBYTES, ht]; omega
  · simp only [State.fillBuf, BLOCKBYTES]
    rw [List.take_left' (by simp [hb]; omega), hbuf, List.drop_append_of_le_length (by omega)]
  · simp only [State.fillBuf, hw]
    exact (prefixWords_append _ _ _ _ (by omega)).symm

/-- A full buffer, compressed, becomes the next block of the state. -/
theorem Rep.compressBuf {ℓ : ℕ} {p z : List ℕ} {st : State}
    (ok : CompressOk st.implementation.compressBlock) (h : Rep ℓ p z st)
    (hfull : st.buflen = BLOCKBYTES) (hz : z.length < 2 ^ 128) :
    Rep ℓ p z
      { st with
        words := st.implementation.compress1Loop st.buf st.words st.count false
        count := (st.count + BLOCKBYTES) % 2 ^ 128
        buflen := 0 } := by
  have hws := h.size_words
  obtain ⟨hl, hb, hle, hc, hd, hbuf, hw⟩ := h
  simp only [BLOCKBYTES] at hfull ⊢
  have hmod : (st.count + 128) % 2 ^ 128 = st.count + 128 := Nat.mod_eq_of_lt (by omega)
  obtain ⟨k, hk⟩ := hd
  have htake : st.buf.take 128 = st.buf := List.take_of_length_le (by rw [hb])
  have hbuf' : st.buf = (z.drop (128 * k)).take 128 := by
    rw [← hk, ← hbuf, hfull, List.take_take, Nat.min_self, htake]
  refine ⟨hl, hb, by simp only; omega, by simp only; rw [hmod]; omega,
    ⟨k + 1, by simp only; rw [hmod, hk]; ring⟩, ?_, ?_⟩
  · simp only [List.take_zero, hmod]
    rw [List.drop_eq_nil_of_le (by omega)]
  · simp only [Implementation.compress1Loop]
    rw [compress1Loop_blocks _ _ 1 (by omega) (by simp [hb, BLOCKBYTES]), hmod]
    simp only [List.range_one, List.foldl_cons, List.foldl_nil, BLOCKBYTES, Nat.mul_zero,
      List.drop_zero, List.take_of_length_le (show st.buf.length ≤ 128 by omega)]
    rw [ok _ _ hws, hmod, hw, hk, show (128 * k + 128) / 128 = k + 1 by omega,
      show 128 * k / 128 = k by omega, prefixWords_succ, hbuf']
    ring_nf

/-- The loop over `j` whole blocks of `w`, after `k` blocks of `z` (`z`'s length): the state after
    `k + j` blocks of `z ++ w`. -/
theorem foldl_blocks (f : List ℕ → Array UInt64 → ℕ → UInt64 → UInt64 → Array UInt64)
    (ok : CompressOk f) (h0 : Array UInt64) (hh : h0.size = 8) (z w : List ℕ) (k : ℕ)
    (hz : z.length = 128 * k) (j : ℕ) (hj : 128 * (k + j) < 2 ^ 128) :
    (List.range j).foldl (fun s i =>
        (f ((w.drop (BLOCKBYTES * i)).take BLOCKBYTES) s.1 ((s.2 + BLOCKBYTES) % 2 ^ 128)
          (flagWord false) (flagWord false), (s.2 + BLOCKBYTES) % 2 ^ 128))
      (prefixWords h0 z k, 128 * k) = (prefixWords h0 (z ++ w) (k + j), 128 * (k + j)) := by
  induction j with
  | zero => simp [prefixWords_append _ _ _ _ (by omega : 128 * k ≤ z.length)]
  | succ j ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil, BLOCKBYTES]
    have hmod : (128 * (k + j) + 128) % 2 ^ 128 = 128 * (k + j + 1) := by
      rw [Nat.mod_eq_of_lt (by omega)]; ring
    rw [hmod, ok _ _ (size_prefixWords _ hh _ _), ← Nat.add_assoc, prefixWords_succ]
    congr 2
    rw [show 128 * (k + j) = z.length + 128 * j by omega, List.drop_append,
      List.drop_eq_nil_of_le (show z.length ≤ z.length + 128 * j by omega), List.nil_append,
      Nat.add_sub_cancel_left]

/-- `k` whole blocks, compressed after a state with an empty buffer, are its next `k` blocks. -/
theorem Rep.compressBlocks {ℓ : ℕ} {p z : List ℕ} {st : State}
    (ok : CompressOk st.implementation.compressBlock) (h : Rep ℓ p z st) (hempty : st.buflen = 0)
    (w : List ℕ) (m : ℕ) (hm : 0 < m) (hw : w.length = BLOCKBYTES * m)
    (hzw : z.length + w.length < 2 ^ 128) :
    Rep ℓ p (z ++ w)
      { st with
        words := st.implementation.compress1Loop w st.words st.count false
        count := (st.count + BLOCKBYTES * m) % 2 ^ 128 } := by
  obtain ⟨hl, hb, hle, hc, hd, hbuf, hw'⟩ := h
  obtain ⟨k, hk⟩ := hd
  simp only [BLOCKBYTES] at hw ⊢
  have hz : z.length = 128 * k := by omega
  have hmod : (st.count + 128 * m) % 2 ^ 128 = 128 * (k + m) := by
    rw [Nat.mod_eq_of_lt (by omega), hk]; ring
  refine ⟨hl, hb, by simp only; omega, by simp only; rw [hmod]; simp; omega,
    ⟨k + m, by simp only; rw [hmod]⟩, ?_, ?_⟩
  · simp only [hempty, List.take_zero, hmod]
    rw [List.drop_eq_nil_of_le (by simp; omega)]
  · simp only [Implementation.compress1Loop]
    rw [compress1Loop_blocks _ _ m hm (by simp [BLOCKBYTES, hw]), hw', hk,
      show 128 * k / 128 = k by omega, foldl_blocks _ ok _ (size_initState ℓ p) z w k hz m
        (by omega), show (128 * k + 128 * m) % 2 ^ 128 / 128 = k + m by
          rw [Nat.mod_eq_of_lt (by omega)]; omega]

/-- `fill_buf` keeps the implementation. -/
theorem fillBuf_implementation (st : State) (y : List ℕ) :
    (st.fillBuf y).1.implementation = st.implementation := rfl

/-- `fill_buf`'s buffer length. -/
theorem fillBuf_buflen (st : State) (y : List ℕ) :
    (st.fillBuf y).1.buflen = st.buflen + min (BLOCKBYTES - st.buflen) y.length := rfl

/-- What `fill_buf` leaves of `y`. -/
theorem fillBuf_rest (st : State) (y : List ℕ) :
    (st.fillBuf y).2 = y.drop (min (BLOCKBYTES - st.buflen) y.length) := rfl

/-- `compress_buffer_if_possible`: the state represents a first part `y₀` of `y` more, and when
    the rest `y₁` is not empty, the buffer is. -/
theorem Absorbed.compressBufferIfPossible {ℓ : ℕ} {p x : List ℕ} {st : State}
    (ok : CompressOk st.implementation.compressBlock) (h : Absorbed ℓ p x st) (y : List ℕ)
    (hxy : x.length + y.length < 2 ^ 128) :
    ∃ y₀, y₀ ++ (st.compressBufferIfPossible y).2 = y ∧
      Rep ℓ p (x ++ y₀) (st.compressBufferIfPossible y).1 ∧
      ((st.compressBufferIfPossible y).2 ≠ [] → (st.compressBufferIfPossible y).1.buflen = 0) ∧
      (x ++ y₀ ≠ [] → (st.compressBufferIfPossible y).2 = [] →
        0 < (st.compressBufferIfPossible y).1.buflen) ∧
      (st.compressBufferIfPossible y).1.implementation = st.implementation := by
  by_cases hb : st.buflen > 0
  · set t := min (BLOCKBYTES - st.buflen) y.length with ht
    have hfill := h.toRep.fillBuf y
    by_cases hrest : (st.fillBuf y).2 = []
    · refine ⟨y.take t, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [State.compressBufferIfPossible, hb, ↓reduceIte, hrest, ne_eq, not_true_eq_false]
      · rw [← hrest, fillBuf_rest, List.take_append_drop]
      · exact hfill
      · simp
      · intro _ _; rw [fillBuf_buflen]; omega
      · exact fillBuf_implementation st y
    · have hfull : (st.fillBuf y).1.buflen = BLOCKBYTES := by
        rw [fillBuf_rest, List.drop_eq_nil_iff] at hrest
        rw [fillBuf_buflen]; simp only [BLOCKBYTES] at hrest ⊢; have := h.buflen_le; omega
      refine ⟨y.take t, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [State.compressBufferIfPossible, hb, ↓reduceIte, hrest, ne_eq, not_false_eq_true]
      · rw [fillBuf_rest, List.take_append_drop]
      · exact hfill.compressBuf (by rwa [fillBuf_implementation]) hfull
          (by have := hfill.count; simp at this ⊢; omega)
      · simp
      · intro _ h; exact h.elim
      · rfl
  · refine ⟨[], ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [State.compressBufferIfPossible, hb, ↓reduceIte, List.append_nil, List.nil_append]
    · exact h.toRep
    · intro _; omega
    · intro hx _; exact absurd (h.buflen_pos hx) hb

/-- `Rep` for equal byte sequences. -/
theorem Rep.congr {ℓ : ℕ} {p z z' : List ℕ} {st : State} (h : Rep ℓ p z st) (hz : z = z') :
    Rep ℓ p z' st := hz ▸ h

/-- **`update` absorbs its input.** -/
theorem Absorbed.update {ℓ : ℕ} {p x : List ℕ} {st : State}
    (ok : CompressOk st.implementation.compressBlock) (h : Absorbed ℓ p x st) (y : List ℕ)
    (hxy : x.length + y.length < 2 ^ 128) :
    Absorbed ℓ p (x ++ y) (st.update y) ∧ (st.update y).implementation = st.implementation := by
  obtain ⟨y₀, hy, hrep, hempty, hpos, himpl⟩ := h.compressBufferIfPossible ok y hxy
  generalize hc : st.compressBufferIfPossible y = c at hy hrep hempty hpos himpl
  obtain ⟨s₁, y₁⟩ := c
  simp only at hy hrep hempty hpos himpl
  have ok₁ : CompressOk s₁.implementation.compressBlock := by rwa [himpl]
  have hlen : (x ++ y₀).length + y₁.length < 2 ^ 128 := by
    rw [← hy] at hxy; simp at hxy ⊢; omega
  simp only [State.update, hc]
  by_cases he : (y₁.length - 1) - (y₁.length - 1) % BLOCKBYTES > 0
  · simp only [he, ↓reduceIte]
    have hne : y₁ ≠ [] := by intro h; simp [h] at he
    set e := (y₁.length - 1) - (y₁.length - 1) % BLOCKBYTES with he'
    have hm : e = BLOCKBYTES * (e / BLOCKBYTES) := by simp only [he', BLOCKBYTES]; omega
    have hep : 0 < e / BLOCKBYTES := by
      have := hm; simp only [BLOCKBYTES] at this he ⊢; omega
    have hel : e ≤ y₁.length := by simp only [he', BLOCKBYTES]; omega
    have h₂ := hrep.compressBlocks ok₁ (hempty hne) (y₁.take e) (e / BLOCKBYTES) hep
      (by simp only [List.length_take]; omega) (by simp only [List.length_take]; omega)
    rw [← hm] at h₂
    have hrest : (y₁.drop e).length ≤ BLOCKBYTES := by
      simp only [List.length_drop, he', BLOCKBYTES]; omega
    have h₃ := h₂.fillBuf (y₁.drop e)
    have htake : ∀ b, b = 0 →
        (y₁.drop e).take (min (BLOCKBYTES - b) (y₁.drop e).length) = y₁.drop e := by
      intro b hb; subst hb
      exact List.take_of_length_le (by rw [Nat.sub_zero]; exact Nat.le_min.mpr ⟨hrest, le_refl _⟩)
    rw [htake _ (by exact hempty hne)] at h₃
    refine ⟨⟨h₃.congr (z' := x ++ y) (by rw [← hy, List.append_assoc (x ++ y₀),
      List.take_append_drop, List.append_assoc]), fun _ => ?_⟩, ?_⟩
    · rw [fillBuf_buflen]; simp only [hempty hne, Nat.sub_zero, Nat.min_eq_right hrest]
      simp only [List.length_drop, he', BLOCKBYTES]; omega
    · rw [fillBuf_implementation]; exact himpl
  · simp only [he, ↓reduceIte]
    have hsmall : y₁.length ≤ BLOCKBYTES := by simp only [BLOCKBYTES] at he ⊢; omega
    have h₃ := hrep.fillBuf y₁
    by_cases hne : y₁ = []
    · subst hne
      simp only [List.append_nil] at hy
      subst hy
      refine ⟨⟨h₃.congr (z' := x ++ y₀) (by simp), fun hx => ?_⟩, ?_⟩
      · rw [fillBuf_buflen]; have := hpos (by simpa using hx) rfl; omega
      · rw [fillBuf_implementation]; exact himpl
    · simp only [hempty hne, Nat.sub_zero, Nat.min_eq_right hsmall, List.take_of_length_le
        (le_refl _)] at h₃
      refine ⟨⟨h₃.congr (z' := x ++ y) (by rw [← hy, List.append_assoc]), fun _ => ?_⟩, ?_⟩
      · rw [fillBuf_buflen]; simp only [hempty hne, Nat.sub_zero, Nat.min_eq_right hsmall]
        have := List.length_pos_of_ne_nil hne; omega
      · rw [fillBuf_implementation]; exact himpl

/-! ## `finalize` -/

/-- `state_words_to_bytes` is RFC 7693's output bytes. -/
theorem stateWordsToBytes_eq (W : Array UInt64) :
    stateWordsToBytes W =
      (List.range 64).map fun q => (W[q / 8]! >>> UInt64.ofNat (8 * (q % 8))).toNat % 256 := by
  simp [stateWordsToBytes, u64ToLeBytes, List.range_succ]

/-- Zero bytes past a block's end are no message bytes. -/
theorem word_append_zeros (b : List ℕ) (n i : ℕ) : word (b ++ List.replicate n 0) i = word b i := by
  simp only [word]
  apply List.foldr_ext
  intro j _ w
  congr 2
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h
  · rfl
  · simp only [List.getElem?_replicate]
    split_ifs <;> simp [List.getElem?_eq_none (show b.length ≤ 8 * i + j by omega)]

/-- Zero padding does not change a compression. -/
theorem compress_append_zeros (h : Array UInt64) (b : List ℕ) (n t : ℕ) (last : Bool) :
    compress h (b ++ List.replicate n 0) t last = compress h b t last := by
  have hr : ∀ v, LeafHash.rounds v (word (b ++ List.replicate n 0)) = LeafHash.rounds v (word b) :=
    fun v => rounds_congr v fun i _ => word_append_zeros b n i
  simp only [compress_eq, hr]

/-- RFC 7693's final state: the whole blocks but the last, then the last, flagged. -/
theorem finalState_eq (ℓ : ℕ) (p x : List ℕ) :
    finalState ℓ p x =
      compress (prefixWords (initState ℓ p) x (max 1 ((x.length + 127) / 128) - 1))
        ((x.drop (128 * (max 1 ((x.length + 127) / 128) - 1))).take 128) x.length true := by
  set N := max 1 ((x.length + 127) / 128) with hN
  have hN1 : N = N - 1 + 1 := by omega
  simp only [finalState, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, pure_bind, Id.run_pure, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one, ← hN]
  rw [hN1, List.range'_1_concat, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, Nat.zero_add, beq_self_eq_true, ↓reduceIte,
    ← hN1, prefixWords, List.range_eq_range']
  congr 1
  apply List.foldl_ext
  intro h i hi
  simp only [List.mem_range'_1] at hi
  have : (i + 1 == N) = false := by simp; omega
  simp [this]

/-- `to_words` is RFC 7693's initial state. -/
theorem toWords_eq (params : Params) :
    params.toWords = initState params.hashLength params.personal := by
  apply Array.ext_getElem?
  intro i
  by_cases hi : i < 8
  · interval_cases i <;>
      simp [Params.toWords, initState, iv, IV, Array.set!_eq_setIfInBounds,
        ← u64FromLeBytes_eq_word, UInt64.xor_assoc]
    · rw [UInt64.xor_comm (UInt64.ofNat _), ← UInt64.xor_assoc]
      congr 1
  · rw [Array.getElem?_eq_none, Array.getElem?_eq_none] <;>
      simp [Params.toWords, initState, iv, Array.set!_eq_setIfInBounds] <;> omega

/-- **`finalize` is RFC 7693's BLAKE2b of the bytes absorbed.** -/
theorem Absorbed.finalize {ℓ : ℕ} {p x : List ℕ} {st : State}
    (ok : CompressOk st.implementation.compressBlock) (h : Absorbed ℓ p x st) (hℓ : ℓ ≤ 64)
    (hx : x.length < 2 ^ 128) : st.finalize = blake2b ℓ p x := by
  have hws := h.size_words
  obtain ⟨⟨hl, hb, hle, hc, hd, hbuf, hw⟩, hpos⟩ := h
  obtain ⟨k, hk⟩ := hd
  have hN : max 1 ((x.length + 127) / 128) - 1 = k := by
    by_cases hx0 : x = []
    · subst hx0; simp only [List.length_nil] at hc ⊢; omega
    · have := hpos hx0; omega
  have hblock : (x.drop (128 * k)).take 128 = x.drop (128 * k) :=
    List.take_of_length_le (by simp; omega)
  have htake : (st.buf.take st.buflen).length = st.buflen := by simp [hb]; omega
  simp only [State.finalize, Implementation.compress1Loop]
  rw [compress1Loop_final _ _ (by rw [htake]; exact hle), ok _ _ hws, htake,
    show (st.count + st.buflen) % 2 ^ 128 = x.length by rw [hc]; exact Nat.mod_eq_of_lt hx,
    hbuf, compress_append_zeros, blake2b, finalState_eq, hN, stateWordsToBytes_eq, hl,
    take_map_range _ _ hℓ, hw, hk, show 128 * k / 128 = k by omega, hblock]

/-- `Params::to_state`: nothing absorbed. -/
theorem Params.toState_absorbed (params : Params) :
    Absorbed params.hashLength params.personal [] params.toState :=
  ⟨⟨rfl, by simp [Params.toState, BLOCKBYTES], by simp [Params.toState],
    by simp [Params.toState], by simp [Params.toState], by simp [Params.toState],
    by simp [Params.toState, prefixWords, toWords_eq]⟩, by simp⟩

/-- `update`s in turn absorb their inputs. -/
theorem Absorbed.foldl_update {ℓ : ℕ} {p : List ℕ} (impl : Implementation)
    (ok : CompressOk impl.compressBlock) (ys : List (List ℕ)) :
    ∀ (x : List ℕ) (st : State), Absorbed ℓ p x st → st.implementation = impl →
      (x ++ ys.flatten).length < 2 ^ 128 →
      Absorbed ℓ p (x ++ ys.flatten) (ys.foldl State.update st) ∧
        (ys.foldl State.update st).implementation = impl := by
  induction ys with
  | nil => intro x st h hi _; simpa using ⟨h, hi⟩
  | cons y ys ih =>
    intro x st h hi hlen
    simp only [List.flatten_cons, List.length_append] at hlen
    obtain ⟨h', hi'⟩ := h.update (hi ▸ ok) y (by omega)
    have := ih (x ++ y) (st.update y) h' (hi' ▸ hi) (by simp only [List.length_append]; omega)
    simpa [List.append_assoc] using this

/-- **`blake2b_simd`'s `State` computes RFC 7693's BLAKE2b**, on an implementation whose
    `compress_block` is RFC 7693's compression: `finalize` after `update`s of `xs` from
    `to_state` is the BLAKE2b of the bytes of `xs`, for a digest of at most 64 bytes and fewer
    than `2^128` bytes in all. -/
theorem finalize_foldl_update (params : Params)
    (ok : CompressOk params.implementation.compressBlock) (hℓ : params.hashLength ≤ 64)
    (xs : List (List ℕ)) (hlen : xs.flatten.length < 2 ^ 128) :
    (xs.foldl State.update params.toState).finalize =
      blake2b params.hashLength params.personal xs.flatten := by
  obtain ⟨h, hi⟩ := Absorbed.foldl_update params.implementation ok xs [] params.toState
    params.toState_absorbed rfl (by simpa using hlen)
  simp only [List.nil_append] at h
  exact h.finalize (hi ▸ ok) hℓ hlen

/-! ## The setters -/

/-- `Params::hash_length` panics exactly on a length outside `1 ..= 64`. -/
theorem Params.hashLength?_isSome (params : Params) (ℓ : ℕ) :
    (params.hashLength? ℓ).isSome ↔ 1 ≤ ℓ ∧ ℓ ≤ 64 := by
  by_cases h : 1 ≤ ℓ ∧ ℓ ≤ 64 <;> simp [Params.hashLength?, outBytes, h]

/-- `Params::personal` panics exactly on a personalization over 16 bytes. -/
theorem Params.personal?_isSome (params : Params) (x : List ℕ) :
    (params.personal? x).isSome ↔ x.length ≤ 16 := by
  by_cases h : x.length ≤ 16 <;> simp [Params.personal?, personalBytes, h]

end Equihash.Verifier.Blake2b
