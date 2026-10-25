/-
`expand_array`: each `c`-bit digit of the input becomes `w = ⌈c/8⌉ + pad` bytes, big-endian.
-/
module

public import Equihash.Verifier.Minimal
public import Equihash.Proofs.Expand
public import Equihash.Proofs.Std

@[expose] public section

namespace Equihash.Verifier

open Equihash

/-! ## The loops, as folds -/

theorem forIn_some_yield {α β : Type} (l : List α) (f : α → β → β) (init : β) :
    forIn (m := Option) l init (fun a b => some (.yield (f a b))) =
      some (l.foldl (fun b a => f a b) init) :=
  List.forIn_pure_yield_eq_foldl f init

/-- A loop whose every pass continues is a fold. -/
theorem forIn_option_eq {α β : Type} (l : List α) (init : β)
    (f : α → β → Option (ForInStep β)) (g : α → β → β)
    (h : ∀ a b, f a b = some (.yield (g a b))) :
    forIn l init f = some (l.foldl (fun b a => g a b) init) := by
  rw [show f = fun a b => some (.yield (g a b)) from funext fun a => funext (h a)]
  exact forIn_some_yield l g init

/-- The inner loop's write: byte `x` of the digit ending at bit `ab` of `acc`, into slot
    `j + x`. -/
def writeByte (c w j acc ab : ℕ) (vout : List ℕ) (x : ℕ) : List ℕ :=
  vout.set (j + x)
    ((acc >>> (ab + 8 * (w - x - 1)) &&& ((2 ^ c - 1) >>> (8 * (w - x - 1)) &&& 255)) % 256)

/-- One pass of the outer loop, for input byte `b`, on the state
    `(vout, acc_bits, acc_value, j)`. -/
def outerStep (c pad : ℕ) (s : List ℕ × ℕ × ℕ × ℕ) (b : ℕ) : List ℕ × ℕ × ℕ × ℕ :=
  let w := divCeil c 8 + pad
  let acc := s.2.2.1 <<< 8 % 2 ^ 32 ||| b
  if s.2.1 + 8 ≥ c then
    ((List.range' pad (w - pad)).foldl (writeByte c w s.2.2.2 acc (s.2.1 + 8 - c)) s.1,
      s.2.1 + 8 - c, acc, s.2.2.2 + w)
  else (s.1, s.2.1 + 8, acc, s.2.2.2)

/-- Past its checks, and unless expansion is a copy, `expand_array_into` folds `outerStep` over the
    input, from an all-zero output. -/
theorem expandArrayInto?_eq_fold (vin vout : List ℕ) (c pad : ℕ) (h8 : c ≥ 8)
    (h32 : 32 ≥ 7 + c) (hl : vout.length = expandedLen vin.length c pad)
    (hne : ¬ expandedLen vin.length c pad = vin.length) :
    expandArrayInto? vin c pad vout =
      some (vin.foldl (outerStep c pad) (vout.map fun _ => 0, 0, 0, 0)).1 := by
  simp only [expandArrayInto?, h8, h32, hl, hne, guard_true, ↓reduceIte, Option.pure_def,
    Option.bind_eq_bind, Option.bind_some, Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, forIn_some_yield, Option.bind_some]
  rw [forIn_option_eq vin _ _ (fun b s => outerStep c pad s b) (fun b s => by
    simp only [outerStep]; split_ifs <;> simp; rfl)]
  rfl

/-! ## The inner loop -/

/-- The value the inner loop writes is byte `x` of the digit `⌊acc / 2^ab⌋ mod 2^c`. -/
theorem writeByte_value (c w acc ab x : ℕ) :
    (acc >>> (ab + 8 * (w - x - 1)) &&& ((2 ^ c - 1) >>> (8 * (w - x - 1)) &&& 255)) % 256 =
      beByte w (acc >>> ab % 2 ^ c) x := by
  have := emit_byte acc ab c (w - x - 1)
  rw [beByte, show w - 1 - x = w - x - 1 by omega]
  simpa using this

/-- The inner loop writes byte `x` of the digit into slot `j + x`, for each `x` in `xs`, and
    changes nothing else. -/
theorem foldl_writeByte (c w j acc ab : ℕ) (xs : List ℕ) (hxs : xs.Nodup) (vout : List ℕ) :
    (xs.foldl (writeByte c w j acc ab) vout).length = vout.length ∧
    (∀ x ∈ xs, j + x < vout.length → (xs.foldl (writeByte c w j acc ab) vout)[j + x]? =
      some (beByte w (acc >>> ab % 2 ^ c) x)) ∧
    (∀ i, (∀ x ∈ xs, j + x ≠ i) → (xs.foldl (writeByte c w j acc ab) vout)[i]? = vout[i]?) := by
  induction xs generalizing vout with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx, hxs'⟩ := List.nodup_cons.mp hxs
    have hlen : (writeByte c w j acc ab vout x).length = vout.length := by simp [writeByte]
    obtain ⟨hl, hw, hr⟩ := ih hxs' (writeByte c w j acc ab vout x)
    simp only [List.foldl_cons]
    refine ⟨hl.trans hlen, fun y hy hyl => ?_, fun i hi => ?_⟩
    · rcases List.mem_cons.mp hy with rfl | hy
      · rw [hr (j + y) (fun x' hx' h => hx (by rwa [show x' = y by omega] at hx'))]
        simp [writeByte, hyl, writeByte_value]
      · exact hw y hy (by rw [hlen]; exact hyl)
    · rw [hr i (fun x' hx' => hi x' (List.mem_cons_of_mem _ hx'))]
      simp [writeByte, List.getElem?_set_ne (hi x List.mem_cons_self)]

/-! ## The digits of the input -/

/-- The first `t` bytes of `vin`, as a big-endian number. -/
def prefixVal (vin : List ℕ) (t : ℕ) : ℕ := beNat (vin.take t)

theorem prefixVal_succ (vin : List ℕ) (t : ℕ) (ht : t < vin.length) :
    prefixVal vin (t + 1) = 2 ^ 8 * prefixVal vin t + vin[t] := by
  simp only [prefixVal, List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some,
    beNat_append_singleton]
  norm_num

/-- The whole input is a prefix followed by fewer than `256^(L − t)` more. -/
theorem prefixVal_split (vin : List ℕ) (hvin : ∀ b ∈ vin, b < 256) (t : ℕ) :
    ∃ R < 256 ^ (vin.length - t),
      prefixVal vin vin.length = prefixVal vin t * 256 ^ (vin.length - t) + R := by
  refine ⟨beNat (vin.drop t), ?_, ?_⟩
  · simpa using beNat_lt (vin.drop t) fun b hb => hvin b (List.mem_of_mem_drop hb)
  · conv_lhs => rw [prefixVal, List.take_of_length_le (le_of_eq rfl),
      ← List.take_append_drop t vin]
    rw [beNat_append]
    simp [prefixVal]

/-- **Accumulate**: shifting input byte `t` into the accumulator keeps its low bits equal to
    the first `t + 1` bytes'. -/
theorem acc_prefix (vin : List ℕ) (hvin : ∀ b ∈ vin, b < 256) (t : ℕ) (ht : t < vin.length)
    (ab av : ℕ) (hab : ab + 8 ≤ 32) (hav : av % 2 ^ ab = prefixVal vin t % 2 ^ ab) :
    (av <<< 8 % 2 ^ 32 ||| vin[t]) % 2 ^ (ab + 8) = prefixVal vin (t + 1) % 2 ^ (ab + 8) := by
  have hb : vin[t] < 2 ^ 8 := hvin _ (List.getElem_mem ht)
  rw [Nat.shiftLeft_eq, acc_shift_or _ _ _ hb hab, hav, prefixVal_succ _ _ ht,
    append_byte_mod _ _ _ hb]

/-- **Emit**: when the pending bits reach `c`, the top `c` of them are digit `⌊8t/c⌋` of the
    whole input. -/
theorem digit_emit (vin : List ℕ) (hvin : ∀ b ∈ vin, b < 256) (t : ℕ) (ht : t < vin.length)
    (ab c X : ℕ) (hc : 8 ≤ c) (hab : ab = 8 * t % c) (hemit : c ≤ ab + 8)
    (hX : X % 2 ^ (ab + 8) = prefixVal vin (t + 1) % 2 ^ (ab + 8)) :
    X >>> (ab + 8 - c) % 2 ^ c = digit c vin.length (prefixVal vin vin.length) (8 * t / c) := by
  have hdm := (div_mod_add_eight (8 * t) c hc).1 (by rw [← hab]; exact hemit)
  have hsplit := Nat.div_add_mod (8 * t + 8) c
  rw [hdm.1, hdm.2, ← hab] at hsplit
  obtain ⟨a₂, ha₂⟩ : ∃ a₂, ab + 8 = a₂ + c := ⟨ab + 8 - c, by omega⟩
  rw [show ab + 8 - c = a₂ by omega]
  rw [ha₂] at hX
  rw [← mod_shiftRight, hX, mod_shiftRight, Nat.shiftRight_eq_div_pow]
  obtain ⟨R, hR, hV⟩ := prefixVal_split vin hvin (t + 1)
  have hexp : 8 * vin.length - (8 * t / c + 1) * c = 8 * (vin.length - (t + 1)) + a₂ := by
    rw [Nat.mul_comm (8 * t / c + 1) c]; omega
  simp only [digit, hexp, hV, div_prefix _ _ _ _ hR]

/-- Whole-byte digits (`c = 8·w`) are runs of input bytes: byte `x` of digit `s` is input
    byte `s·w + x`. This is why `expand_array_into` may copy its input when the expansion
    adds no padding. -/
theorem digit_whole_bytes (vin : List ℕ) (hvin : ∀ b ∈ vin, b < 256) (w s x : ℕ)
    (hs : (s + 1) * w ≤ vin.length) (hx : x < w) :
    vin[s * w + x]? =
      some (beByte w (digit (8 * w) vin.length (prefixVal vin vin.length) s) x) := by
  have hs' : s * w + w ≤ vin.length := by rw [← Nat.succ_mul]; exact hs
  -- The digit is cut from the number formed by the first `(s+1)·w` bytes.
  obtain ⟨R, hR, hV⟩ := prefixVal_split vin hvin ((s + 1) * w)
  have hexp : 8 * vin.length - (s + 1) * (8 * w) = 8 * (vin.length - (s + 1) * w) + 0 := by
    rw [show (s + 1) * (8 * w) = 8 * ((s + 1) * w) by ring]; omega
  -- Those bytes are the first `s·w`, then the block of `w`.
  set blk := (vin.drop (s * w)).take w with hblk
  have hblen : blk.length = w := by
    simp only [hblk, List.length_take, List.length_drop]
    omega
  have hblt : ∀ b ∈ blk, b < 256 := fun b hb =>
    hvin b (List.mem_of_mem_drop (List.mem_of_mem_take hb))
  have hP : prefixVal vin ((s + 1) * w) = prefixVal vin (s * w) * 256 ^ w + beNat blk := by
    simp only [prefixVal, hblk]
    rw [show (s + 1) * w = s * w + w by ring, List.take_add, beNat_append, ← hblk, hblen]
  rw [digit, hexp, hV, div_prefix _ _ _ _ hR, pow_zero, Nat.div_one, hP,
    show (2 : ℕ) ^ (8 * w) = 256 ^ w by rw [pow_mul]; norm_num,
    Nat.add_comm (prefixVal vin (s * w) * 256 ^ w), Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (hblen ▸ beNat_lt blk hblt)]
  -- Byte `x` of the block.
  have hbyte := beNat_byte blk hblt x (by omega)
  rw [beByte, Nat.shiftRight_eq_div_pow,
    show (2 : ℕ) ^ (8 * (w - 1 - x)) = 256 ^ (w - 1 - x) by rw [pow_mul]; norm_num,
    show (2 : ℕ) ^ 8 = 256 by norm_num, show w - 1 - x = blk.length - 1 - x by rw [hblen],
    hbyte]
  simp [hblk, List.getElem?_eq_getElem (show s * w + x < vin.length by omega)]

/-! ## The outer loop -/

/-- The invariant of the outer loop after the first `t` input bytes: the digits completed so
    far are written as expanded chunks, the pending bits are the low `acc_bits` bits of
    `acc_value`, and the rest of the output is still zero. -/
def OuterInv (vin : List ℕ) (c w len t : ℕ) (s : List ℕ × ℕ × ℕ × ℕ) : Prop :=
  s.1.length = len ∧ s.2.1 = 8 * t % c ∧ s.2.2.2 = 8 * t / c * w ∧
  s.2.2.1 % 2 ^ s.2.1 = prefixVal vin t % 2 ^ s.2.1 ∧
  (∀ d < 8 * t / c, ∀ x < w,
    s.1[d * w + x]? = some (beByte w (digit c vin.length (prefixVal vin vin.length) d) x)) ∧
  (∀ i, s.2.2.2 ≤ i → i < len → s.1[i]? = some 0)

/-- One pass of the outer loop keeps the invariant. -/
theorem OuterInv.next (vin : List ℕ) (hvin : ∀ b ∈ vin, b < 256) (c pad len t : ℕ)
    (hc8 : 8 ≤ c) (hc32 : c + 7 ≤ 32) (ht : t < vin.length)
    (hlen : len = 8 * vin.length / c * (divCeil c 8 + pad))
    (s : List ℕ × ℕ × ℕ × ℕ) (h : OuterInv vin c (divCeil c 8 + pad) len t s) :
    OuterInv vin c (divCeil c 8 + pad) len (t + 1) (outerStep c pad s vin[t]) := by
  obtain ⟨v, ab, av, j⟩ := s
  obtain ⟨hvl, hab, hj, hav, hdone, hzero⟩ := h
  dsimp only at hvl hab hj hav hdone hzero
  set w := divCeil c 8 + pad with hw
  have hw8 : divCeil c 8 = (c + 7) / 8 := by rw [divCeil_eq _ _ (by norm_num)]; rfl
  have habc : ab < c := by rw [hab]; exact Nat.mod_lt _ (by omega)
  have hdm := div_mod_add_eight (8 * t) c hc8
  have h8 : 8 * (t + 1) = 8 * t + 8 := by ring
  have hacc := acc_prefix vin hvin t ht ab av (by omega) hav
  simp only [outerStep, ← hw]
  split_ifs with hemit
  · -- A digit completes and is written.
    obtain ⟨hq, hr⟩ := hdm.1 (by omega)
    have hjw : j + w ≤ len := by
      have hq' : 8 * t / c + 1 ≤ 8 * vin.length / c := by
        rw [← hq]; exact Nat.div_le_div_right (by omega)
      have := Nat.mul_le_mul_right w hq'
      rw [Nat.succ_mul] at this; rw [hlen, hj]; omega
    have hD := digit_emit vin hvin t ht ab c (av <<< 8 % 2 ^ 32 ||| vin[t]) hc8 hab hemit hacc
    obtain ⟨hwl, hww, hwr⟩ := foldl_writeByte c w j (av <<< 8 % 2 ^ 32 ||| vin[t]) (ab + 8 - c)
      (List.range' pad (w - pad)) (List.nodup_range' ..) v
    refine ⟨by rw [hwl, hvl], by rw [h8, hr, hab], by rw [h8, hq, Nat.succ_mul, hj], ?_, ?_, ?_⟩
    · have hdvd : 2 ^ (ab + 8 - c) ∣ 2 ^ (ab + 8) := Nat.pow_dvd_pow 2 (by omega)
      dsimp only
      rw [← Nat.mod_mod_of_dvd _ hdvd, hacc, Nat.mod_mod_of_dvd _ hdvd]
    · intro d hd x hx
      rw [h8, hq] at hd
      rcases Nat.lt_or_ge d (8 * t / c) with hd' | hd'
      · have hlt : d * w + x < j := by
          have := Nat.mul_le_mul_right w (show d + 1 ≤ 8 * t / c by omega)
          rw [Nat.succ_mul] at this; omega
        rw [hwr _ (fun y _ => by omega)]
        exact hdone d hd' x hx
      · obtain rfl : d = 8 * t / c := by omega
        rw [← hj]
        rcases Nat.lt_or_ge x pad with hxp | hxp
        · rw [hwr _ (fun y hy => by rw [List.mem_range'_1] at hy; omega),
            hzero _ (by omega) (by omega)]
          congr 1
          symm
          exact beByte_pad _ pad c _ x (Nat.mod_lt _ (by positivity)) (by omega) hxp (by omega)
        · rw [hww x (List.mem_range'_1.mpr ⟨hxp, by omega⟩) (by omega), hD]
    · intro i hi hi'
      dsimp only at hi
      rw [hwr _ (fun y hy => by rw [List.mem_range'_1] at hy; omega)]
      exact hzero i (by omega) hi'
  · -- No digit completes: the bits are pending.
    obtain ⟨hq, hr⟩ := hdm.2 (by omega)
    refine ⟨hvl, by rw [h8, hr, hab], by rw [h8, hq, hj], ?_, ?_, hzero⟩
    · dsimp only; rw [hab, ← hr, ← h8]; rw [hab] at hacc; rw [← hr, ← h8] at hacc; exact hacc
    · intro d hd; exact hdone d (by rw [h8, hq] at hd; exact hd)

/-- **`expand_array`**: digit `s` of the input (`c` bits, from the most significant) becomes
    bytes `s·w .. s·w + w` of the output, big-endian, with `w = ⌈c/8⌉ + pad`. -/
theorem expandArray?_spec (vin : List ℕ) (hvin : ∀ b ∈ vin, b < 256) (c pad : ℕ)
    (hc8 : 8 ≤ c) (hc32 : c + 7 ≤ 32) (hdiv : c ∣ 8 * vin.length) :
    ∃ out, expandArray? vin c pad = some out ∧
      out.length = 8 * vin.length / c * (divCeil c 8 + pad) ∧
      ∀ s < 8 * vin.length / c, ∀ x < divCeil c 8 + pad,
        out[s * (divCeil c 8 + pad) + x]? = some
          (beByte (divCeil c 8 + pad) (digit c vin.length (prefixVal vin vin.length) s) x) := by
  set w := divCeil c 8 + pad with hw
  have hw8 : divCeil c 8 = (c + 7) / 8 := by rw [divCeil_eq _ _ (by norm_num)]; rfl
  -- The output has `(8L / c)·w` bytes.
  have hexp : expandedLen vin.length c pad = 8 * vin.length / c * w := by
    rw [expandedLen, ← hw, Nat.mul_comm 8 w, Nat.mul_assoc, Nat.mul_div_assoc _ hdiv,
      Nat.mul_comm]
  by_cases hcopy : expandedLen vin.length c pad = vin.length
  · -- Expansion is the identity: the output is a copy of the input.
    refine ⟨vin, ?_, by rw [← hexp, hcopy], fun s hs x hx => ?_⟩
    · simp [expandArray?, expandArrayInto?, show c ≥ 8 by omega, show 32 ≥ 7 + c by omega,
        hcopy]
    have hL0 : 0 < vin.length := by
      rcases Nat.eq_zero_or_pos vin.length with h0 | h0
      · simp [h0] at hs
      · exact h0
    have hcw : c = 8 * w := by
      refine eq_of_expanded_len _ _ _ (by omega) hdiv hL0 ?_
      have := hcopy
      rwa [expandedLen, ← hw] at this
    have hsw : (s + 1) * w ≤ vin.length := by
      have hw0 : 0 < w := by omega
      rw [hcw, Nat.mul_comm 8 w, Nat.mul_comm 8 vin.length,
        Nat.mul_div_mul_right _ _ (by norm_num)] at hs
      exact le_trans (Nat.mul_le_mul_right w hs) (Nat.div_mul_le_self _ _)
    rw [digit_whole_bytes vin hvin w s x hsw hx, hcw]
  · -- The general case: the outer loop, from an all-zero output.
    have hfold := expandArrayInto?_eq_fold vin (List.replicate (expandedLen vin.length c pad) 0)
      c pad (by omega) (by omega) (by simp) hcopy
    have hinv : ∀ t ≤ vin.length, OuterInv vin c w (8 * vin.length / c * w) t
        ((vin.take t).foldl (outerStep c pad)
          ((List.replicate (expandedLen vin.length c pad) 0).map fun _ => 0, 0, 0, 0)) := by
      intro t ht
      induction t with
      | zero =>
        refine ⟨by simp [hexp], by simp, by simp, by simp [Nat.mod_one], fun d hd => by simp at hd,
          ?_⟩
        intro i _ hi
        simp [hexp, hi]
      | succ t ih =>
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
          List.foldl_append, List.foldl_cons, List.foldl_nil]
        exact OuterInv.next vin hvin c pad _ t hc8 hc32 (by omega) rfl _ (ih (by omega))
    obtain ⟨hl, -, -, -, hdone, -⟩ := hinv vin.length le_rfl
    rw [List.take_of_length_le le_rfl] at hl hdone
    exact ⟨_, hfold, hl, hdone⟩

end Equihash.Verifier
