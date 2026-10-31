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

/-- A loop whose every pass either continues or fails is a monadic fold. -/
theorem forIn_option_eq_foldlM {α β : Type} (l : List α) (init : β)
    (f : α → β → Option (ForInStep β)) (g : α → β → Option β)
    (h : ∀ a b, f a b = (g a b).map .yield) :
    forIn l init f = l.foldlM (fun b a => g a b) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    simp only [List.forIn_cons, h, List.foldlM_cons]
    cases g a init <;> simp [ih]

/-- `writeByte`, panicking (`none`) out of bounds as `vout[j + x] = …` does. -/
def writeByte? (c w j acc ab : ℕ) (vout : List ℕ) (x : ℕ) : Option (List ℕ) :=
  set? vout (j + x)
    ((acc >>> (ab + 8 * (w - x - 1)) &&& ((2 ^ c - 1) >>> (8 * (w - x - 1)) &&& 255)) % 256)

/-- `outerStep`, with each write panicking out of bounds. -/
def outerStep? (c pad : ℕ) (s : List ℕ × ℕ × ℕ × ℕ) (b : ℕ) : Option (List ℕ × ℕ × ℕ × ℕ) :=
  let w := divCeil c 8 + pad
  let acc := s.2.2.1 <<< 8 % 2 ^ 32 ||| b
  if s.2.1 + 8 ≥ c then do
    let v ← (List.range' pad (w - pad)).foldlM (writeByte? c w s.2.2.2 acc (s.2.1 + 8 - c)) s.1
    pure (v, s.2.1 + 8 - c, acc, s.2.2.2 + w)
  else pure (s.1, s.2.1 + 8, acc, s.2.2.2)

/-- Writing an element's bytes keeps the output's length. -/
theorem length_foldl_writeByte (c w j acc ab : ℕ) (xs vout : List ℕ) :
    (xs.foldl (writeByte c w j acc ab) vout).length = vout.length := by
  induction xs generalizing vout with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih]; simp [writeByte]

/-- Writes in bounds do not panic. -/
theorem foldlM_writeByte? (c w j acc ab : ℕ) (xs vout : List ℕ)
    (hb : ∀ x ∈ xs, j + x < vout.length) :
    xs.foldlM (writeByte? c w j acc ab) vout = some (xs.foldl (writeByte c w j acc ab) vout) := by
  induction xs generalizing vout with
  | nil => rfl
  | cons x xs ih =>
    have hx := hb x List.mem_cons_self
    simp only [List.foldlM_cons, List.foldl_cons, writeByte?, set?, hx, ↓reduceIte,
      Option.bind_eq_bind, Option.bind_some]
    exact ih _ fun y hy => by
      rw [List.length_set]; exact hb y (List.mem_cons_of_mem _ hy)

/-- The outer loop after `t` input bytes, as far as its writes' bounds go: the output keeps its
    length, and the next digit starts at `⌊8t/c⌋·w`. -/
def BoundInv (c w len t : ℕ) (s : List ℕ × ℕ × ℕ × ℕ) : Prop :=
  s.1.length = len ∧ s.2.1 = 8 * t % c ∧ s.2.2.2 = 8 * t / c * w

/-- The outer loop writes nothing out of bounds, into an output of at least `⌊8L/c⌋·w` bytes. -/
theorem foldlM_outerStep? (vin : List ℕ) (c pad len : ℕ) (hc8 : 8 ≤ c)
    (hlen : 8 * vin.length / c * (divCeil c 8 + pad) ≤ len) (init : List ℕ × ℕ × ℕ × ℕ)
    (hinit : BoundInv c (divCeil c 8 + pad) len 0 init) :
    vin.foldlM (outerStep? c pad) init = some (vin.foldl (outerStep c pad) init) := by
  set w := divCeil c 8 + pad with hw
  suffices ∀ t ≤ vin.length,
      (vin.take t).foldlM (outerStep? c pad) init =
        some ((vin.take t).foldl (outerStep c pad) init) ∧
      BoundInv c w len t ((vin.take t).foldl (outerStep c pad) init) by
    have := (this vin.length le_rfl).1
    rwa [List.take_of_length_le le_rfl] at this
  intro t ht
  induction t with
  | zero => exact ⟨rfl, by simpa using hinit⟩
  | succ t ih =>
    obtain ⟨hM, hl, hab, hj⟩ := ih (by omega)
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
      List.foldlM_append, hM, List.foldl_append]
    simp only [Option.bind_eq_bind, Option.bind_some, List.foldlM_cons, List.foldlM_nil,
      List.foldl_cons, List.foldl_nil]
    set s := (vin.take t).foldl (outerStep c pad) init
    have hdm := div_mod_add_eight (8 * t) c hc8
    have h8 : 8 * (t + 1) = 8 * t + 8 := by ring
    unfold outerStep? outerStep
    dsimp only
    rw [← hw]
    split_ifs with hemit
    · -- A digit completes: its `w` bytes fit below `⌊8L/c⌋·w`.
      obtain ⟨hq, hr⟩ := hdm.1 (by omega)
      have hjw : s.2.2.2 + w ≤ len := by
        have hq' : 8 * t / c + 1 ≤ 8 * vin.length / c := by
          rw [← hq]; exact Nat.div_le_div_right (by omega)
        have := Nat.mul_le_mul_right w hq'
        rw [Nat.succ_mul] at this; omega
      rw [foldlM_writeByte? _ _ _ _ _ _ _ fun x hx => by
        rw [List.mem_range'_1] at hx; omega]
      refine ⟨rfl, by rw [length_foldl_writeByte, hl], by rw [h8, hr, hab], ?_⟩
      show s.2.2.2 + w = 8 * (t + 1) / c * w
      rw [h8, hq, Nat.succ_mul, hj]
    · obtain ⟨hq, hr⟩ := hdm.2 (by omega)
      exact ⟨rfl, hl, by rw [h8, hr, hab], by rw [h8, hq, hj]⟩

/-- A write sequence that does not panic keeps the output's length, and wrote in bounds. -/
theorem foldlM_writeByte?_bound (c w j acc ab : ℕ) (xs vout v : List ℕ)
    (h : xs.foldlM (writeByte? c w j acc ab) vout = some v) :
    v.length = vout.length ∧ ∀ x ∈ xs, j + x < vout.length := by
  induction xs generalizing vout with
  | nil =>
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp
  | cons x xs ih =>
    simp only [List.foldlM_cons, writeByte?, set?] at h
    split_ifs at h with hx
    · simp only [Option.bind_eq_bind, Option.bind_some] at h
      obtain ⟨hl, hb⟩ := ih _ h
      rw [List.length_set] at hl hb
      exact ⟨hl, fun y hy => (List.mem_cons.mp hy).elim (fun e => e ▸ hx) (hb y)⟩
    · simp at h

/-- The outer loop panics, into an output shorter than `⌊8L/c⌋·w` bytes: its last write is out
    of bounds. -/
theorem foldlM_outerStep?_short (vin : List ℕ) (c pad len : ℕ) (hc8 : 8 ≤ c)
    (hlen : len < 8 * vin.length / c * (divCeil c 8 + pad)) (init : List ℕ × ℕ × ℕ × ℕ)
    (hinit : BoundInv c (divCeil c 8 + pad) len 0 init) :
    vin.foldlM (outerStep? c pad) init = none := by
  set w := divCeil c 8 + pad with hw
  have hw1 : pad < w := by
    have : 1 ≤ divCeil c 8 := by rw [divCeil_eq _ _ (by norm_num)]; omega
    omega
  suffices ∀ t ≤ vin.length, ∀ s, (vin.take t).foldlM (outerStep? c pad) init = some s →
      BoundInv c w len t s ∧ s.2.2.2 ≤ len by
    rcases hM : vin.foldlM (outerStep? c pad) init with _ | s
    · rfl
    obtain ⟨⟨-, -, hj⟩, hle⟩ := this vin.length le_rfl s
      (by rwa [List.take_of_length_le le_rfl])
    omega
  intro t ht
  induction t with
  | zero =>
    intro s hs
    simp only [List.take_zero, List.foldlM_nil, Option.pure_def, Option.some.injEq] at hs
    subst hs
    exact ⟨hinit, by rw [hinit.2.2]; simp⟩
  | succ t ih =>
    intro s' hs'
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
      List.foldlM_append] at hs'
    obtain ⟨s, hM, hstep⟩ := Option.bind_eq_some_iff.mp hs'
    obtain ⟨⟨hl, hab, hj⟩, hjle⟩ := ih (by omega) s hM
    simp only [List.foldlM_cons, List.foldlM_nil, Option.bind_eq_bind] at hstep
    obtain ⟨s'', hs'', hpure⟩ := Option.bind_eq_some_iff.mp hstep
    simp only [Option.pure_def, Option.some.injEq] at hpure
    subst hpure
    have hdm := div_mod_add_eight (8 * t) c hc8
    have h8 : 8 * (t + 1) = 8 * t + 8 := by ring
    unfold outerStep? at hs''
    dsimp only at hs''
    rw [← hw] at hs''
    split_ifs at hs'' with hemit
    · -- A digit completes: its last byte was written in bounds.
      obtain ⟨hq, hr⟩ := hdm.1 (by omega)
      obtain ⟨v, hv, hpure⟩ := Option.bind_eq_some_iff.mp hs''
      simp only [Option.pure_def, Option.some.injEq] at hpure
      subst hpure
      obtain ⟨hvl, hb⟩ := foldlM_writeByte?_bound _ _ _ _ _ _ _ _ hv
      have hlast := hb (w - 1) (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
      refine ⟨⟨by rw [hvl, hl], by rw [h8, hr, hab], ?_⟩, by dsimp only; omega⟩
      show s.2.2.2 + w = 8 * (t + 1) / c * w
      rw [h8, hq, Nat.succ_mul, hj]
    · obtain ⟨hq, hr⟩ := hdm.2 (by omega)
      simp only [Option.pure_def, Option.some.injEq] at hs''
      subst hs''
      exact ⟨⟨hl, by rw [h8, hr, hab], by rw [h8, hq, hj]⟩, hjle⟩

/-- Past its checks, and unless expansion is a copy, `expand_array_into` is the outer loop, a
    monadic fold of `outerStep?` over the input, from an all-zero output. -/
theorem expandArrayInto?_eq_foldlM (vin vout : List ℕ) (c pad : ℕ) (h8 : c ≥ 8)
    (h32 : 32 ≥ 7 + c) (hl : vout.length = expandedLen vin.length c pad)
    (hne : ¬ expandedLen vin.length c pad = vin.length) :
    expandArrayInto? vin c pad vout =
      (vin.foldlM (outerStep? c pad) (vout.map fun _ => 0, 0, 0, 0)).map Prod.fst := by
  simp only [expandArrayInto?, h8, h32, hl, hne, guard_true, ↓reduceIte, Option.pure_def,
    Option.bind_eq_bind, Option.bind_some, Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size]
  rw [forIn_option_eq_foldlM vin _ _ (fun b s => outerStep? c pad s b) (fun b s => by
    simp only [outerStep?]
    split_ifs
    · rw [forIn_option_eq_foldlM _ _ _ (fun x v => writeByte? c (divCeil c 8 + pad) s.2.2.2
        (s.2.2.1 <<< 8 % 2 ^ 32 ||| b) (s.2.1 + 8 - c) v x) (fun x v => by
          simp only [writeByte?]
          cases set? v _ _ <;> rfl)]
      have key : ∀ {α γ : Type} (x : Option α) (g : α → γ),
          (x.bind fun a => some (ForInStep.yield (g a))) =
            Option.map ForInStep.yield (x >>= fun v => pure (g v)) := by
        intro α γ x g; cases x <;> rfl
      simp only [Nat.add_sub_cancel, Nat.div_one]
      exact key _ _
    · rfl)]
  cases vin.foldlM (outerStep? c pad) (vout.map fun _ => 0, 0, 0, 0) <;> rfl

/-- Past its checks, and unless expansion is a copy, `expand_array_into` writes nothing out of
    bounds when the product `8·w·L` does not wrap, and folds `outerStep` over the input, from an
    all-zero output. -/
theorem expandArrayInto?_eq_fold (vin vout : List ℕ) (c pad : ℕ) (h8 : c ≥ 8)
    (h32 : 32 ≥ 7 + c) (hl : vout.length = expandedLen vin.length c pad)
    (hne : ¬ expandedLen vin.length c pad = vin.length)
    (hfit : 8 * (divCeil c 8 + pad) * vin.length < 2 ^ 64) :
    expandArrayInto? vin c pad vout =
      some (vin.foldl (outerStep c pad) (vout.map fun _ => 0, 0, 0, 0)).1 := by
  have hlen : 8 * vin.length / c * (divCeil c 8 + pad) ≤ (vout.map fun _ => 0).length := by
    rw [List.length_map, hl, expandedLen, Nat.mod_eq_of_lt hfit,
      Nat.le_div_iff_mul_le (by omega)]
    calc 8 * vin.length / c * (divCeil c 8 + pad) * c
        = 8 * vin.length / c * c * (divCeil c 8 + pad) := by ring
      _ ≤ 8 * vin.length * (divCeil c 8 + pad) :=
        Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
      _ = 8 * (divCeil c 8 + pad) * vin.length := by ring
  rw [expandArrayInto?_eq_foldlM vin vout c pad h8 h32 hl hne,
    foldlM_outerStep? vin c pad _ h8 hlen _ ⟨rfl, by simp, by simp⟩]
  rfl

/-- Past its checks, and unless expansion is a copy, `expand_array_into` panics into an output
    shorter than `⌊8L/c⌋·w` bytes. -/
theorem expandArrayInto?_short (vin vout : List ℕ) (c pad : ℕ) (h8 : c ≥ 8)
    (h32 : 32 ≥ 7 + c) (hl : vout.length = expandedLen vin.length c pad)
    (hne : ¬ expandedLen vin.length c pad = vin.length)
    (hshort : vout.length < 8 * vin.length / c * (divCeil c 8 + pad)) :
    expandArrayInto? vin c pad vout = none := by
  rw [expandArrayInto?_eq_foldlM vin vout c pad h8 h32 hl hne,
    foldlM_outerStep?_short vin c pad _ h8 (by rwa [List.length_map]) _
      ⟨rfl, by simp, by simp⟩]
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
    bytes `s·w .. s·w + w` of the output, big-endian, with `w = ⌈c/8⌉ + pad`, when the product
    `8·w·L` does not wrap. -/
theorem expandArray?_spec (vin : List ℕ) (hvin : ∀ b ∈ vin, b < 256) (c pad : ℕ)
    (hc8 : 8 ≤ c) (hc32 : c + 7 ≤ 32) (hdiv : c ∣ 8 * vin.length)
    (hfit : 8 * (divCeil c 8 + pad) * vin.length < 2 ^ 64) :
    ∃ out, expandArray? vin c pad = some out ∧
      out.length = 8 * vin.length / c * (divCeil c 8 + pad) ∧
      ∀ s < 8 * vin.length / c, ∀ x < divCeil c 8 + pad,
        out[s * (divCeil c 8 + pad) + x]? = some
          (beByte (divCeil c 8 + pad) (digit c vin.length (prefixVal vin vin.length) s) x) := by
  set w := divCeil c 8 + pad with hw
  have hw8 : divCeil c 8 = (c + 7) / 8 := by rw [divCeil_eq _ _ (by norm_num)]; rfl
  -- The output has `(8L / c)·w` bytes.
  have hexp : expandedLen vin.length c pad = 8 * vin.length / c * w := by
    rw [expandedLen, Nat.mod_eq_of_lt hfit, Nat.mul_comm 8 w, Nat.mul_assoc,
      Nat.mul_div_assoc _ hdiv, Nat.mul_comm]
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
      rwa [expandedLen, Nat.mod_eq_of_lt hfit] at this
    have hsw : (s + 1) * w ≤ vin.length := by
      have hw0 : 0 < w := by omega
      rw [hcw, Nat.mul_comm 8 w, Nat.mul_comm 8 vin.length,
        Nat.mul_div_mul_right _ _ (by norm_num)] at hs
      exact le_trans (Nat.mul_le_mul_right w hs) (Nat.div_mul_le_self _ _)
    rw [digit_whole_bytes vin hvin w s x hsw hx, hcw]
  · -- The general case: the outer loop, from an all-zero output.
    have hfold := expandArrayInto?_eq_fold vin (List.replicate (expandedLen vin.length c pad) 0)
      c pad (by omega) (by omega) (by simp) hcopy hfit
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
