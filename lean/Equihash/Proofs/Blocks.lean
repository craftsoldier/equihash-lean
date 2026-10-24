/-
§7.7.1's conditions, read as a tree.

The verifier checks a solution bottom up: it splits a block of `2^r` indices into halves,
checks each, then merges them. `Good` states what it checks, on the indices and their hash
values, and `good_iff_validSolution` shows that these checks are §7.7.1's conditions plus
distinct indices.

Indices here are 0-based, as encoded in a block header: index `j` is `j + 1` in §7.7.1.
-/
module

public import Equihash.Proofs.Bits

@[expose] public section

namespace Equihash

open Spec

variable (H : HashFn) (p : Params) (S : List Byte)

/-! ## Hash values have `n` bits -/

theorem one_le_m : 1 ≤ p.m := (Nat.one_le_div_iff p.n_pos).mpr p.n_le

/-- `BLAKE2b-(n·m)` outputs at least one byte. -/
theorem genHashParams_len_pos : 1 ≤ (genHashParams p).len := by
  have h1 := one_le_m p
  have h2 : p.n ≤ p.n * p.m := Nat.le_mul_of_pos_right _ h1
  obtain ⟨c, hc⟩ := p.bytes_dvd
  have := p.n_pos
  simp only [genHashParams, Params.m] at *
  omega

/-- `BLAKE2b-(n·m)` outputs at most 64 bytes, the most BLAKE2b can. -/
theorem genHashParams_len_le : (genHashParams p).len ≤ 64 := by
  have h : p.n * (512 / p.n) ≤ 512 := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self 512 p.n
  simp only [genHashParams, Params.m]
  omega

theorem length_X (i : ℕ) : (X H p S i).length = p.n := by
  have hm := one_le_m p
  have hb : 8 ∣ p.n * p.m := p.bytes_dvd
  simp only [X, equihashGen, List.length_take, List.length_drop, length_bitsOfBytes,
    List.Vector.toList_length, genHashParams]
  have hlt : (i - 1) % p.m < p.m := Nat.mod_lt _ (by omega)
  have : ((i - 1) % p.m) * p.n + p.n ≤ p.m * p.n := by
    have := Nat.mul_le_mul_right p.n (Nat.succ_le_of_lt hlt); simpa [Nat.succ_mul] using this
  rw [Nat.mul_div_cancel' hb, Nat.mul_comm p.n p.m]
  omega

/-! ## The tree -/

/-- The XOR of the hash values of the 0-based indices `is`. -/
def blockXor (is : List ℕ) : Bits := xorAll p.n (is.map fun j => X H p S (j + 1))

/-- What the verifier checks when it merges sibling blocks `L` and `R` of height `r`: their
    XORs agree on digit `r + 1` (counting from 1), `R` does not start before `L`, and they
    share no index. -/
def Mergeable (r : ℕ) (L R : List ℕ) : Prop :=
  ((blockXor H p S L).drop (r * p.digitBits)).take p.digitBits =
    ((blockXor H p S R).drop (r * p.digitBits)).take p.digitBits ∧
  ¬ R.headD 0 < L.headD 0 ∧
  ¬ ∃ i ∈ L, i ∈ R

/-- What the verifier checks on a block of `2^r` indices: both halves, then their merge. -/
def Good : ℕ → List ℕ → Prop
  | 0, _ => True
  | r + 1, is =>
    Good r (is.take (2 ^ r)) ∧ Good r (is.drop (2 ^ r)) ∧
      Mergeable H p S r (is.take (2 ^ r)) (is.drop (2 ^ r))

theorem blockXor_singleton (j : ℕ) : blockXor H p S [j] = X H p S (j + 1) := by
  have hx := zeros_xor (X H p S (j + 1))
  rw [length_X] at hx
  simpa [blockXor, xorAll] using hx

theorem blockXor_append (l₁ l₂ : List ℕ) :
    blockXor H p S (l₁ ++ l₂) = xor (blockXor H p S l₁) (blockXor H p S l₂) := by
  simp only [blockXor, List.map_append]
  exact xorAll_append _ _ _
    (fun x hx => by obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx; exact length_X H p S _)
    (fun x hx => by obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx; exact length_X H p S _)

/-! ## Blocks: the specification's flat view of the tree -/

/-- Block `w` at level `r`: the `w`-th run of `2^r` consecutive elements (0-based). -/
def block (r w : ℕ) (l : List ℕ) : List ℕ := (l.drop (w * 2 ^ r)).take (2 ^ r)

/-- `P` holds for every block at every level `1 .. R` of a list of `2^R` elements. -/
def AllBlocks (P : ℕ → List ℕ → Prop) (R : ℕ) (l : List ℕ) : Prop :=
  ∀ r, 1 ≤ r → r ≤ R → ∀ w < 2 ^ (R - r), P r (block r w l)

theorem block_top (R : ℕ) (l : List ℕ) (h : l.length = 2 ^ R) : block R 0 l = l := by
  simp [block, ← h]

/-- Each half of a list of `2^(R+1)` elements has `2^R`. -/
theorem length_take_half {R : ℕ} {l : List ℕ} (h : l.length = 2 ^ (R + 1)) :
    (l.take (2 ^ R)).length = 2 ^ R := by
  simp [h, pow_succ]; omega

theorem length_drop_half {R : ℕ} {l : List ℕ} (h : l.length = 2 ^ (R + 1)) :
    (l.drop (2 ^ R)).length = 2 ^ R := by
  simp [h, pow_succ]; omega

/-- A block in the left half of a list of `2^(R+1)` elements is a block of that half. -/
theorem block_left {R r w : ℕ} (l : List ℕ) (hr : r ≤ R) (hw : w < 2 ^ (R - r)) :
    block r w l = block r w (l.take (2 ^ R)) := by
  have : (w + 1) * 2 ^ r ≤ 2 ^ R := by
    calc (w + 1) * 2 ^ r ≤ 2 ^ (R - r) * 2 ^ r := Nat.mul_le_mul_right _ hw
      _ = 2 ^ R := by rw [← pow_add, Nat.sub_add_cancel hr]
  simp only [block, List.drop_take, List.take_take]
  congr 1; rw [Nat.add_mul, one_mul] at this; omega

/-- A block in the right half of a list of `2^(R+1)` elements is a block of that half. -/
theorem block_right {R r w : ℕ} (l : List ℕ) (hr : r ≤ R) (hw : 2 ^ (R - r) ≤ w) :
    block r w l = block r (w - 2 ^ (R - r)) (l.drop (2 ^ R)) := by
  have : w * 2 ^ r = 2 ^ R + (w - 2 ^ (R - r)) * 2 ^ r := by
    rw [Nat.sub_mul, ← pow_add, Nat.sub_add_cancel hr]
    have : 2 ^ R ≤ w * 2 ^ r := by
      calc 2 ^ R = 2 ^ (R - r) * 2 ^ r := by rw [← pow_add, Nat.sub_add_cancel hr]
        _ ≤ w * 2 ^ r := Nat.mul_le_mul_right _ hw
    omega
  simp only [block, List.drop_drop, this]

/-- **Blocks split at the top.** The blocks of a list of `2^(R+1)` elements are those of
    its two halves, plus the whole list at level `R + 1`. -/
theorem allBlocks_succ (P : ℕ → List ℕ → Prop) (R : ℕ) (l : List ℕ)
    (h : l.length = 2 ^ (R + 1)) :
    AllBlocks P (R + 1) l ↔
      AllBlocks P R (l.take (2 ^ R)) ∧ AllBlocks P R (l.drop (2 ^ R)) ∧ P (R + 1) l := by
  constructor
  · intro hA
    refine ⟨fun r h1 h2 w hw => ?_, fun r h1 h2 w hw => ?_, ?_⟩
    · rw [← block_left l h2 hw]
      exact hA r h1 (by omega) w (by
        calc w < 2 ^ (R - r) := hw
          _ ≤ 2 ^ (R + 1 - r) := Nat.pow_le_pow_right (by decide) (by omega))
    · have := hA r h1 (by omega) (w + 2 ^ (R - r)) (by
        rw [show R + 1 - r = R - r + 1 by omega, pow_succ]; omega)
      rwa [block_right l h2 (by omega), Nat.add_sub_cancel] at this
    · simpa [block_top _ _ h] using hA (R + 1) (by omega) le_rfl 0 (by simp)
  · rintro ⟨hL, hR, htop⟩ r h1 h2 w hw
    rcases Nat.lt_or_ge R r with hr | hr
    · obtain rfl : r = R + 1 := by omega
      obtain rfl : w = 0 := by simpa using hw
      rwa [block_top _ _ h]
    · rcases Nat.lt_or_ge w (2 ^ (R - r)) with hw' | hw'
      · rw [block_left l hr hw']; exact hL r h1 hr w hw'
      · rw [block_right l hr hw']
        exact hR r h1 hr _ (by
          rw [show R + 1 - r = R - r + 1 by omega, pow_succ] at hw; omega)

/-! ## `Good` is a condition on every block -/

/-- The merge of the two halves of a level-`r` block `b`. -/
def GoodAt (r : ℕ) (b : List ℕ) : Prop :=
  Mergeable H p S (r - 1) (b.take (2 ^ (r - 1))) (b.drop (2 ^ (r - 1)))

/-- `Good`, which checks a block through its halves, is `GoodAt` on every block. -/
theorem good_iff_allBlocks (R : ℕ) (l : List ℕ) (h : l.length = 2 ^ R) :
    Good H p S R l ↔ AllBlocks (GoodAt H p S) R l := by
  induction R generalizing l with
  | zero => simp [Good, AllBlocks]; intro r h1 h2; omega
  | succ R ih =>
    rw [allBlocks_succ _ _ _ h, ← ih _ (length_take_half h), ← ih _ (length_drop_half h)]
    simp only [Good, GoodAt, Mergeable, Nat.add_sub_cancel]

theorem allBlocks_and {P Q : ℕ → List ℕ → Prop} {R : ℕ} {l : List ℕ} :
    AllBlocks (fun r b => P r b ∧ Q r b) R l ↔ AllBlocks P R l ∧ AllBlocks Q R l :=
  ⟨fun h => ⟨fun r h1 h2 w hw => (h r h1 h2 w hw).1, fun r h1 h2 w hw => (h r h1 h2 w hw).2⟩,
   fun h r h1 h2 w hw => ⟨h.1 r h1 h2 w hw, h.2 r h1 h2 w hw⟩⟩

theorem allBlocks_congr {P Q : ℕ → List ℕ → Prop} {R : ℕ} {l : List ℕ}
    (h : ∀ r, 1 ≤ r → r ≤ R → ∀ w < 2 ^ (R - r),
      (P r (block r w l) ↔ Q r (block r w l))) :
    AllBlocks P R l ↔ AllBlocks Q R l :=
  ⟨fun hP r h1 h2 w hw => (h r h1 h2 w hw).mp (hP r h1 h2 w hw),
   fun hQ r h1 h2 w hw => (h r h1 h2 w hw).mpr (hQ r h1 h2 w hw)⟩

/-! ## Distinctness -/

/-- The halves of every block are disjoint exactly when the whole list has no repeats. -/
theorem allBlocks_disjoint_iff_nodup (R : ℕ) (l : List ℕ) (h : l.length = 2 ^ R) :
    AllBlocks (fun r b => ¬ ∃ i ∈ b.take (2 ^ (r - 1)), i ∈ b.drop (2 ^ (r - 1))) R l ↔
      l.Nodup := by
  induction R generalizing l with
  | zero =>
    obtain ⟨j, rfl⟩ := List.length_eq_one_iff.mp h
    simp [AllBlocks]; intro r h1 h2; omega
  | succ R ih =>
    rw [allBlocks_succ _ _ _ h, ih _ (length_take_half h), ih _ (length_drop_half h)]
    conv_rhs => rw [← List.take_append_drop (2 ^ R) l]
    simp only [List.nodup_append, Nat.add_sub_cancel, not_exists, not_and]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun a ha b hb hab => h3 a ha (hab ▸ hb)⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun a ha hb => h3 a ha a hb rfl⟩

/-! ## Ordering -/

theorem length_block {R r w : ℕ} {l : List ℕ} (h : l.length = 2 ^ R) (hr : r ≤ R)
    (hw : w < 2 ^ (R - r)) : (block r w l).length = 2 ^ r := by
  have : (w + 1) * 2 ^ r ≤ 2 ^ R := by
    calc (w + 1) * 2 ^ r ≤ 2 ^ (R - r) * 2 ^ r := Nat.mul_le_mul_right _ hw
      _ = 2 ^ R := by rw [← pow_add, Nat.sub_add_cancel hr]
  simp only [block, List.length_take, List.length_drop, h]
  rw [Nat.add_mul, one_mul] at this
  omega

theorem nodup_block {r w : ℕ} {l : List ℕ} (h : l.Nodup) : (block r w l).Nodup :=
  (h.sublist (List.drop_sublist _ _)).sublist (List.take_sublist _ _)

/-- Lexicographic order between sequences with different first elements is decided by
    those elements. -/
theorem lex_cons_of_ne {a b : ℕ} {l₁ l₂ : List ℕ} (hab : a ≠ b) :
    List.Lex (· < ·) (a :: l₁) (b :: l₂) ↔ a < b := by
  constructor
  · intro h
    cases h with
    | cons => exact absurd rfl hab
    | rel h => exact h
  · exact List.Lex.rel

/-- With distinct indices, the code's ordering check (the right half does not start
    before the left) is §7.7.1's lexicographic ordering of the halves (shifted to the
    specification's 1-based indices). -/
theorem order_iff_lex {b : List ℕ} {h : ℕ} (hb : b.Nodup) (h1 : 0 < h) (h2 : h < b.length) :
    ¬ (b.drop h).headD 0 < (b.take h).headD 0 ↔
      List.Lex (· < ·) ((b.take h).map (· + 1)) ((b.drop h).map (· + 1)) := by
  obtain ⟨x, L, hL⟩ : ∃ x L, b.take h = x :: L := List.exists_cons_of_ne_nil (by
    intro hc; have := congrArg List.length hc
    rw [List.length_take, List.length_nil] at this; omega)
  obtain ⟨y, R, hR⟩ : ∃ y R, b.drop h = y :: R :=
    List.exists_cons_of_ne_nil (by intro hc; have := congrArg List.length hc; simp at this; omega)
  have hxy : x ≠ y := by
    have := List.take_append_drop h b
    rw [hL, hR] at this
    rw [← this] at hb
    intro rfl
    simp [List.nodup_append] at hb
  rw [hL, hR]
  simp only [List.headD_cons, List.map_cons]
  rw [lex_cons_of_ne (by omega)]
  omega

theorem allBlocks_order_iff_lex (R : ℕ) (l : List ℕ) (h : l.length = 2 ^ R) (hl : l.Nodup) :
    AllBlocks (fun r b => ¬ (b.drop (2 ^ (r - 1))).headD 0 < (b.take (2 ^ (r - 1))).headD 0)
        R l ↔
      AllBlocks (fun r b => List.Lex (· < ·) ((b.take (2 ^ (r - 1))).map (· + 1))
        ((b.drop (2 ^ (r - 1))).map (· + 1))) R l := by
  refine allBlocks_congr fun r h1 h2 w hw => order_iff_lex (nodup_block hl)
    (Nat.two_pow_pos _) ?_
  rw [length_block h h2 hw]
  exact Nat.pow_lt_pow_right (by decide) (by omega)

/-! ## Collisions -/

theorem n_eq : p.n = (p.k + 1) * p.digitBits := (Nat.mul_div_cancel' p.n_dvd).symm

theorem length_blockXor (is : List ℕ) : (blockXor H p S is).length = p.n :=
  length_xorAll _ _ fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx; exact length_X H p S _

theorem blockXor_split (l : List ℕ) (m : ℕ) :
    blockXor H p S l = xor (blockXor H p S (l.take m)) (blockXor H p S (l.drop m)) := by
  conv_lhs => rw [← List.take_append_drop m l]
  exact blockXor_append H p S _ _

/-- Agreement on one digit per merge, at every level, is the leading-zeros condition at
    every level. -/
theorem allBlocks_digit_iff_zeros (R : ℕ) (hR : R ≤ p.k + 1) (l : List ℕ)
    (h : l.length = 2 ^ R) :
    AllBlocks (fun r b =>
        ((blockXor H p S (b.take (2 ^ (r - 1)))).drop ((r - 1) * p.digitBits)).take p.digitBits =
        ((blockXor H p S (b.drop (2 ^ (r - 1)))).drop ((r - 1) * p.digitBits)).take p.digitBits)
        R l ↔
      AllBlocks (fun r b => HasLeadingZeros (r * p.digitBits) (blockXor H p S b)) R l := by
  induction R generalizing l with
  | zero => simp [AllBlocks]; constructor <;> intro _ r h1 h2 <;> omega
  | succ R ih =>
    have hL := length_take_half h
    have hRr := length_drop_half h
    rw [allBlocks_succ _ _ _ h, allBlocks_succ _ _ _ h, ih (by omega) _ hL, ih (by omega) _ hRr]
    simp only [Nat.add_sub_cancel]
    refine and_congr_right fun hAL => and_congr_right fun hAR => ?_
    -- Both halves already start with `R` zero digits: from their top block, or vacuously.
    have hz : ∀ l' : List ℕ, l'.length = 2 ^ R →
        AllBlocks (fun r b => HasLeadingZeros (r * p.digitBits) (blockXor H p S b)) R l' →
        HasLeadingZeros (R * p.digitBits) (blockXor H p S l') := by
      intro l' hl' hA
      rcases Nat.eq_zero_or_pos R with rfl | hpos
      · simp [HasLeadingZeros]
      · simpa [block_top _ _ hl'] using hA R hpos le_rfl 0 (by simp)
    have hn := n_eq p
    rw [blockXor_split H p S l (2 ^ R), Nat.succ_mul,
      hasLeadingZeros_xor (length_blockXor H p S _) (length_blockXor H p S _)
        (by rw [hn, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega))
        (hz _ hL hAL) (hz _ hRr hAR)]

/-! ## The specification's notation -/

/-- §7.7.1's `i_{w·2^r+1 .. w·2^r+2^r}` is block `w` at level `r`. -/
theorem range_block (l : List ℕ) (f : ℕ → ℕ) (r w : ℕ) :
    range (l.map f) (w * 2 ^ r + 1) (w * 2 ^ r + 2 ^ r) = (block r w l).map f := by
  simp only [range, block, List.map_take, List.map_drop]
  generalize 2 ^ r = t
  rw [show w * t + 1 - 1 = w * t by omega, show w * t + t + 1 - (w * t + 1) = t by omega]

/-- The first half of block `w` at level `r ≥ 1`, in §7.7.1's notation. -/
theorem range_block_left (l : List ℕ) (f : ℕ → ℕ) {r : ℕ} (hr : 1 ≤ r) (w : ℕ) :
    range (l.map f) (w * 2 ^ r + 1) (w * 2 ^ r + 2 ^ (r - 1)) =
      ((block r w l).take (2 ^ (r - 1))).map f := by
  have : 2 ^ (r - 1) ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) (by omega)
  simp only [range, block, List.map_take, List.map_drop, List.take_take]
  generalize 2 ^ r = t at this ⊢
  generalize 2 ^ (r - 1) = u at this ⊢
  rw [show w * t + 1 - 1 = w * t by omega, show w * t + u + 1 - (w * t + 1) = u by omega,
    Nat.min_eq_left this]

/-- The second half of block `w` at level `r ≥ 1`, in §7.7.1's notation. -/
theorem range_block_right (l : List ℕ) (f : ℕ → ℕ) {r : ℕ} (hr : 1 ≤ r) (w : ℕ) :
    range (l.map f) (w * 2 ^ r + 2 ^ (r - 1) + 1) (w * 2 ^ r + 2 ^ r) =
      ((block r w l).drop (2 ^ (r - 1))).map f := by
  have h2 : 2 ^ r = 2 ^ (r - 1) * 2 := by rw [← pow_succ]; congr 1; omega
  simp only [range, block, List.map_take, List.map_drop, List.drop_take, List.drop_drop]
  generalize 2 ^ r = t at h2 ⊢
  generalize 2 ^ (r - 1) = u at h2 ⊢
  rw [show w * t + u + 1 - 1 = w * t + u by omega,
    show w * t + t + 1 - (w * t + u + 1) = t - u by omega]

/-- `n·r/(k+1)`, §7.7.1's count of leading zeros at level `r`, is `r` digits. -/
theorem leadingZeros_eq (r : ℕ) : p.n * r / (p.k + 1) = r * p.digitBits := by
  rw [n_eq p, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by omega), Nat.mul_comm]

/-! ## The tree's checks are §7.7.1's conditions -/

/-- **The tree's checks are §7.7.1's conditions.** For `2^k` indices below `N`, the tree is
    `Good` and the root's last digit is zero exactly when the indices (shifted to §7.7.1's
    1-based ones) are a valid solution with no index repeated. -/
theorem good_iff_validSolution (is : List ℕ) (hlen : is.length = 2 ^ p.k)
    (hbound : ∀ j ∈ is, j < p.N) :
    Good H p S p.k is ∧
        ((blockXor H p S is).drop (p.k * p.digitBits)).take p.digitBits = zeros p.digitBits ↔
      ValidSolution H p S (is.map (· + 1)) ∧ is.Nodup := by
  have hX : (is.map (· + 1)).map (X H p S) = is.map fun j => X H p S (j + 1) := by
    simp [List.map_map, Function.comp_def]
  -- The tree's checks, as three conditions on every block.
  rw [good_iff_allBlocks H p S _ _ hlen]
  have hsplit : AllBlocks (GoodAt H p S) p.k is ↔ _ :=
    allBlocks_and.trans (and_congr_right fun _ => allBlocks_and)
  rw [hsplit, allBlocks_disjoint_iff_nodup _ _ hlen,
    allBlocks_digit_iff_zeros H p S _ (by omega) _ hlen]
  -- The specification's conditions, in the same terms.
  have hcol : CollisionCondition H p S (is.map (· + 1)) ↔
      ∀ r, 1 ≤ r → r ≤ p.k - 1 → ∀ w < 2 ^ (p.k - r),
        HasLeadingZeros (r * p.digitBits) (blockXor H p S (block r w is)) := by
    simp only [CollisionCondition, range_block, leadingZeros_eq, blockXor, List.map_map,
      Function.comp_def]
  have hord : OrderingCondition p (is.map (· + 1)) ↔
      AllBlocks (fun r b => List.Lex (· < ·) ((b.take (2 ^ (r - 1))).map (· + 1))
        ((b.drop (2 ^ (r - 1))).map (· + 1))) p.k is := by
    constructor <;> intro h r h1 h2 w hw
    · simpa [range_block_left _ _ h1, range_block_right _ _ h1] using h r h1 h2 w hw
    · simpa [range_block_left _ _ h1, range_block_right _ _ h1] using h r h1 h2 w hw
  have hbirth : GeneralizedBirthday H p S (is.map (· + 1)) ↔
      blockXor H p S is = zeros (p.k * p.digitBits + p.digitBits) := by
    simp only [GeneralizedBirthday, hX, blockXor]
    rw [n_eq p, Nat.succ_mul]
  -- The top level of the leading-zeros condition is part of the Birthday condition.
  have htop : AllBlocks (fun r b => HasLeadingZeros (r * p.digitBits) (blockXor H p S b)) p.k is ↔
      (∀ r, 1 ≤ r → r ≤ p.k - 1 → ∀ w < 2 ^ (p.k - r),
        HasLeadingZeros (r * p.digitBits) (blockXor H p S (block r w is))) ∧
      HasLeadingZeros (p.k * p.digitBits) (blockXor H p S is) := by
    have hk := p.k_ge
    constructor
    · intro h
      exact ⟨fun r h1 h2 w hw => h r h1 (by omega) w hw,
        by simpa [block_top _ _ hlen] using h p.k (by omega) le_rfl 0 (by simp)⟩
    · rintro ⟨h, htop⟩ r h1 h2 w hw
      rcases Nat.lt_or_ge r p.k with hr | hr
      · exact h r h1 (by omega) w hw
      · obtain rfl : r = p.k := by omega
        obtain rfl : w = 0 := by simpa using hw
        simpa [block_top _ _ hlen] using htop
  have hlenX := length_blockXor H p S is
  rw [n_eq p, Nat.succ_mul] at hlenX
  constructor
  · rintro ⟨⟨hD, hO, hN⟩, hroot⟩
    rw [allBlocks_order_iff_lex _ _ hlen hN, ← hord] at hO
    rw [htop] at hD
    refine ⟨⟨by simp [hlen], fun j hj => ?_, ?_, hcol.mpr hD.1, hO⟩, hN⟩
    · obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hj; exact ⟨by omega, hbound j' hj'⟩
    · rw [hbirth, eq_zeros_split _ _ _ hlenX, ← hasLeadingZeros_iff (by omega)]
      exact ⟨hD.2, hroot⟩
  · rintro ⟨⟨-, -, hB, hC, hO⟩, hN⟩
    rw [hbirth, eq_zeros_split _ _ _ hlenX, ← hasLeadingZeros_iff (by omega)] at hB
    refine ⟨⟨htop.mpr ⟨hcol.mp hC, hB.1⟩, ?_, hN⟩, hB.2⟩
    rw [allBlocks_order_iff_lex _ _ hlen hN, ← hord]; exact hO

end Equihash
