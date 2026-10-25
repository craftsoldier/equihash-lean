/-
Merging nodes: what `has_collision`, `distinct_indices`, `validate_subtrees`,
`from_children` and `is_zero` compute, in terms of `Spec`.
-/
module

public import Equihash.Proofs.Leaf

@[expose] public section

namespace Equihash.Verifier

open Equihash Equihash.Spec

/-! ## The checks -/

/-- `has_collision` compares the first `len` bytes of the two hashes. -/
theorem hasCollision_iff (a b : Node) (w : ℕ) (ha : w ≤ a.hash.length) (hb : w ≤ b.hash.length) :
    hasCollision a b w = true ↔ a.hash.take w = b.hash.take w := by
  unfold hasCollision
  rw [List.zip_eq_zipWith, List.take_zipWith, ← List.zip_eq_zipWith]
  have hl₁ : (a.hash.take w).length = w := by simp [ha]
  have hl₂ : (b.hash.take w).length = w := by simp [hb]
  generalize a.hash.take w = x at *
  generalize b.hash.take w = y at *
  clear ha hb
  induction x generalizing y w with
  | nil => cases y <;> simp_all; omega
  | cons u x ih =>
    cases y with
    | nil => simp_all; omega
    | cons v y =>
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, List.cons.injEq,
        beq_iff_eq]
      exact and_congr_right fun _ =>
        ih (w - 1) (by simp at hl₁; omega) y (by simp at hl₂; omega)

/-- `distinct_indices` returns `false` at the first equal pair: it checks that every pair
    differs. -/
theorem distinctIndices_eq (a b : Node) :
    distinctIndices a b = a.indices.all fun i => b.indices.all fun j => i != j := by
  -- The inner loop stops at `i` in `b`, or runs to the end.
  have inner : ∀ (i : ℕ) (js : List ℕ),
      (forIn (m := Id) js ((none, ()) : Option Bool × Unit) fun j _ =>
        if (i == j) = true then pure (ForInStep.done (some false, ()))
        else pure (ForInStep.yield (none, ()))) =
      if js.all (fun j => i != j) then (none, ()) else (some false, ()) := by
    intro i js
    induction js with
    | nil => rfl
    | cons j js ih =>
      by_cases h : i = j
      · subst h; simp; rfl
      · have hb : (i == j) = false := beq_false_of_ne h
        simp only [List.forIn_cons, hb, Bool.false_eq_true, ↓reduceIte, pure_bind, List.all_cons]
        simp only [show (i != j) = true from bne_iff_ne.mpr h, Bool.true_and]
        exact ih
  unfold distinctIndices
  simp only [inner]
  generalize a.indices = is
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.forIn_cons, List.all_cons]
    by_cases h : (b.indices.all fun j => i != j) = true
    · simp only [h, ↓reduceIte, Bool.true_and]
      exact ih
    · simp only [h, Bool.false_and]
      rfl

theorem distinctIndices_iff (a b : Node) :
    distinctIndices a b = true ↔ ¬ ∃ i ∈ a.indices, i ∈ b.indices := by
  simp only [distinctIndices_eq, List.all_eq_true, bne_iff_ne, ne_eq, not_exists, not_and]
  exact ⟨fun h x hx hxb => h x hx x hxb rfl, fun h x hx y hy hxy => h x hx (hxy ▸ hy)⟩

theorem ne_nil_of_length_pow {l : List ℕ} {r : ℕ} (h : l.length = 2 ^ r) : l ≠ [] := by
  rintro rfl
  rw [List.length_nil] at h
  exact absurd h.symm (by positivity)

/-! ## Nodes as blocks -/

/-- The hash a node of height `r` over block `l` carries: the XOR of the block's hash values,
    without the first `r` digits (the ones its merges checked). -/
abbrev rest (p : ZakuraParams) (S : List Byte) (r : ℕ) (l : List ℕ) : Bits :=
  (blockXor Blake2b.hashFn p.toParams S l).drop (r * p.digitBits)

theorem length_rest (p : ZakuraParams) (S : List Byte) (r : ℕ) (l : List ℕ) :
    (rest p S r l).length = (p.k + 1 - r) * p.digitBits := by
  rw [List.length_drop, length_blockXor, n_eq, Nat.sub_mul]

/-- **The node invariant.** A node of height `r` holds block `l` of `2^r` indices, and its
    hash is the expansion of `rest`. -/
def NodeRel (p : ZakuraParams) (S : List Byte) (r : ℕ) (node : Node) (l : List ℕ) : Prop :=
  node.indices = l ∧ l.length = 2 ^ r ∧
  ExpandedN p.digitBits ((p.digitBits + 7) / 8) node.hash (rest p S r l)

section Merge
variable {rp : Params} {p : ZakuraParams} {S : List Byte} {r : ℕ} {a b : Node}
  {la lb : List ℕ}

/-- The first index of a node is its block's. -/
theorem NodeRel.head (h : NodeRel p S r a la) : a.indices[0]? = some (la.headD 0) := by
  obtain ⟨rfl, hlen, -⟩ := h
  obtain ⟨x, l, hxl⟩ := List.exists_cons_of_ne_nil (ne_nil_of_length_pow hlen)
  rw [hxl]
  rfl

/-- An expanded hash of a node below the root has at least one digit's worth of bytes. -/
theorem NodeRel.width_le (h : NodeRel p S r a la) (hr : r ≤ p.k) :
    (p.digitBits + 7) / 8 ≤ a.hash.length ∧ p.digitBits ≤ (rest p S r la).length ∧
      1 ≤ (rest p S r la).length / p.digitBits := by
  obtain ⟨-, -, hE⟩ := h
  have hl := length_rest p S r la
  have hc : 0 < p.digitBits := by have : 8 ≤ p.digitBits := p.digit_ge; omega
  have hq : (rest p S r la).length / p.digitBits = p.k + 1 - r := by
    rw [hl, Nat.mul_div_cancel _ hc]
  have hlen := hE.1
  rw [hq] at hlen
  refine ⟨?_, ?_, by omega⟩
  · rw [hlen]; exact Nat.le_mul_of_pos_left _ (by omega)
  · rw [hl]; exact Nat.le_mul_of_pos_left _ (by omega)

/-- **`validate_subtrees`** returns, without panicking, `Ok(())` for sibling nodes exactly when
    their blocks are `Mergeable`. -/
theorem validateSubtrees?_spec (h : rp.Is p) (ha : NodeRel p S r a la)
    (hb : NodeRel p S r b lb) (hr : r < p.k) :
    ∃ e, (validateSubtrees? rp a b).run = some e ∧
      (e = .ok () ↔ Mergeable Blake2b.hashFn p.toParams S r la lb) := by
  have hc8 : 8 ≤ p.digitBits := p.digit_ge
  obtain ⟨hwa, hca, h1a⟩ := ha.width_le hr.le
  obtain ⟨hwb, hcb, h1b⟩ := hb.width_le hr.le
  -- The three checks, on the blocks.
  have hcol : hasCollision a b ((p.digitBits + 7) / 8) = true ↔
      (rest p S r la).take p.digitBits = (rest p S r lb).take p.digitBits := by
    rw [hasCollision_iff _ _ _ hwa hwb,
      ExpandedN.take_eq_iff (by omega) ha.2.2 hb.2.2 h1a h1b hca hcb]
  have hord : b.indicesBefore? a = some (decide (lb.headD 0 < la.headD 0)) := by
    simp [Node.indicesBefore?, ha.head, hb.head]
  have hdis : distinctIndices a b = true ↔ ¬ ∃ i ∈ la, i ∈ lb := by
    rw [distinctIndices_iff, ha.1, hb.1]
  generalize hd : decide (lb.headD 0 < la.headD 0) = d at hord
  simp only [validateSubtrees?, Params.collisionByteLength_eq h, hord, Mergeable, ← hcol,
    ← hdis]
  cases hc : hasCollision a b ((p.digitBits + 7) / 8) <;>
    cases hdi : distinctIndices a b <;> cases d <;> refine ⟨_, rfl, ?_⟩ <;>
    simp_all [decide_eq_false_iff_not]

/-- **`from_children`** merges `Mergeable` sibling nodes into the node over both blocks. -/
theorem fromChildren?_spec (ha : NodeRel p S r a la) (hb : NodeRel p S r b lb)
    (hm : Mergeable Blake2b.hashFn p.toParams S r la lb) :
    ∃ n, Node.fromChildren? a b ((p.digitBits + 7) / 8) = some n ∧
      NodeRel p S (r + 1) n (la ++ lb) := by
  obtain ⟨-, hO, hD⟩ := hm
  have hxa := ha.head
  have hxb := hb.head
  obtain ⟨hia, hla, hEa⟩ := ha
  obtain ⟨hib, hlb, hEb⟩ := hb
  -- The left block starts first: its first index is smaller, and they differ.
  have hlt : la.headD 0 < lb.headD 0 := by
    have hne : la.headD 0 ≠ lb.headD 0 := by
      intro he; apply hD
      obtain ⟨x, l, rfl⟩ := List.exists_cons_of_ne_nil (ne_nil_of_length_pow hla)
      obtain ⟨y, l', rfl⟩ := List.exists_cons_of_ne_nil (ne_nil_of_length_pow hlb)
      exact ⟨x, by simp, by simp at he; simp [he]⟩
    omega
  have hbefore : a.indicesBefore? b = some true := by
    simpa [Node.indicesBefore?, hxa, hxb] using hlt
  -- The new hash drops one more digit of the XOR of both blocks.
  have hrest : (xor (rest p S r la) (rest p S r lb)).drop p.digitBits =
      rest p S (r + 1) (la ++ lb) := by
    simp only [rest, blockXor_append, Nat.succ_mul, drop_xor, List.drop_drop]
  refine ⟨⟨((a.hash.zip b.hash).drop ((p.digitBits + 7) / 8)).map fun (x, y) => x ^^^ y,
    a.indices ++ b.indices⟩, by simp [Node.fromChildren?, hbefore], ?_, ?_, ?_⟩
  · simp [hia, hib]
  · rw [List.length_append, hla, hlb, Nat.pow_succ]; omega
  · simp only [List.map_drop, List.zip_eq_zipWith, List.map_zipWith, ← hrest]
    exact ExpandedN.xor_drop hEa hEb (by rw [length_rest, length_rest])

/-- **`is_zero`**: the root's first expanded digit is zero exactly when the last digit of its
    block's XOR is. -/
theorem isZero_eq (ha : NodeRel p S p.k a la) :
    a.isZero ((p.digitBits + 7) / 8) =
      decide ((rest p S p.k la).take p.digitBits = zeros p.digitBits) := by
  have hc8 : 8 ≤ p.digitBits := p.digit_ge
  obtain ⟨hwa, hca, h1a⟩ := ha.width_le le_rfl
  rw [Bool.eq_iff_iff, decide_eq_true_iff,
    ← ExpandedN.take_eq_zero_iff (by omega) ha.2.2 h1a hca, List.eq_replicate_iff]
  simp [Node.isZero, List.all_eq_true, hwa]

end Merge

end Equihash.Verifier
