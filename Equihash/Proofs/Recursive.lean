/-
The recursive verifier is correct: `tree_validator` checks exactly that a block is `Good`,
so `is_valid_solution_recursive` accepts exactly §7.7.1's valid solutions with distinct
indices.
-/
module

public import Equihash.Proofs.Node

@[expose] public section

namespace Equihash.Verifier

open Equihash Equihash.Spec

variable {rp : Params} {p : ZakuraParams}

/-- What `tree_validator` returns on block `l` of height `r`: the node over `l` when the
    block is `Good`, nothing when it is not. -/
def Checked (p : ZakuraParams) (S : List Byte) (r : ℕ) (l : List ℕ) : Option Node → Prop
  | some node => Good Blake2b.hashFn p.toParams S r l ∧ NodeRel p S r node l
  | none => ¬ Good Blake2b.hashFn p.toParams S r l

/-- **`tree_validator`** checks a block of `2^r` indices: it returns the node over the block
    when the block is `Good`, and fails when it is not. -/
theorem treeValidator?_spec (h : rp.Is p) {S : List Byte} {st : Blake2b.State}
    (hst : StateFor p.toParams S st) (r : ℕ) :
    ∀ l : List ℕ, r ≤ p.k → l.length = 2 ^ r → Checked p S r l (treeValidator? rp st l) := by
  induction r with
  | zero =>
    intro l _ hl
    obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp hl
    obtain ⟨node, hnode, hi, hE⟩ := Node.new?_spec h hst i
    rw [treeValidator?]
    simp only [List.length_singleton, gt_iff_lt, lt_self_iff_false, ↓reduceDIte,
      List.getElem?_cons_zero, Option.bind_eq_bind, Option.bind_some, hnode]
    refine ⟨trivial, hi, rfl, ?_⟩
    simpa [rest, blockXor_singleton] using hE
  | succ r ih =>
    intro l hr hl
    have hL := length_take_half hl
    have hR := length_drop_half hl
    have hmid : l.length / 2 = 2 ^ r := by rw [hl, Nat.pow_succ]; omega
    have h1 : l.length > 1 := by rw [hl]; exact Nat.one_lt_two_pow (by omega)
    rw [treeValidator?]
    simp only [h1, ↓reduceDIte, hmid, Option.bind_eq_bind]
    -- The left half.
    have hA := ih (l.take (2 ^ r)) (by omega) hL
    rcases ha : treeValidator? rp st (l.take (2 ^ r)) with _ | a <;> rw [ha] at hA
    · simpa [Checked, Good] using fun h _ => absurd h hA
    obtain ⟨gA, hA⟩ := hA
    -- The right half.
    have hB := ih (l.drop (2 ^ r)) (by omega) hR
    rcases hb : treeValidator? rp st (l.drop (2 ^ r)) with _ | b <;> rw [hb] at hB
    · simpa [Checked, Good] using fun _ h _ => absurd h hB
    obtain ⟨gB, hB⟩ := hB
    -- Their merge.
    have hM := validateSubtrees?_iff h hA hB (by omega)
    simp only [Option.bind_some]
    by_cases hm : Mergeable Blake2b.hashFn p.toParams S r (l.take (2 ^ r)) (l.drop (2 ^ r))
    · obtain ⟨n, hn, hrel⟩ := fromChildren?_spec hA hB hm
      rw [hM.mpr hm]
      simp only [Option.bind_some, Params.collisionByteLength_eq h, hn]
      rw [List.take_append_drop] at hrel
      exact ⟨⟨gA, gB, hm⟩, hrel⟩
    · have hv : validateSubtrees? rp a b = none := by
        rcases hv : validateSubtrees? rp a b with _ | ⟨⟩
        · rfl
        · exact absurd (hM.mp hv) hm
      rw [hv]
      simp only [Option.bind_none, Checked, Good]
      exact fun ⟨_, _, h'⟩ => hm h'

/-- **The recursive verifier checks the tree.** On `2^k` indices, `is_valid_solution_recursive`
    accepts exactly when the indices form a `Good` tree whose root's last digit is zero, for
    BLAKE2b over the input followed by the nonce. -/
theorem isValidSolutionRecursive?_iff (h : rp.Is p) (input nonce indices : List ℕ)
    (hin : Bytes input) (hnon : Bytes nonce) (hlen : indices.length = 2 ^ p.k) :
    isValidSolutionRecursive? rp input nonce indices = some () ↔
      Good Blake2b.hashFn p.toParams (bytesOf (input ++ nonce)) p.k indices ∧
        (rest p (bytesOf (input ++ nonce)) p.k indices).take p.digitBits = zeros p.digitBits := by
  obtain ⟨st, hst0, hst⟩ := initialiseState?_spec h
  have hst' : StateFor p.toParams (bytesOf (input ++ nonce)) ((st.update input).update nonce) := by
    simpa [List.map_append] using (hst.update input hin).update nonce hnon
  have hT := treeValidator?_spec h hst' p.k indices le_rfl hlen
  simp only [isValidSolutionRecursive?, hst0, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some]
  rcases ht : treeValidator? rp ((st.update input).update nonce) indices with _ | root <;>
    rw [ht] at hT
  · simpa using fun g _ => hT g
  obtain ⟨g, hroot⟩ := hT
  simp only [Option.bind_some]
  rw [Params.collisionByteLength_eq h, isZero_eq hroot]
  by_cases hZ : (rest p (bytesOf (input ++ nonce)) p.k indices).take p.digitBits =
      zeros p.digitBits
  · simp only [hZ, decide_true, ↓reduceIte, true_iff, and_true]
    exact g
  · simp only [hZ, decide_false, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, and_false]

/-- **The recursive verifier is correct.** On `2^k` indices below `N` (the range the minimal
    encoding can express; the verifier does not check it), `is_valid_solution_recursive`
    accepts exactly the solutions valid by §7.7.1, for `powheader` the input followed by the
    nonce, whose indices are distinct. -/
theorem isValidSolutionRecursive?_correct (h : rp.Is p) (input nonce indices : List ℕ)
    (hin : Bytes input) (hnon : Bytes nonce) (hlen : indices.length = 2 ^ p.k)
    (hbound : ∀ j ∈ indices, j < p.N) :
    isValidSolutionRecursive? rp input nonce indices = some () ↔
      ValidSolution Blake2b.hashFn p.toParams (bytesOf (input ++ nonce)) (indices.map (· + 1)) ∧
        indices.Nodup :=
  (isValidSolutionRecursive?_iff h input nonce indices hin hnon hlen).trans
    (good_iff_validSolution _ _ _ _ hlen hbound)

-- The build fails if the theorem rests on anything beyond Lean's three axioms.
/--
info: 'Equihash.Verifier.isValidSolutionRecursive?_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms isValidSolutionRecursive?_correct

end Equihash.Verifier
