/-
The single-pass verifier checks the same tree as the recursive one: `validate_tree` accepts
exactly the `Good` trees whose root digit is zero.
-/
module

public import Equihash.Proofs.Recursive
public import Init.Internal.Order.While

@[expose] public section

namespace Equihash.Verifier

open Equihash Equihash.Spec

/-! ## Loops -/

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

/-- The `while` loop's unfolding: one pass, then the rest. -/
theorem loop_unfold {β : Type} {b : β} {f : Unit → β → Option (ForInStep β)} :
    forIn Lean.Loop.mk b f = (do
      match ← f () b with
      | .done val => pure val
      | .yield val => forIn Lean.Loop.mk val f) :=
  Lean.Loop.forIn_eq_of_monadTail

/-! ## `blocks[j] = index / per_hash` -/

/-- Setting position `j` of each `(x, j)` from `l.zipIdx k` writes `l.map f` from position `k`. -/
theorem foldl_set_zipIdx {α : Type} (f : α → ℕ) (l : List α) (k : ℕ) (s : List ℕ)
    (hs : s.length = k + l.length) :
    (l.zipIdx k).foldl (fun s x => s.set x.2 (f x.1)) s = s.take k ++ l.map f := by
  induction l generalizing k s with
  | nil => simp [List.take_of_length_le (by simp at hs; omega : s.length ≤ k)]
  | cons a l ih =>
    simp only [List.length_cons] at hs
    simp only [List.zipIdx_cons, List.foldl_cons, List.map_cons]
    rw [ih (k + 1) _ (by simp only [List.length_set]; omega)]
    have hk : k < s.length := by omega
    rw [List.take_add_one, List.getElem?_set_self hk, List.take_set_of_le (le_refl k)]
    simp

/-! ## `row[i] = left ^ row[collision_bytes + i]` -/

/-- The in-place XOR loop: writing `seg[i] ^ row[cb + i]` at position `i`, in increasing `i`,
    reads only positions not yet written, since `cb ≥ 1`. -/
theorem foldlM_xor (cb : ℕ) (hcb : 1 ≤ cb) (seg : List ℕ) (k : ℕ) (row : List ℕ)
    (hlen : k + seg.length + cb ≤ row.length) :
    (seg.zipIdx k).foldlM (fun row x => do
        let v ← row[cb + x.2]?
        pure (row.set x.2 (x.1 ^^^ v))) row =
      some (row.take k ++ List.zipWith (· ^^^ ·) seg (row.drop (k + cb)) ++
        row.drop (k + seg.length)) := by
  simp only [Option.pure_def, Option.bind_eq_bind]
  induction seg generalizing k row with
  | nil => simp
  | cons a seg ih =>
    simp only [List.length_cons] at hlen
    simp only [List.zipIdx_cons, List.foldlM_cons]
    have hk : cb + k < row.length := by omega
    rw [List.getElem?_eq_getElem hk]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [ih (k + 1) _ (by simp only [List.length_set]; omega)]
    have hk' : k < row.length := by omega
    have hd : row.drop (k + cb) = row[cb + k] :: row.drop (k + 1 + cb) := by
      rw [List.drop_eq_getElem_cons (by omega)]; simp [Nat.add_comm k cb, Nat.add_right_comm]
    congr 1
    simp only [List.length_cons, List.zipWith_cons_cons, List.drop_set, List.take_add_one,
      List.getElem?_set_self hk', List.take_set_of_le (le_refl k), hd,
      show k < k + 1 + cb by omega, show k < k + 1 + seg.length by omega, ↓reduceIte]
    simp [Nat.add_assoc, Nat.add_comm 1 seg.length]

/-! ## Leaf counts

After leaf `c`, the walk merges at every height `h` whose bits `0 .. h` of `c` are set, that
is, where `2^(h+1)` divides `c + 1`. -/

theorem shiftRight_and_one (c h : ℕ) : (c >>> h) &&& 1 = c / 2 ^ h % 2 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]

/-- When `2^h` divides `c + 1`, leaf `c` ends block `c / 2^h` of height `h`. -/
theorem succ_eq_of_mod {c P : ℕ} (hP : 0 < P) (h : (c + 1) % P = 0) :
    c + 1 = (c / P + 1) * P := by
  obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero h
  have hm1 : 1 ≤ m := by rcases m with _ | m <;> simp_all
  have hq : c / P = m - 1 := by
    apply Nat.div_eq_of_lt_le
    · rw [Nat.sub_mul, one_mul, Nat.mul_comm]; omega
    · rw [Nat.sub_add_cancel hm1, Nat.mul_comm]; omega
  rw [hq, Nat.sub_add_cancel hm1, hm, Nat.mul_comm]

/-- Bit `h` of `c` is set, and bits below it too, exactly when `2^(h+1)` divides `c + 1`. -/
theorem mod_succ_pow_succ {c h : ℕ} (h0 : (c + 1) % 2 ^ h = 0) :
    (c + 1) % 2 ^ (h + 1) = 0 ↔ c / 2 ^ h % 2 = 1 := by
  have hc := succ_eq_of_mod (Nat.two_pow_pos h) h0
  rw [hc, Nat.pow_succ, Nat.mul_comm (c / 2 ^ h + 1), Nat.mul_mod_mul_left, Nat.mul_eq_zero]
  have := Nat.two_pow_pos h
  omega

/-- A block of height `h + 1` is its two halves of height `h`. -/
theorem block_succ (h w : ℕ) (L : List ℕ) :
    block (h + 1) w L = block h (2 * w) L ++ block h (2 * w + 1) L := by
  simp only [block]
  rw [show 2 ^ (h + 1) = 2 ^ h + 2 ^ h by ring, List.take_add, List.drop_drop]
  congr 1 <;> congr 2 <;> ring

/-! ## `Good`, leaf by leaf -/

/-- The merges leaf `c` completes are good: each block of height `h + 1` ending at leaf `c` is
    `GoodAt`. -/
def LeafGood (H : HashFn) (p : Spec.Params) (S : List Byte) (L : List ℕ) (c : ℕ) : Prop :=
  ∀ h, (c + 1) % 2 ^ (h + 1) = 0 → GoodAt H p S (h + 1) (block (h + 1) (c / 2 ^ (h + 1)) L)

/-- A tree is `Good` exactly when the merges every leaf completes are. -/
theorem good_iff_leafGood (H : HashFn) (p : Spec.Params) (S : List Byte) (k : ℕ)
    (L : List ℕ) (hL : L.length = 2 ^ k) :
    Good H p S k L ↔ ∀ c < 2 ^ k, LeafGood H p S L c := by
  rw [good_iff_allBlocks H p S k L hL]
  constructor
  · intro hA c hc h hmod
    have hP := Nat.two_pow_pos (h + 1)
    have hc1 := succ_eq_of_mod hP hmod
    have hr : h + 1 ≤ k := by
      by_contra hlt
      have h1 : 2 ^ k < 2 ^ (h + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ (h + 1) ≤ c + 1 := by rw [hc1]; exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      omega
    refine hA (h + 1) (by omega) hr _ ?_
    rw [Nat.div_lt_iff_lt_mul hP, ← Nat.pow_add, Nat.sub_add_cancel hr]
    exact hc
  · intro hG r h1 h2 w hw
    have hP := Nat.two_pow_pos r
    have hwk : (w + 1) * 2 ^ r ≤ 2 ^ k := by
      calc (w + 1) * 2 ^ r ≤ 2 ^ (k - r) * 2 ^ r := Nat.mul_le_mul_right _ hw
        _ = 2 ^ k := by rw [← Nat.pow_add, Nat.sub_add_cancel h2]
    have hpos : 1 ≤ (w + 1) * 2 ^ r := Nat.mul_pos (by omega) hP
    have hq : ((w + 1) * 2 ^ r - 1) / 2 ^ r = w := by
      apply Nat.div_eq_of_lt_le
      · rw [Nat.add_mul, one_mul] at hpos ⊢; omega
      · rw [Nat.add_mul, one_mul] at hpos ⊢; omega
    have := hG ((w + 1) * 2 ^ r - 1) (by omega) (r - 1) (by
      rw [Nat.sub_add_cancel h1, Nat.sub_add_cancel hpos, Nat.mul_mod_left])
    rwa [Nat.sub_add_cancel h1, hq] at this

/-! ## The walk's state -/

section Walk

variable (p : ZakuraParams) (S : List Byte) (L : List ℕ)

/-- Slot `h` of `pending`: the trimmed hash of the unmerged left subtree of height `h`. -/
def slot (pending : List ℕ) (h : ℕ) : List ℕ :=
  (pending.drop (h * ((p.k + 1) * ((p.digitBits + 7) / 8)))).take
    ((p.k + 1 - h) * ((p.digitBits + 7) / 8))

/-- `pending` after `c` leaves: for each set bit `h` of `c`, slot `h` holds the block of height
    `h` that ends where the current run of leaves begins. -/
def PendingRel (c : ℕ) (pending : List ℕ) : Prop :=
  pending.length = (p.k + 1) * ((p.k + 1) * ((p.digitBits + 7) / 8)) ∧
  ∀ h ≤ p.k, c / 2 ^ h % 2 = 1 →
    ExpandedN p.digitBits ((p.digitBits + 7) / 8) (slot p pending h)
      (rest p S h (block h (c / 2 ^ h - 1) L))

/-- `row` while leaf `c` climbs to height `h`: it holds the block of height `h` that ends at
    leaf `c`. -/
def RowRel (c : ℕ) (row : List ℕ) (h : ℕ) : Prop :=
  row.length = (p.k + 1) * ((p.digitBits + 7) / 8) ∧ h ≤ p.k ∧ (c + 1) % 2 ^ h = 0 ∧
    ExpandedN p.digitBits ((p.digitBits + 7) / 8)
      (row.take ((p.k + 1 - h) * ((p.digitBits + 7) / 8)))
      (rest p S h (block h (c / 2 ^ h) L))

/-- The merges leaf `c` completes from height `h` up are good. -/
def MergesFrom (c h : ℕ) : Prop :=
  ∀ h' ≥ h, (c + 1) % 2 ^ (h' + 1) = 0 →
    GoodAt Blake2b.hashFn p.toParams S (h' + 1) (block (h' + 1) (c / 2 ^ (h' + 1)) L)

variable {p S L}

/-- The merge at height `h` of leaf `c`'s walk joins the block before the current run with
    the run itself. -/
theorem goodAt_iff_mergeable (hL : L.length = 2 ^ p.k) {c h : ℕ} (hc : c < 2 ^ p.k)
    (hmod : (c + 1) % 2 ^ (h + 1) = 0) :
    GoodAt Blake2b.hashFn p.toParams S (h + 1) (block (h + 1) (c / 2 ^ (h + 1)) L) ↔
      Mergeable Blake2b.hashFn p.toParams S h (block h (c / 2 ^ h - 1) L)
        (block h (c / 2 ^ h) L) := by
  have hP := Nat.two_pow_pos (h + 1)
  have hc1 := succ_eq_of_mod hP hmod
  have hhk : h + 1 ≤ p.k := by
    by_contra hlt
    have h1 : 2 ^ p.k < 2 ^ (h + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (h + 1) ≤ c + 1 := by rw [hc1]; exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    omega
  -- `c / 2^h` is odd: the run is a right child.
  have hdiv : c / 2 ^ h = 2 * (c / 2 ^ (h + 1)) + 1 := by
    have h0 : (c + 1) % 2 ^ h = 0 := by
      obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero hmod
      rw [hm, Nat.pow_succ, Nat.mul_assoc, Nat.mul_mod_right]
    have hbit := (mod_succ_pow_succ h0).mp hmod
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    omega
  have hw : c / 2 ^ (h + 1) < 2 ^ (p.k - (h + 1)) := by
    rw [Nat.div_lt_iff_lt_mul hP, ← Nat.pow_add, Nat.sub_add_cancel hhk]; exact hc
  have hlen := length_block hL (by omega : h ≤ p.k) (w := 2 * (c / 2 ^ (h + 1))) (by
    rw [show p.k - h = p.k - (h + 1) + 1 by omega, pow_succ 2 (p.k - (h + 1))]; omega)
  simp only [GoodAt, Nat.add_sub_cancel, block_succ, hdiv, Nat.add_sub_cancel]
  rw [List.take_left' hlen, List.drop_left' hlen]

/-- `MergesFrom` peels off its lowest height. -/
theorem mergesFrom_iff (c h : ℕ) :
    MergesFrom p S L c h ↔
      ((c + 1) % 2 ^ (h + 1) = 0 →
        GoodAt Blake2b.hashFn p.toParams S (h + 1) (block (h + 1) (c / 2 ^ (h + 1)) L)) ∧
      MergesFrom p S L c (h + 1) :=
  ⟨fun hM => ⟨hM h le_rfl, fun h' hh' => hM h' (by omega)⟩, fun ⟨h0, hM⟩ h' hh' => by
    rcases Nat.eq_or_lt_of_le hh' with rfl | hlt
    · exact h0
    · exact hM h' hlt⟩

/-- With bit `h` clear, leaf `c` completes no merge from height `h` up. -/
theorem mergesFrom_of_clear {c h : ℕ} (h0 : (c + 1) % 2 ^ h = 0) (hbit : c / 2 ^ h % 2 = 0) :
    MergesFrom p S L c h := by
  intro h' hh' hmod
  exfalso
  have hmod' : (c + 1) % 2 ^ (h + 1) = 0 := by
    obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero hmod
    rw [hm, show h' + 1 = (h + 1) + (h' - h) by omega, Nat.pow_add, Nat.mul_assoc,
      Nat.mul_mod_right]
  rw [mod_succ_pow_succ h0] at hmod'
  omega

/-- **The `while` loop.** From height `h`, a loop whose passes merge as `validate_tree`'s do
    climbs to the first clear bit `t` of `c`, when every merge on the way is good, and fails
    otherwise. -/
theorem while_spec (hL : L.length = 2 ^ p.k) {c : ℕ} (hc : c < 2 ^ p.k)
    (f : Unit → List ℕ × ℕ → Option (ForInStep (List ℕ × ℕ)))
    (hf : ∀ row h, RowRel p S L c row h →
      (c / 2 ^ h % 2 = 0 → f () (row, h) = some (.done (row, h))) ∧
      (c / 2 ^ h % 2 = 1 →
        (Mergeable Blake2b.hashFn p.toParams S h (block h (c / 2 ^ h - 1) L)
            (block h (c / 2 ^ h) L) →
          ∃ row', f () (row, h) = some (.yield (row', h + 1)) ∧ RowRel p S L c row' (h + 1)) ∧
        (¬ Mergeable Blake2b.hashFn p.toParams S h (block h (c / 2 ^ h - 1) L)
            (block h (c / 2 ^ h) L) →
          f () (row, h) = none))) :
    ∀ row h, RowRel p S L c row h →
      (MergesFrom p S L c h → ∃ row' t, forIn Lean.Loop.mk (row, h) f = some (row', t) ∧
        RowRel p S L c row' t ∧ c / 2 ^ t % 2 = 0) ∧
      (¬ MergesFrom p S L c h → forIn Lean.Loop.mk (row, h) f = none) := by
  intro row h hR
  -- Induction on the heights left above `h`.
  obtain ⟨n, hn⟩ : ∃ n, n = p.k - h := ⟨_, rfl⟩
  induction n generalizing row h with
  | zero =>
    -- At the top, bit `k` of `c < 2^k` is clear.
    have hk : h = p.k := by have := hR.2.1; omega
    have hbit : c / 2 ^ h % 2 = 0 := by
      rw [hk, Nat.div_eq_of_lt hc]
    have hdone := (hf row h hR).1 hbit
    refine ⟨fun _ => ⟨row, h, by rw [loop_unfold, hdone]; rfl, hR, hbit⟩,
      fun hM => absurd (mergesFrom_of_clear hR.2.2.1 hbit) hM⟩
  | succ n ih =>
    rcases Nat.mod_two_eq_zero_or_one (c / 2 ^ h) with hbit | hbit
    · have hdone := (hf row h hR).1 hbit
      exact ⟨fun _ => ⟨row, h, by rw [loop_unfold, hdone]; rfl, hR, hbit⟩,
        fun hM => absurd (mergesFrom_of_clear hR.2.2.1 hbit) hM⟩
    · have hmod := (mod_succ_pow_succ hR.2.2.1).mpr hbit
      have hiff := goodAt_iff_mergeable (S := S) hL hc hmod
      obtain ⟨hyes, hno⟩ := (hf row h hR).2 hbit
      rw [mergesFrom_iff, hiff]
      by_cases hm : Mergeable Blake2b.hashFn p.toParams S h (block h (c / 2 ^ h - 1) L)
          (block h (c / 2 ^ h) L)
      · obtain ⟨row', hstep, hR'⟩ := hyes hm
        have ⟨hok, hbad⟩ := ih row' (h + 1) hR' (by omega)
        rw [loop_unfold, hstep]
        simp only [Option.bind_eq_bind, Option.bind_some]
        exact ⟨fun ⟨_, hM⟩ => hok hM, fun hM => hbad fun hM' => hM ⟨fun _ => hm, hM'⟩⟩
      · rw [loop_unfold, hno hm]
        exact ⟨fun ⟨h1, _⟩ => absurd (h1 hmod) hm, fun _ => rfl⟩

end Walk

/-! ## `validate_tree`'s loop bodies -/

/-- One pass of `validate_tree`'s `while` loop (`src/verify.rs`, lines 343–367): merge the
    left sibling of height `height` into `row`, or stop. -/
def whilePass (indices pending : List ℕ) (allDistinct : Bool) (rowLen collisionBytes leaf : ℕ)
    (_ : Unit) (s : List ℕ × ℕ) : Option (ForInStep (List ℕ × ℕ)) := do
  let mut row := s.1
  let mut height := s.2
  if (leaf >>> height) &&& 1 = 1 then
    let len := rowLen - height * collisionBytes
    let left ← slice? pending (height * rowLen) (height * rowLen + len)
    let rightStart := leaf + 1 - (1 <<< height)
    let leftStart := rightStart - (1 <<< height)
    let leftIndices ← slice? indices leftStart rightStart
    let rightIndices ← slice? indices rightStart (leaf + 1)
    if (← slice? left 0 collisionBytes) ≠ (← slice? row 0 collisionBytes) then
      none
    if (← rightIndices[0]?) < (← leftIndices[0]?) then
      none
    if !allDistinct && leftIndices.any (fun i => rightIndices.contains i) then
      none
    for (l, i) in (← slice? left collisionBytes left.length).zipIdx do
      row := row.set i (l ^^^ (← row[collisionBytes + i]?))
    height := height + 1
    return .yield (row, height)
  else
    return .done (row, height)

/-- One leaf of `validate_tree` (lines 332–369): expand its hash into `row`, climb, and store
    the result in `pending`. -/
def leafPass (p : Params) (indices : List ℕ) (allDistinct : Bool) (batch : ℕ)
    (x : (ℕ × List ℕ) × ℕ) (s : List ℕ × List ℕ) : Option (ForInStep (List ℕ × List ℕ)) :=
  have pending := s.1
  have row := s.2
  match x with
  | ((index, digest), offset) => do
    let leaf := batch * HASH_BATCH + offset
    let start := index % p.indicesPerHashOutput * (p.n / 8)
    let row ← expandArrayInto? (← slice? digest start (start + p.n / 8)) p.collisionBitLength 0
      row
    let s ← forIn Lean.Loop.mk (row, 0)
      (whilePass indices pending allDistinct p.hashLength p.collisionByteLength leaf)
    let row := s.1
    let height := s.2
    let len := p.hashLength - height * p.collisionByteLength
    let pending ← copyFromSlice? pending (height * p.hashLength) (← slice? row 0 len)
    return .yield (pending, row)

/-- One batch of `validate_tree` (lines 324–371): hash its leaves' blocks, then walk them. -/
def batchPass (p : Params) (indices : List ℕ) (allDistinct : Bool)
    (hash : List ℕ → List (List ℕ) → Option (List (List ℕ))) (x : List ℕ × ℕ)
    (s : List ℕ × List ℕ × List ℕ × List (List ℕ)) :
    Option (ForInStep (List ℕ × List ℕ × List ℕ × List (List ℕ))) :=
  have pending := s.1
  have row := s.2.1
  have blocks := s.2.2.1
  have digests := s.2.2.2
  match x with
  | (chunk, batch) => do
    let bs ← forIn chunk.zipIdx (blocks.take chunk.length) fun x bs =>
      match x with
      | (index, j) => pure (.yield (bs.set j (index / p.indicesPerHashOutput)))
    let blocks := bs ++ blocks.drop chunk.length
    let ds ← hash bs (digests.take chunk.length)
    let digests := ds ++ digests.drop chunk.length
    let s ← forIn (chunk.zip ds).zipIdx (pending, row) (leafPass p indices allDistinct batch)
    return .yield (s.1, s.2, blocks, digests)

/-- `validate_tree`, as its loop bodies. -/
theorem validateTree?_eq (p : Params) (indices : List ℕ)
    (hash : List ℕ → List (List ℕ) → Option (List (List ℕ))) :
    validateTree? p indices hash =
      (if p.solutionIndices? ≠ some indices.length then none else do
        let sorted := indices.mergeSort
        let allDistinct := (sorted.zip sorted.tail).all fun (a, b) => a != b
        let s ← forIn (← chunks? indices HASH_BATCH).zipIdx
          (List.replicate ((p.k + 1) * p.hashLength) 0, List.replicate p.hashLength 0,
            List.replicate HASH_BATCH 0, List.replicate HASH_BATCH (List.replicate 64 0))
          (batchPass p indices allDistinct hash)
        let root ← slice? s.1 (p.k * p.hashLength) (p.k * p.hashLength + p.collisionByteLength)
        if root.all (· == 0) then pure () else none) := by
  rfl

/-! ## A pass of the `while` loop -/

theorem Params.hashLength_eq {rp : Params} {p : ZakuraParams} (h : rp.Is p) :
    rp.hashLength = (p.k + 1) * ((p.digitBits + 7) / 8) := by
  simp [Params.hashLength, Params.collisionByteLength_eq h, h.2]

/-- The in-place XOR loop of a pass. -/
theorem forIn_xor (cb : ℕ) (hcb : 1 ≤ cb) (seg row : List ℕ)
    (hlen : seg.length + cb ≤ row.length) :
    forIn seg.zipIdx row (fun x (row : List ℕ) =>
      row[cb + x.2]?.bind fun v => pure (ForInStep.yield (row.set x.2 (x.1 ^^^ v)))) =
      some (List.zipWith (· ^^^ ·) seg (row.drop cb) ++ row.drop seg.length) := by
  rw [forIn_option_eq_foldlM _ _ _ (fun x row => do
    let v ← row[cb + x.2]?
    pure (row.set x.2 (x.1 ^^^ v))) (fun x row => by
      rcases row[cb + x.2]? with _ | v <;> simp)]
  rw [foldlM_xor cb hcb seg 0 row (by omega)]
  simp

/-- A nonempty list's first element. -/
theorem getElem?_zero_eq_headD {l : List ℕ} (h : l ≠ []) : l[0]? = some (l.headD 0) := by
  obtain ⟨x, l, rfl⟩ := List.exists_cons_of_ne_nil h
  rfl

/-- `zipWith` reads its second list only as far as its first. -/
theorem zipWith_take_length {f : ℕ → ℕ → ℕ} (a b : List ℕ) :
    List.zipWith f a (b.take a.length) = List.zipWith f a b := by
  apply List.ext_getElem
  · simp only [List.length_zipWith, List.length_take]; omega
  · intro i _ _
    simp

section Pass

variable {p : ZakuraParams} {S : List Byte} {L : List ℕ}

theorem whilePass_spec (hL : L.length = 2 ^ p.k) {c : ℕ} (hc : c < 2 ^ p.k)
    {pending : List ℕ} (hP : PendingRel p S L c pending) {allDistinct : Bool}
    (hAD : allDistinct = true → L.Nodup) :
    ∀ row h, RowRel p S L c row h →
      (c / 2 ^ h % 2 = 0 →
        whilePass L pending allDistinct ((p.k + 1) * ((p.digitBits + 7) / 8))
          ((p.digitBits + 7) / 8) c () (row, h) = some (.done (row, h))) ∧
      (c / 2 ^ h % 2 = 1 →
        (Mergeable Blake2b.hashFn p.toParams S h (block h (c / 2 ^ h - 1) L)
            (block h (c / 2 ^ h) L) →
          ∃ row', whilePass L pending allDistinct ((p.k + 1) * ((p.digitBits + 7) / 8))
            ((p.digitBits + 7) / 8) c () (row, h) = some (.yield (row', h + 1)) ∧
            RowRel p S L c row' (h + 1)) ∧
        (¬ Mergeable Blake2b.hashFn p.toParams S h (block h (c / 2 ^ h - 1) L)
            (block h (c / 2 ^ h) L) →
          whilePass L pending allDistinct ((p.k + 1) * ((p.digitBits + 7) / 8))
            ((p.digitBits + 7) / 8) c () (row, h) = none)) := by
  intro row h hR
  obtain ⟨hrl, hk, h0, hE⟩ := hR
  set w := (p.digitBits + 7) / 8 with hw
  have hc8 : 8 ≤ p.digitBits := p.digit_ge
  have hw1 : 1 ≤ w := by omega
  constructor
  · intro hbit
    have hne : ¬ (c >>> h) &&& 1 = 1 := by rw [shiftRight_and_one, hbit]; decide
    simp only [whilePass, hne, ↓reduceIte]
    rfl
  · intro hbit
    have hcond : (c >>> h) &&& 1 = 1 := by rw [shiftRight_and_one, hbit]
    -- The leaf count: `c + 1 = (q + 1)·2^h` with `q` odd, and the merge stays below the top.
    have hP2 := Nat.two_pow_pos h
    have hc1 := succ_eq_of_mod hP2 h0
    have hmod := (mod_succ_pow_succ h0).mpr hbit
    set q := c / 2 ^ h with hq
    have hq1 : 1 ≤ q := Nat.pos_of_ne_zero fun h' => by rw [h'] at hbit; simp at hbit
    have hhk : h + 1 ≤ p.k := by
      by_contra hlt
      have h1 : 2 ^ p.k < 2 ^ (h + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ (h + 1) ≤ c + 1 := by
        rw [succ_eq_of_mod (Nat.two_pow_pos (h + 1)) hmod]
        exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      omega
    have hqk : q < 2 ^ (p.k - h) := by
      rw [hq, Nat.div_lt_iff_lt_mul hP2, ← Nat.pow_add, Nat.sub_add_cancel hk]; exact hc
    -- The two blocks: positions `(q-1)·2^h .. q·2^h` and `q·2^h .. c + 1`.
    have hX : 2 ^ h ≤ q * 2 ^ h := Nat.le_mul_of_pos_left _ (by omega)
    have hqm : (q - 1) * 2 ^ h = q * 2 ^ h - 2 ^ h := by rw [Nat.sub_mul, one_mul]
    have hc1' : c + 1 = q * 2 ^ h + 2 ^ h := by rw [hc1, Nat.add_mul, one_mul]
    have hrs : c + 1 - 1 <<< h = q * 2 ^ h := by rw [Nat.one_shiftLeft]; omega
    have hls : q * 2 ^ h - 1 <<< h = (q - 1) * 2 ^ h := by rw [Nat.one_shiftLeft, hqm]
    have hlenL : (block h (q - 1) L).length = 2 ^ h := length_block hL hk (by omega)
    have hlenR : (block h q L).length = 2 ^ h := length_block hL hk hqk
    have hLI : slice? L ((q - 1) * 2 ^ h) (q * 2 ^ h) = some (block h (q - 1) L) := by
      rw [slice?_eq _ _ _ (by omega) (by rw [hL]; omega)]
      simp only [block]
      congr 2; omega
    have hRI : slice? L (q * 2 ^ h) (c + 1) = some (block h q L) := by
      rw [slice?_eq _ _ _ (by omega) (by rw [hL]; omega)]
      simp only [block]
      congr 2; omega
    have hhL := getElem?_zero_eq_headD (List.ne_nil_of_length_pos (l := block h (q - 1) L)
      (by rw [hlenL]; exact hP2))
    have hhR := getElem?_zero_eq_headD (List.ne_nil_of_length_pos (l := block h q L)
      (by rw [hlenR]; exact hP2))
    -- Slot `h` of `pending` holds the left block.
    have hEL := hP.2 h hk hbit
    have hd : 0 < p.digitBits := by omega
    have hslot : (slot p pending h).length = (p.k + 1 - h) * w := by
      rw [hEL.1, length_rest, Nat.mul_div_cancel _ hd]
    have hpl : pending.length = (p.k + 1) * ((p.k + 1) * w) := hP.1
    have hwk : w ≤ (p.k + 1 - h) * w := Nat.le_mul_of_pos_left _ (by omega)
    have hwk' : (p.k + 1 - h) * w ≤ (p.k + 1) * w := Nat.mul_le_mul_right _ (by omega)
    have hhR' : (h + 1) * ((p.k + 1) * w) ≤ (p.k + 1) * ((p.k + 1) * w) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.succ_mul] at hhR'
    have hleft :
        slice? pending (h * ((p.k + 1) * w)) (h * ((p.k + 1) * w) + ((p.k + 1) * w - h * w)) =
        some (slot p pending h) := by
      rw [← Nat.sub_mul, slice?_eq _ _ _ (by omega) (by omega), Nat.add_sub_cancel_left]
      rfl
    have hc0 : slice? (slot p pending h) 0 w = some ((slot p pending h).take w) := by
      rw [slice?_eq _ _ _ (Nat.zero_le _) (by omega)]; simp
    have hr0 : slice? row 0 w = some (row.take w) := by
      rw [slice?_eq _ _ _ (Nat.zero_le _) (by rw [hrl]; omega)]; simp
    have hseg : slice? (slot p pending h) w (slot p pending h).length =
        some ((slot p pending h).drop w) := by
      rw [slice?_eq _ _ _ (by omega) le_rfl, List.take_of_length_le (by simp)]
    have hxor := forIn_xor w hw1 ((slot p pending h).drop w) row (by
      rw [List.length_drop, hslot, hrl]; omega)
    simp only [whilePass, hcond, ↓reduceIte, Option.bind_eq_bind, hrs, hls, hleft, hLI, hRI,
      hc0, hr0, hhL, hhR, hseg, hxor, Option.bind_some, Option.bind_none]
    -- The merged block: the two halves of block `q / 2` of height `h + 1`.
    have hdiv : c / 2 ^ (h + 1) = q / 2 := by rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    have hmerge : block h (q - 1) L ++ block h q L = block (h + 1) (c / 2 ^ (h + 1)) L := by
      rw [block_succ, hdiv, show 2 * (q / 2) + 1 = q by omega, show 2 * (q / 2) = q - 1 by omega]
    -- The three checks are `Mergeable`'s.
    have hlr : ∀ l, (rest p S h l).length = (p.k + 1 - h) * p.digitBits :=
      fun l => length_rest p S h l
    have h1d : 1 ≤ (p.k + 1 - h) * p.digitBits / p.digitBits := by
      rw [Nat.mul_div_cancel _ hd]; omega
    have hdle : p.digitBits ≤ (p.k + 1 - h) * p.digitBits := Nat.le_mul_of_pos_left _ (by omega)
    have hcol : (slot p pending h).take w = row.take w ↔
        (rest p S h (block h (q - 1) L)).take p.digitBits =
          (rest p S h (block h q L)).take p.digitBits := by
      have := ExpandedN.take_eq_iff (by omega : p.digitBits ≤ 8 * w) hEL hE
        (by rw [hlr]; exact h1d) (by rw [hlr]; exact h1d) (by rw [hlr]; exact hdle)
        (by rw [hlr]; exact hdle)
      rwa [List.take_take, Nat.min_eq_left hwk] at this
    have hdup : (!allDistinct && (block h (q - 1) L).any fun i => (block h q L).contains i) =
        true ↔ ∃ i ∈ block h (q - 1) L, i ∈ block h q L := by
      cases hAD' : allDistinct
      · simp
      · simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, false_iff]
        rintro ⟨i, hi1, hi2⟩
        have hb := nodup_block (r := h + 1) (w := c / 2 ^ (h + 1)) (hAD hAD')
        rw [← hmerge] at hb
        exact (List.nodup_append.mp hb).2.2 i hi1 i hi2 rfl
    have hM : Mergeable Blake2b.hashFn p.toParams S h (block h (q - 1) L) (block h q L) ↔
        (slot p pending h).take w = row.take w ∧
          ¬ (block h q L).headD 0 < (block h (q - 1) L).headD 0 ∧
          ¬ (!allDistinct && (block h (q - 1) L).any fun i => (block h q L).contains i) =
            true := by
      rw [hcol, hdup]; rfl
    rw [hM]
    refine ⟨fun ⟨h1, h2, h3⟩ => ⟨_, by
      simp only [h1, h2, h3, ne_eq, not_true_eq_false, ↓reduceIte]; rfl, ?_⟩, fun hn => ?_⟩
    · -- The XOR of both blocks, without its first digit, is the merged block's.
      have hX := ExpandedN.xor_drop hEL hE (by rw [hlr, hlr])
      have hrest : (xor (rest p S h (block h (q - 1) L)) (rest p S h (block h q L))).drop
          p.digitBits = rest p S (h + 1) (block (h + 1) (c / 2 ^ (h + 1)) L) := by
        rw [← hmerge]
        simp only [rest, blockXor_append, Nat.succ_mul, drop_xor, List.drop_drop]
      have hseglen : ((slot p pending h).drop w).length = (p.k + 1 - h) * w - w := by
        rw [List.length_drop, hslot]
      have htake : (List.zipWith (· ^^^ ·) ((slot p pending h).drop w) (row.drop w) ++
          row.drop ((slot p pending h).drop w).length).take ((p.k + 1 - (h + 1)) * w) =
          (List.zipWith (· ^^^ ·) (slot p pending h)
            (row.take ((p.k + 1 - h) * w))).drop w := by
        have hzl : (List.zipWith (· ^^^ ·) ((slot p pending h).drop w) (row.drop w)).length =
            (p.k + 1 - (h + 1)) * w := by
          have e1 : (p.k + 1 - (h + 1)) * w = (p.k + 1 - h) * w - w := by
            rw [show p.k + 1 - (h + 1) = p.k + 1 - h - 1 by omega, Nat.sub_mul, one_mul]
          rw [List.length_zipWith, hseglen, List.length_drop, hrl, e1]
          omega
        rw [List.take_left' hzl, List.drop_zipWith, List.drop_take, ← hseglen,
          zipWith_take_length]
      refine ⟨?_, hhk, hmod, ?_⟩
      · simp only [List.length_append, List.length_zipWith, List.length_drop, hslot, hrl, ← hw]
        omega
      · rw [htake, ← hrest]; exact hX
    · by_cases h1 : (slot p pending h).take w = row.take w
      · by_cases h2 : (block h q L).headD 0 < (block h (q - 1) L).headD 0
        · simp only [h1, h2, ne_eq, not_true_eq_false, ↓reduceIte]
        · have h3 : (!allDistinct && (block h (q - 1) L).any fun i => (block h q L).contains i) =
              true := by
            by_contra h3; exact hn ⟨h1, h2, h3⟩
          simp only [h1, h2, h3, ne_eq, not_true_eq_false, ↓reduceIte]
      · simp only [h1, ne_eq, not_false_eq_true, ↓reduceIte]

end Pass

/-! ## A leaf -/

/-- `expand_array_into` writes every byte of its output: what `vout` held does not matter. -/
theorem expandArrayInto?_eq_expandArray? (vin : List ℕ) (c pad : ℕ) (vout : List ℕ)
    (hl : vout.length = expandedLen vin.length c pad) :
    expandArrayInto? vin c pad vout = expandArray? vin c pad := by
  have hmap : vout.map (fun _ => 0) = List.replicate vout.length 0 := by
    simp [List.map_const']
  simp only [expandArray?, expandArrayInto?, hmap, List.length_replicate, hl,
    List.map_replicate]

/-- Reading back a slice written by `copy_from_slice`. -/
theorem copyFromSlice?_eq {α : Type} (dst src : List α) (start : ℕ)
    (h : start + src.length ≤ dst.length) :
    copyFromSlice? dst start src = some (dst.take start ++ src ++ dst.drop (start + src.length)) :=
  by simp [copyFromSlice?, h]

/-- The slot a copy writes holds what was copied. -/
theorem slot_copy_self (p : ZakuraParams) (pending src : List ℕ) (t : ℕ)
    (hsrc : src.length = (p.k + 1 - t) * ((p.digitBits + 7) / 8))
    (hfit : t * ((p.k + 1) * ((p.digitBits + 7) / 8)) ≤ pending.length) :
    slot p (pending.take (t * ((p.k + 1) * ((p.digitBits + 7) / 8))) ++ src ++
      pending.drop (t * ((p.k + 1) * ((p.digitBits + 7) / 8)) + src.length)) t = src := by
  simp only [slot, List.append_assoc]
  rw [List.drop_left' (by simp; omega), ← hsrc, List.take_left' rfl]

/-- A copy into one slot leaves the slots above it as they were. -/
theorem slot_copy_above (p : ZakuraParams) (pending src : List ℕ) (t h : ℕ) (hth : t < h)
    (hsrc : src.length = (p.k + 1 - t) * ((p.digitBits + 7) / 8))
    (hfit : t * ((p.k + 1) * ((p.digitBits + 7) / 8)) + src.length ≤ pending.length) :
    slot p (pending.take (t * ((p.k + 1) * ((p.digitBits + 7) / 8))) ++ src ++
      pending.drop (t * ((p.k + 1) * ((p.digitBits + 7) / 8)) + src.length)) h =
      slot p pending h := by
  have hs : src.length ≤ (p.k + 1) * ((p.digitBits + 7) / 8) := by
    rw [hsrc]; exact Nat.mul_le_mul_right _ (by omega)
  simp only [slot]
  generalize (p.k + 1) * ((p.digitBits + 7) / 8) = R at *
  have hhR : (t + 1) * R ≤ h * R := Nat.mul_le_mul_right _ hth
  rw [Nat.succ_mul] at hhR
  congr 1
  rw [List.append_assoc, List.drop_append, List.drop_eq_nil_of_le (by simp; omega),
    List.nil_append, List.drop_append,
    List.drop_eq_nil_of_le (by simp only [List.length_take]; omega), List.nil_append,
    List.drop_drop]
  congr 1
  simp only [List.length_take]
  omega

/-! ## From `c` to `c + 1`

The climb of leaf `c` stops at the first clear bit `t` of `c`; adding one sets bit `t`, clears
the bits below it, and leaves those above it. -/

section Carry

variable {c t : ℕ} (h0 : (c + 1) % 2 ^ t = 0) (hbit : c / 2 ^ t % 2 = 0)
include h0

theorem succ_div_self : (c + 1) / 2 ^ t = c / 2 ^ t + 1 := by
  rw [succ_eq_of_mod (Nat.two_pow_pos t) h0, Nat.mul_div_cancel _ (Nat.two_pow_pos t)]

include hbit

theorem succ_div_above {h : ℕ} (hth : t < h) : (c + 1) / 2 ^ h = c / 2 ^ h := by
  have hs := succ_div_self h0
  obtain ⟨m, rfl⟩ : ∃ m, h = t + 1 + m := ⟨h - (t + 1), by omega⟩
  rw [Nat.pow_add, Nat.pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
    ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hs]
  congr 1
  omega

theorem succ_bit_below {h : ℕ} (hth : h < t) : (c + 1) / 2 ^ h % 2 = 0 := by
  have hc := succ_eq_of_mod (Nat.two_pow_pos t) h0
  generalize c / 2 ^ t = q at hc
  obtain ⟨m, rfl⟩ : ∃ m, t = h + (m + 1) := ⟨t - (h + 1), by omega⟩
  rw [hc, Nat.pow_add, show (q + 1) * (2 ^ h * 2 ^ (m + 1)) = 2 ^ h * ((q + 1) * 2 ^ m * 2) by
    ring, Nat.mul_div_cancel_left _ (Nat.two_pow_pos h), Nat.mul_mod_left]

end Carry

section Leaf

variable {rp : Params} {p : ZakuraParams} {S : List Byte} {L : List ℕ}

/-- `slice?` reads only the part of a list it needs. -/
theorem slice?_append_left {A B x : List ℕ} {s e : ℕ} (h : slice? A s e = some x) :
    slice? (A ++ B) s e = some x := by
  simp only [slice?] at h ⊢
  split_ifs at h with hse
  have hc : s ≤ e ∧ e ≤ (A ++ B).length := ⟨hse.1, by simp; omega⟩
  simp only [hc, and_self, ↓reduceIte]
  rw [← h, List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp; omega)]

/-- **A leaf's row.** The digest of the leaf's block, sliced and expanded as `validate_tree`
    does, holds the leaf's hash value. -/
theorem leafRow (h : rp.Is p) {st : Blake2b.State} (hst : StateFor p.toParams S st)
    {D : ℕ → List ℕ} (hD : ∀ b, D b = generateHash st b ++ List.replicate (64 - rp.hashOutput) 0)
    {c : ℕ} (hcL : c < L.length) {row : List ℕ}
    (hrow : row.length = (p.k + 1) * ((p.digitBits + 7) / 8)) :
    ∃ bytes row0,
      slice? (D (L[c] / rp.indicesPerHashOutput)) (L[c] % rp.indicesPerHashOutput * (rp.n / 8))
        (L[c] % rp.indicesPerHashOutput * (rp.n / 8) + rp.n / 8) = some bytes ∧
      expandArrayInto? bytes rp.collisionBitLength 0 row = some row0 ∧
      RowRel p S L c row0 0 := by
  have hc8 : 8 ≤ p.digitBits := p.digit_ge
  obtain ⟨q, hq⟩ := p.n_dvd_8
  have hn8 : rp.n / 8 = q := by rw [h.1, hq]; omega
  obtain ⟨node, hnode, -, hE⟩ := Node.new?_spec h hst L[c]
  simp only [Node.new?, Option.bind_eq_bind, Option.pure_def] at hnode
  have hstart : L[c] % rp.indicesPerHashOutput * rp.n / 8 =
      L[c] % rp.indicesPerHashOutput * (rp.n / 8) := by
    rw [h.1, hq, Nat.mul_div_assoc _ (by omega : 8 ∣ 8 * q)]
  rw [hstart] at hnode
  rcases hs : slice? (generateHash st (L[c] / rp.indicesPerHashOutput))
      (L[c] % rp.indicesPerHashOutput * (rp.n / 8))
      (L[c] % rp.indicesPerHashOutput * (rp.n / 8) + rp.n / 8) with _ | bytes
  · simp [hs] at hnode
  rcases hx : expandArray? bytes rp.collisionBitLength 0 with _ | out
  · simp [hs, hx] at hnode
  have hout : node.hash = out := by
    simp only [hs, hx, Option.bind_some, Option.some.injEq] at hnode; rw [← hnode]
  rw [hout] at hE
  -- The expansion's length.
  have hbl : bytes.length = q := by
    simp only [slice?] at hs
    split_ifs at hs with hse
    simp only [Option.some.injEq] at hs
    rw [← hs, List.length_take, List.length_drop]; omega
  have hlenX : (X Blake2b.hashFn p.toParams S (L[c] + 1)).length / p.digitBits = p.k + 1 := by
    rw [length_X, n_eq p.toParams, Nat.mul_div_cancel _ (by omega)]
  have hol : out.length = (p.k + 1) * ((p.digitBits + 7) / 8) := by rw [hE.1, hlenX]
  have hexp : expandedLen bytes.length rp.collisionBitLength 0 =
      (p.k + 1) * ((p.digitBits + 7) / 8) := by
    have hn : 8 * q = (p.k + 1) * p.digitBits := by rw [← hq]; exact n_eq p.toParams
    rw [expandedLen, Params.collisionBitLength_eq h, divCeil_eq _ _ (by norm_num), hbl,
      Nat.add_zero, show p.digitBits + 8 - 1 = p.digitBits + 7 by omega,
      show 8 * ((p.digitBits + 7) / 8) * q = (p.k + 1) * ((p.digitBits + 7) / 8) * p.digitBits by
        calc 8 * ((p.digitBits + 7) / 8) * q = (p.digitBits + 7) / 8 * (8 * q) := by ring
          _ = _ := by rw [hn]; ring]
    exact Nat.mul_div_cancel _ (by omega)
  refine ⟨bytes, out, ?_, ?_, ?_⟩
  · rw [hD]; exact slice?_append_left hs
  · rw [expandArrayInto?_eq_expandArray? _ _ _ _ (by rw [hrow, hexp]), hx]
  · refine ⟨hol, Nat.zero_le _, by rw [pow_zero, Nat.mod_one], ?_⟩
    have hb : block 0 (c / 2 ^ 0) L = [L[c]] := by
      simp [block, List.take_one, List.head?_drop, hcL]
    rw [hb, List.take_of_length_le (by rw [hol]; simp), rest, Nat.zero_mul, List.drop_zero,
      blockXor_singleton]
    exact hE


/-- **A leaf.** `validate_tree` walks leaf `c`: when the merges it completes are good, it
    leaves `pending` as after `c + 1` leaves; otherwise it fails. -/
theorem leafPass_spec (h : rp.Is p) {st : Blake2b.State} (hst : StateFor p.toParams S st)
    {D : ℕ → List ℕ} (hD : ∀ b, D b = generateHash st b ++ List.replicate (64 - rp.hashOutput) 0)
    (hL : L.length = 2 ^ p.k) {allDistinct : Bool} (hAD : allDistinct = true → L.Nodup)
    {c : ℕ} (hc : c < 2 ^ p.k) {batch offset : ℕ} (hleaf : batch * HASH_BATCH + offset = c)
    {pending row : List ℕ} (hP : PendingRel p S L c pending)
    (hrow : row.length = (p.k + 1) * ((p.digitBits + 7) / 8)) :
    (LeafGood Blake2b.hashFn p.toParams S L c → ∃ pending' row',
      leafPass rp L allDistinct batch
          ((L[c]'(by omega), D (L[c]'(by omega) / rp.indicesPerHashOutput)), offset)
          (pending, row) = some (.yield (pending', row')) ∧
        PendingRel p S L (c + 1) pending' ∧
        row'.length = (p.k + 1) * ((p.digitBits + 7) / 8)) ∧
    (¬ LeafGood Blake2b.hashFn p.toParams S L c →
      leafPass rp L allDistinct batch
        ((L[c]'(by omega), D (L[c]'(by omega) / rp.indicesPerHashOutput)), offset)
        (pending, row) = none) := by
  have hcL : c < L.length := by omega
  obtain ⟨bytes, row0, hs, hx, hR0⟩ := leafRow (L := L) h hst hD hcL hrow
  have hW := while_spec hL hc _ (whilePass_spec hL hc hP hAD) row0 0 hR0
  have hG : LeafGood Blake2b.hashFn p.toParams S L c ↔ MergesFrom p S L c 0 :=
    ⟨fun hG h' _ => hG h', fun hM h' => hM h' (Nat.zero_le _)⟩
  simp only [leafPass, hleaf, hs, hx, Option.bind_eq_bind, Option.bind_some,
    Params.hashLength_eq h, Params.collisionByteLength_eq h]
  rw [hG]
  refine ⟨fun hM => ?_, fun hM => by rw [hW.2 hM]; rfl⟩
  -- The climb stops at the first clear bit `t` of `c`; its row goes to slot `t`.
  obtain ⟨row', t, hloop, ⟨hrl', htk, h0t, hEt⟩, hbit⟩ := hW.1 hM
  have hpl : pending.length = (p.k + 1) * ((p.k + 1) * ((p.digitBits + 7) / 8)) := hP.1
  generalize hw : (p.digitBits + 7) / 8 = w at *
  have hlen : (p.k + 1) * w - t * w = (p.k + 1 - t) * w := by rw [Nat.sub_mul]
  have htw : (p.k + 1 - t) * w ≤ (p.k + 1) * w := Nat.mul_le_mul_right _ (by omega)
  have hsl : slice? row' 0 ((p.k + 1) * w - t * w) = some (row'.take ((p.k + 1 - t) * w)) := by
    rw [hlen, slice?_eq _ _ _ (Nat.zero_le _) (by rw [hrl']; exact htw)]; simp
  have htl : (row'.take ((p.k + 1 - t) * w)).length = (p.k + 1 - t) * w := by
    rw [List.length_take, hrl']; omega
  have htR : (t + 1) * ((p.k + 1) * w) ≤ (p.k + 1) * ((p.k + 1) * w) :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.succ_mul] at htR
  have hfit : t * ((p.k + 1) * w) + (row'.take ((p.k + 1 - t) * w)).length ≤ pending.length := by
    rw [htl, hpl]; omega
  rw [hloop]
  simp only [Option.bind_some, hsl, copyFromSlice?_eq _ _ _ hfit]
  refine ⟨_, _, rfl, ⟨?_, fun h' hh' hb' => ?_⟩, hrl'⟩
  · simp only [List.length_append, List.length_take, List.length_drop, htl, hw]; omega
  · subst hw
    rcases lt_trichotomy h' t with hlt | rfl | hgt
    · rw [succ_bit_below h0t hbit hlt] at hb'; exact absurd hb' (by decide)
    · rw [slot_copy_self p pending _ h' htl (by omega), succ_div_self h0t, Nat.add_sub_cancel]
      exact hEt
    · rw [slot_copy_above p pending _ t h' hgt htl hfit, succ_div_above h0t hbit hgt]
      rw [succ_div_above h0t hbit hgt] at hb'
      exact hP.2 h' hh' hb'

end Leaf

/-! ## Batches -/

/-- A loop whose passes each continue keeping an invariant `I`, or fail, succeeds when every
    pass `OK`s, and fails at the first that does not. -/
theorem forIn_option_spec {α β : Type} (l : List α) (f : α → β → Option (ForInStep β))
    (I : ℕ → β → Prop) (OK : ℕ → Prop) (k : ℕ) (init : β) (h0 : I k init)
    (hstep : ∀ i (hi : i < l.length) b, I (k + i) b →
      (OK (k + i) → ∃ b', f l[i] b = some (.yield b') ∧ I (k + i + 1) b') ∧
        (¬ OK (k + i) → f l[i] b = none)) :
    ((∀ i < l.length, OK (k + i)) → ∃ b, forIn l init f = some b ∧ I (k + l.length) b) ∧
      ((∃ i < l.length, ¬ OK (k + i)) → forIn l init f = none) := by
  induction l generalizing k init with
  | nil => exact ⟨fun _ => ⟨init, rfl, by simpa using h0⟩, fun ⟨i, hi, _⟩ => absurd hi (by simp)⟩
  | cons a l ih =>
    have ⟨hok, hbad⟩ := hstep 0 (by simp) init (by simpa using h0)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hok hbad
    have ih' := fun b (hb : I (k + 1) b) => ih (k + 1) b hb fun i hi b' hb' => by
      have := hstep (i + 1) (by simp; omega) b' (by rwa [← Nat.add_assoc, Nat.add_right_comm])
      simpa only [List.getElem_cons_succ, ← Nat.add_assoc, Nat.add_right_comm k 1 i] using this
    constructor
    · intro hall
      obtain ⟨b, hb, hI⟩ := hok (by simpa using hall 0 (by simp))
      obtain ⟨c, hc, hIc⟩ := (ih' b hI).1 fun i hi => by
        simpa [Nat.add_right_comm k 1 i, ← Nat.add_assoc] using hall (i + 1) (by simp; omega)
      exact ⟨c, by simp [List.forIn_cons, hb, hc],
        by simpa [Nat.add_right_comm, ← Nat.add_assoc] using hIc⟩
    · rintro ⟨i, hi, hn⟩
      by_cases h0' : OK k
      · obtain ⟨b, hb, hI⟩ := hok h0'
        rcases i with _ | i
        · exact absurd h0' (by simpa using hn)
        · simp only [List.forIn_cons, hb, Option.bind_eq_bind, Option.bind_some]
          exact (ih' b hI).2 ⟨i, by simp at hi; omega, by
            simpa [Nat.add_right_comm k 1 i, ← Nat.add_assoc] using hn⟩
      · simp [List.forIn_cons, hbad h0']

/-- `chunks` cuts a list into runs of `n + 1`, the last possibly shorter. -/
theorem chunksSucc_spec {α : Type} (n : ℕ) (l : List α) :
    (chunksSucc n l).length = (l.length + n) / (n + 1) ∧
      ∀ b (hb : b < (chunksSucc n l).length),
        (chunksSucc n l)[b] = (l.drop (b * (n + 1))).take (n + 1) := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ m ih =>
    match l with
    | [] =>
      simp only [List.length_nil] at h
      subst h
      refine ⟨?_, fun b hb => by simp [chunksSucc] at hb⟩
      simp only [chunksSucc, List.length_nil, Nat.zero_add]
      exact (Nat.div_eq_of_lt (by omega)).symm
    | x :: xs =>
      have hrec := ih ((x :: xs).drop (n + 1)).length (by simp at h ⊢; omega) _ rfl
      rw [chunksSucc]
      refine ⟨?_, fun b hb => ?_⟩
      · have hm1 : 1 ≤ (x :: xs).length := by simp
        rw [List.length_cons, hrec.1, List.length_drop, ← h]
        generalize (x :: xs).length = m' at hm1 ⊢
        rcases Nat.lt_or_ge m' (n + 1) with hm | hm
        · rw [Nat.sub_eq_zero_of_le hm.le, Nat.zero_add, Nat.div_eq_of_lt (by omega),
            Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
        · rw [show m' + n = (m' - (n + 1) + n) + 1 * (n + 1) by omega,
            Nat.add_mul_div_right _ _ (by omega)]
      · rcases b with _ | b
        · simp
        · simp only [List.getElem_cons_succ]
          rw [hrec.2 b (by simpa using hb), List.drop_drop]
          congr 2; ring

/-- `sorted.windows(2).all(|w| w[0] != w[1])` on the sorted indices: when it holds, no index
    repeats. -/
theorem nodup_of_allDistinct {l : List ℕ}
    (h : ((l.mergeSort).zip (l.mergeSort).tail).all (fun (a, b) => a != b) = true) :
    l.Nodup := by
  have hs : (l.mergeSort).Pairwise (· ≤ ·) := by
    simpa using List.pairwise_mergeSort (le := fun a b => decide (a ≤ b))
      (fun a b c hab hbc => by simp_all; omega) (fun a b => by simp; omega) l
  refine (List.mergeSort_perm l fun a b => decide (a ≤ b)).nodup_iff.mp ?_
  generalize l.mergeSort = s at hs h
  induction s with
  | nil => simp
  | cons a s ih =>
    rw [List.pairwise_cons] at hs
    cases s with
    | nil => simp
    | cons b s =>
      simp only [List.tail_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true,
        bne_iff_ne, ne_eq] at h
      refine List.nodup_cons.mpr ⟨fun ha => ?_, ih hs.2 (by simpa using h.2)⟩
      have hab : a < b := lt_of_le_of_ne (hs.1 b (by simp)) h.1
      rcases List.mem_cons.mp ha with rfl | ha
      · omega
      · have := (List.pairwise_cons.mp hs.2).1 a ha; omega

section Batch

variable {rp : Params} {p : ZakuraParams} {S : List Byte} {L : List ℕ}

/-- Each leaf digest is 64 bytes: the BLAKE2b output, then zeros. -/
theorem length_digest (h : rp.Is p) {st : Blake2b.State} (hst : StateFor p.toParams S st)
    {D : ℕ → List ℕ} (hD : ∀ b, D b = generateHash st b ++ List.replicate (64 - rp.hashOutput) 0)
    (b : ℕ) : (D b).length = 64 := by
  have hle := genHashParams_len_le p.toParams
  rw [hD, List.length_append, List.length_replicate, generateHash_eq hst, List.length_map,
    List.Vector.toList_length, Params.hashOutput_eq h]
  simp only [genHashParams] at hle ⊢
  omega

theorem batchPass_spec (h : rp.Is p) {st : Blake2b.State} (hst : StateFor p.toParams S st)
    {D : ℕ → List ℕ} (hD : ∀ b, D b = generateHash st b ++ List.replicate (64 - rp.hashOutput) 0)
    {hash : List ℕ → List (List ℕ) → Option (List (List ℕ))}
    (hhash : ∀ bs ds, ds.length = bs.length → (∀ d ∈ ds, d.length = 64) →
      hash bs ds = some (bs.map D))
    (hL : L.length = 2 ^ p.k) {allDistinct : Bool} (hAD : allDistinct = true → L.Nodup)
    {b : ℕ} (hb : b * 64 < L.length) {pending row blocks : List ℕ} {digests : List (List ℕ)}
    (hP : PendingRel p S L (b * 64) pending)
    (hrow : row.length = (p.k + 1) * ((p.digitBits + 7) / 8))
    (hbl : blocks.length = 64) (hdl : digests.length = 64)
    (hd64 : ∀ d ∈ digests, d.length = 64) :
    ((∀ i < ((L.drop (b * 64)).take 64).length,
        LeafGood Blake2b.hashFn p.toParams S L (b * 64 + i)) →
      ∃ s, batchPass rp L allDistinct hash ((L.drop (b * 64)).take 64, b)
          (pending, row, blocks, digests) = some (.yield s) ∧
        PendingRel p S L (b * 64 + ((L.drop (b * 64)).take 64).length) s.1 ∧
        s.2.1.length = (p.k + 1) * ((p.digitBits + 7) / 8) ∧ s.2.2.1.length = 64 ∧
        s.2.2.2.length = 64 ∧ ∀ d ∈ s.2.2.2, d.length = 64) ∧
    ((∃ i < ((L.drop (b * 64)).take 64).length,
        ¬ LeafGood Blake2b.hashFn p.toParams S L (b * 64 + i)) →
      batchPass rp L allDistinct hash ((L.drop (b * 64)).take 64, b)
        (pending, row, blocks, digests) = none) := by
  simp only [batchPass, Option.bind_eq_bind]
  generalize hchunk : (L.drop (b * 64)).take 64 = chunk
  have hcl : chunk.length = min 64 (L.length - b * 64) := by
    rw [← hchunk, List.length_take, List.length_drop]
  -- `blocks[j] = index / per_hash`, then `hash(blocks, digests)`.
  have hbs : forIn chunk.zipIdx (blocks.take chunk.length) (fun x (bs : List ℕ) =>
      pure (ForInStep.yield (bs.set x.2 (x.1 / rp.indicesPerHashOutput)))) =
      some (chunk.map (· / rp.indicesPerHashOutput)) := by
    rw [List.forIn_pure_yield_eq_foldl, foldl_set_zipIdx (· / rp.indicesPerHashOutput) chunk 0 _
      (by rw [List.length_take]; omega)]
    simp
  have hds : hash (chunk.map (· / rp.indicesPerHashOutput)) (digests.take chunk.length) =
      some (chunk.map fun i => D (i / rp.indicesPerHashOutput)) := by
    rw [hhash _ _ (by simp only [List.length_take, List.length_map]; omega)
      (fun d hd => hd64 d (List.mem_of_mem_take hd)), List.map_map]
    rfl
  simp only [hbs, Option.bind_some, hds]
  -- The leaves of the batch: leaf `b·64 + i` is `chunk[i]`.
  have hlen : ((chunk.zip (chunk.map fun i => D (i / rp.indicesPerHashOutput))).zipIdx).length =
      chunk.length := by simp
  have hcL : ∀ i < chunk.length, b * 64 + i < L.length := fun i hi => by omega
  have helt : ∀ i (hi : i < chunk.length),
      ((chunk.zip (chunk.map fun i => D (i / rp.indicesPerHashOutput))).zipIdx)[i]'(by omega) =
        ((L[b * 64 + i]'(hcL i hi),
          D (L[b * 64 + i]'(hcL i hi) / rp.indicesPerHashOutput)), i) := by
    intro i hi
    have hci : chunk[i] = L[b * 64 + i]'(hcL i hi) := by
      subst hchunk; simp [List.getElem_take, List.getElem_drop]
    simp [List.getElem_zipIdx, hci]
  have hspec := forIn_option_spec _ (leafPass rp L allDistinct b)
    (fun i s => PendingRel p S L (b * 64 + i) s.1 ∧
      s.2.length = (p.k + 1) * ((p.digitBits + 7) / 8))
    (fun i => LeafGood Blake2b.hashFn p.toParams S L (b * 64 + i)) 0 (pending, row)
    ⟨by simpa using hP, hrow⟩ (fun i hi s hs => by
      obtain ⟨pending', row'⟩ := s
      rw [hlen] at hi
      rw [helt i hi]
      simp only [Nat.zero_add] at hs ⊢
      have hc : b * 64 + i < 2 ^ p.k := by rw [← hL]; exact hcL i hi
      have := leafPass_spec h hst hD hL hAD hc (batch := b) (offset := i) rfl hs.1 hs.2
      exact ⟨fun hG => by
        obtain ⟨p', r', heq, hP', hr'⟩ := this.1 hG
        exact ⟨(p', r'), heq, by rwa [← Nat.add_assoc], hr'⟩, this.2⟩)
  simp only [Nat.zero_add, hlen] at hspec
  constructor
  · intro hall
    obtain ⟨s, hs, hP', hr'⟩ := hspec.1 hall
    refine ⟨_, by rw [hs]; rfl, hP', hr', ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_map, List.length_drop, hbl]; omega
    · simp only [List.length_append, List.length_map, List.length_drop, hdl]; omega
    · intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hd
        exact length_digest h hst hD _
      · exact hd64 d (List.mem_of_mem_drop hd)
  · intro hbad
    rw [hspec.2 hbad]
    rfl

end Batch

/-! ## `validate_tree` -/

section Tree

variable {rp : Params} {p : ZakuraParams} {S : List Byte} {L : List ℕ}

/-- `solution_indices`: `2^k`, which fits in a `usize` for every parameter set Zakura accepts
    (`k + 1 ≤ n / 8 ≤ 64`). -/
theorem Params.solutionIndices?_eq (h : rp.Is p) : rp.solutionIndices? = some (2 ^ p.k) := by
  have hd : 8 * (p.k + 1) ≤ p.n := (Nat.le_div_iff_mul_le (by omega)).mp p.digit_ge |>.trans_eq'
    (by ring)
  have hk : p.k < 64 := by have := p.n_le; omega
  simp only [Params.solutionIndices?, checkedShl?, USIZE_BITS, h.2, hk, ↓reduceIte,
    Nat.one_shiftLeft, Option.some.injEq]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hk)

/-- **`validate_tree` checks the tree.** When `hash` gives each block the BLAKE2b digest of
    the absorbed input followed by the block number, zero-padded to 64 bytes, `validate_tree`
    accepts `2^k` indices exactly when they form a `Good` tree whose root's last digit is zero:
    what the recursive verifier accepts (`isValidSolutionRecursive?_iff`). -/
theorem validateTree?_iff (h : rp.Is p) {st : Blake2b.State} (hst : StateFor p.toParams S st)
    {D : ℕ → List ℕ} (hD : ∀ b, D b = generateHash st b ++ List.replicate (64 - rp.hashOutput) 0)
    {hash : List ℕ → List (List ℕ) → Option (List (List ℕ))}
    (hhash : ∀ bs ds, ds.length = bs.length → (∀ d ∈ ds, d.length = 64) →
      hash bs ds = some (bs.map D))
    (hL : L.length = 2 ^ p.k) :
    validateTree? rp L hash = some () ↔
      Good Blake2b.hashFn p.toParams S p.k L ∧
        (rest p S p.k L).take p.digitBits = zeros p.digitBits := by
  have hc8 : 8 ≤ p.digitBits := p.digit_ge
  have hAD := @nodup_of_allDistinct L
  rw [validateTree?_eq, Params.solutionIndices?_eq h, hL]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, Option.bind_eq_bind,
    show chunks? L HASH_BATCH = some (chunksSucc 63 L) from rfl, Option.bind_some,
    Params.hashLength_eq h, Params.collisionByteLength_eq h, h.2]
  generalize hw : (p.digitBits + 7) / 8 = w at *
  -- The batches.
  have hch := chunksSucc_spec 63 L
  have hnb : ∀ b < (chunksSucc 63 L).length, b * 64 < L.length := fun b hb => by
    rw [hch.1, Nat.lt_div_iff_mul_lt (by norm_num)] at hb; omega
  have hspec := forIn_option_spec ((chunksSucc 63 L).zipIdx)
    (batchPass rp L ((L.mergeSort.zip L.mergeSort.tail).all fun (a, b) => a != b) hash)
    (fun b s => PendingRel p S L (min (b * 64) L.length) s.1 ∧
      s.2.1.length = (p.k + 1) * w ∧ s.2.2.1.length = 64 ∧ s.2.2.2.length = 64 ∧
      ∀ d ∈ s.2.2.2, d.length = 64)
    (fun b => ∀ i < ((L.drop (b * 64)).take 64).length,
      LeafGood Blake2b.hashFn p.toParams S L (b * 64 + i)) 0
    (List.replicate ((p.k + 1) * ((p.k + 1) * w)) 0, List.replicate ((p.k + 1) * w) 0,
      List.replicate HASH_BATCH 0, List.replicate HASH_BATCH (List.replicate 64 0))
    ⟨⟨by simp [← hw], fun h' _ hb => by simp at hb⟩, by simp, by simp [HASH_BATCH],
      by simp [HASH_BATCH], fun d hd => by simp [List.eq_of_mem_replicate hd]⟩
    (fun b hb s hs => by
      simp only [List.length_zipIdx] at hb
      obtain ⟨pending, row, blocks, digests⟩ := s
      simp only [Nat.zero_add] at hs ⊢
      rw [List.getElem_zipIdx, hch.2 b hb, Nat.zero_add]
      have hb64 := hnb b hb
      rw [Nat.min_eq_left hb64.le] at hs
      have := batchPass_spec (D := D) h hst hD hhash hL hAD hb64 hs.1
        (by rw [hw]; exact hs.2.1) hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
      refine ⟨fun hG => ?_, fun hG => this.2 (by
        by_contra hc; exact hG fun i hi => by by_contra hx; exact hc ⟨i, hi, hx⟩)⟩
      obtain ⟨s', heq, hP', hr', hb', hd', hd64'⟩ := this.1 hG
      refine ⟨s', heq, ?_, by rw [← hw]; exact hr', hb', hd', hd64'⟩
      simp only [List.length_take, List.length_drop] at hP'
      convert hP' using 2
      omega)
  simp only [Nat.zero_add, List.length_zipIdx] at hspec
  -- Every leaf's merges are good exactly when every batch's are.
  have hall : (∀ b < (chunksSucc 63 L).length, ∀ i < ((L.drop (b * 64)).take 64).length,
      LeafGood Blake2b.hashFn p.toParams S L (b * 64 + i)) ↔
      ∀ c < 2 ^ p.k, LeafGood Blake2b.hashFn p.toParams S L c := by
    constructor
    · intro hB c hc
      have hb : c / 64 < (chunksSucc 63 L).length := by
        rw [hch.1, Nat.lt_div_iff_mul_lt (by norm_num)]; omega
      have := hB (c / 64) hb (c % 64) (by simp; omega)
      rwa [Nat.div_add_mod' c 64] at this
    · intro hC b hb i hi
      exact hC _ (by simp at hi; omega)
  rw [← good_iff_leafGood _ _ _ _ _ hL] at hall
  by_cases hG : Good Blake2b.hashFn p.toParams S p.k L
  · obtain ⟨s, hs, hP, -⟩ := hspec.1 (hall.mpr hG)
    rw [hs, Option.bind_some]
    -- The root is slot `k`, which holds the whole tree.
    have hmin : min ((chunksSucc 63 L).length * 64) L.length = 2 ^ p.k := by
      rw [hch.1, ← hL]; omega
    rw [hmin] at hP
    have hE0 := hP.2 p.k le_rfl (by rw [Nat.div_self (Nat.two_pow_pos _)])
    rw [Nat.div_self (Nat.two_pow_pos _), Nat.sub_self, block_top _ _ hL, hw] at hE0
    have hE : ExpandedN p.digitBits w (slot p s.1 p.k) (rest p S p.k L) := hE0
    have hP1 : s.1.length = (p.k + 1) * ((p.k + 1) * w) := by rw [hP.1, hw]
    have hkR : p.k * ((p.k + 1) * w) + w ≤ s.1.length := by
      have : w ≤ (p.k + 1) * w := Nat.le_mul_of_pos_left _ (by omega)
      rw [hP1, Nat.succ_mul p.k ((p.k + 1) * w)]; omega
    have hroot : slice? s.1 (p.k * ((p.k + 1) * w)) (p.k * ((p.k + 1) * w) + w) =
        some (slot p s.1 p.k) := by
      rw [slice?_eq _ _ _ (by omega) hkR, Nat.add_sub_cancel_left, slot, hw]
      simp
    rw [hroot, Option.bind_some]
    have hl := length_rest p S p.k L
    have h1 : 1 ≤ (rest p S p.k L).length / p.digitBits := by
      rw [hl, Nat.mul_div_cancel _ (by omega)]; omega
    have hc : p.digitBits ≤ (rest p S p.k L).length := by
      rw [hl]; exact Nat.le_mul_of_pos_left _ (by omega)
    have hz := ExpandedN.take_eq_zero_iff (by omega) hE h1 hc
    have hsl : (slot p s.1 p.k).length = w := by
      rw [hE.1, hl, Nat.mul_div_cancel _ (by omega), Nat.add_sub_cancel_left, one_mul]
    rw [List.take_of_length_le hsl.le, List.eq_replicate_iff] at hz
    simp only [hG, true_and, ← hz, hsl]
    by_cases hr : (slot p s.1 p.k).all (· == 0) = true
    · simp only [hr, ↓reduceIte, Option.pure_def, true_iff]
      intro b hb; simpa using List.all_eq_true.mp hr b hb
    · simp only [hr, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff, not_forall]
      simpa [List.all_eq_true] using hr
  · obtain ⟨b, hb, hbad⟩ : ∃ b < (chunksSucc 63 L).length,
        ¬ ∀ i < ((L.drop (b * 64)).take 64).length,
          LeafGood Blake2b.hashFn p.toParams S L (b * 64 + i) := by
      by_contra hn; exact hG (hall.mp fun b hb => by by_contra hx; exact hn ⟨b, hb, hx⟩)
    rw [hspec.2 ⟨b, hb, hbad⟩]
    simp [hG]

end Tree

end Equihash.Verifier
