/-
`src/verify.rs`: the recursive Equihash verifier (test-only in the crate), and the single-pass
one `is_valid_solution` runs.

A Rust panic, and a Rust `Err`, are both `none`: the verifier did not accept.
-/
module

public import Equihash.Verifier.Blake2b
public import Equihash.Verifier.LeafHash
public import Equihash.Verifier.Lib
public import Equihash.Verifier.Minimal
public import Equihash.Verifier.Params

@[expose] public section

namespace Equihash.Verifier

/-- `Node` (`src/verify.rs`, lines 27–30): a subtree's expanded hash, and its indices. -/
structure Node where
  hash : List ℕ
  indices : List ℕ

/-- `initialise_state` (lines 136–145): BLAKE2b with a `digest_len`-byte output, personalized
    by `"ZcashPoW" ‖ n ‖ k`. `write_all` on a `Vec` appends and never fails. -/
def initialiseState? (n k digestLen : ℕ) : Option Blake2b.State := do
  let mut personalization := BLAKE2B_PERSONALIZATION_PREFIX
  personalization := personalization ++ u32ToLeBytes n
  personalization := personalization ++ u32ToLeBytes k
  let params ← Blake2b.Params.new.hashLength? digestLen
  let params ← params.personal? personalization
  return params.toState

/-- `generate_hash` (lines 148–155): the hash of the state's input followed by `i`,
    little-endian. `write_all` fills `lei`, four bytes, with `i.to_le_bytes()`. -/
def generateHash (baseState : Blake2b.State) (i : ℕ) : List ℕ :=
  let lei := u32ToLeBytes i
  let state := baseState.update lei
  state.finalize

namespace Node

/-- `Node::new` (lines 34–42): the leaf for index `i`. -/
def new? (p : Params) (state : Blake2b.State) (i : ℕ) : Option Node := do
  let hash := generateHash state (i / p.indicesPerHashOutput)
  let start := i % p.indicesPerHashOutput * p.n / 8
  let «end» := start + p.n / 8
  let bytes ← slice? hash start «end»
  let hash ← expandArray? bytes p.collisionBitLength 0
  return { hash, indices := [i] }

/-- `Node::indices_before` (lines 86–90): `self.indices[0] < other.indices[0]`. -/
def indicesBefore? (self other : Node) : Option Bool := do
  let a ← self.indices[0]?
  let b ← other.indices[0]?
  return a < b

/-- `Node::from_children` (lines 46–64): the hashes XORed, without the first `trim` bytes,
    and the indices of the subtree that starts first, then the other's. -/
def fromChildren? (a b : Node) (trim : ℕ) : Option Node := do
  let hash := ((a.hash.zip b.hash).drop trim).map fun (x, y) => x ^^^ y
  let indices ← if ← a.indicesBefore? b then
      pure (a.indices ++ b.indices)
    else
      pure (b.indices ++ a.indices)
  return { hash, indices }

/-- `Node::is_zero` (lines 92–94): `self.hash.iter().take(len).all(|v| *v == 0)`. -/
def isZero (self : Node) (len : ℕ) : Bool := (self.hash.take len).all (· == 0)

end Node

/-- `has_collision` (lines 158–164):
    `a.hash.iter().zip(b.hash.iter()).take(len).all(|(a, b)| a == b)`. -/
def hasCollision (a b : Node) (len : ℕ) : Bool :=
  ((a.hash.zip b.hash).take len).all fun (x, y) => x == y

/-- `distinct_indices` (lines 167–176). -/
def distinctIndices (a b : Node) : Bool := Id.run do
  for i in a.indices do
    for j in b.indices do
      if i == j then
        return false
  return true

/-- `validate_subtrees` (lines 179–189): `Err(Collision)`, `Err(OutOfOrder)` or
    `Err(DuplicateIdxs)`, in that order, or `Ok(())`. -/
def validateSubtrees? (p : Params) (a b : Node) : Option Unit := do
  if !hasCollision a b p.collisionByteLength then
    none
  else if ← b.indicesBefore? a then
    none
  else if !distinctIndices a b then
    none
  else
    return ()

/-- `tree_validator` (lines 230–241): checks the two halves of `indices`, then their merge. -/
def treeValidator? (p : Params) (state : Blake2b.State) (indices : List ℕ) : Option Node :=
  if h : indices.length > 1 then do
    let «end» := indices.length
    let mid := «end» / 2
    let a ← treeValidator? p state (indices.take mid)
    let b ← treeValidator? p state (indices.drop mid)
    validateSubtrees? p a b
    Node.fromChildren? a b p.collisionByteLength
  else do
    let i ← indices[0]?
    Node.new? p state i
termination_by indices.length
decreasing_by all_goals simp only [List.length_take, List.length_drop]; omega

/-- `is_valid_solution_recursive` (lines 244–262): `some ()` exactly when the Rust returns
    `Ok(())`. -/
def isValidSolutionRecursive? (p : Params) (input nonce : List ℕ) (indices : List ℕ) :
    Option Unit := do
  let mut state ← initialiseState? p.n p.k p.hashOutput
  state := state.update input
  state := state.update nonce
  let root ← treeValidator? p state indices
  -- Hashes were trimmed, so only need to check remaining length.
  if root.isZero p.collisionByteLength then
    return ()
  else
    none

/-- `HASH_BATCH` (line 287): the leaves hashed per call to `validate_tree`'s `hash`. -/
def HASH_BATCH : ℕ := 64

/-- `validate_tree` (lines 294–380): checks the solution tree for `indices` in one pass over
    its leaves, keeping the unmerged left subtree of each height; `some ()` exactly when the
    Rust returns `Ok(())`.

`hash blocks digests` is the closure call `hash(blocks, digests)`, returning `digests` as the
closure leaves them, or `none` where it panics. `sort_unstable` is `List.mergeSort`: both
sort, and a list of numbers has one sorted order, so which algorithm sorts does not matter.
Rust's subtractions `leaf + 1 - (1 << height)` and `right_start - (1 << height)` cannot
underflow, since bits `0 .. height` of `leaf` are set; `leaf >> height` and `1 << height` cannot
overflow, since `leaf < 2^k` keeps `height ≤ k`, and `Params::new` keeps `k ≤ 63`; `row.set`
never writes past `row`, whose length is `row_len`. -/
def validateTree? (p : Params) (indices : List ℕ)
    (hash : List ℕ → List (List ℕ) → Option (List (List ℕ))) : Option Unit := do
  -- Anything else would leave the tree, or its root, partly unvisited.
  let leaves := indices.length
  if p.solutionIndices? ≠ some leaves then
    none
  let perHash := p.indicesPerHashOutput
  let leafBytes := p.n / 8
  let collisionBytes := p.collisionByteLength
  let rowLen := p.hashLength
  -- With every index distinct, each subtree pair's duplicate check passes.
  let sorted := indices.mergeSort
  let allDistinct := (sorted.zip sorted.tail).all fun (a, b) => a != b
  -- `pending[h]` holds the unmerged left subtree of height `h`, which has
  -- `row_len - h * collision_bytes` hash bytes after trimming.
  let mut pending := List.replicate ((p.k + 1) * rowLen) 0
  let mut row := List.replicate rowLen 0
  let mut blocks := List.replicate HASH_BATCH 0
  let mut digests := List.replicate HASH_BATCH (List.replicate 64 0)
  for (chunk, batch) in (← chunks? indices HASH_BATCH).zipIdx do
    -- `&mut blocks[..chunk.len()]` and `&mut digests[..chunk.len()]`.
    let mut bs := blocks.take chunk.length
    for (index, j) in chunk.zipIdx do
      bs := bs.set j (index / perHash)
    blocks := bs ++ blocks.drop chunk.length
    let ds ← hash bs (digests.take chunk.length)
    digests := ds ++ digests.drop chunk.length
    for ((index, digest), offset) in (chunk.zip ds).zipIdx do
      let leaf := batch * HASH_BATCH + offset
      let start := index % perHash * leafBytes
      row ← expandArrayInto? (← slice? digest start (start + leafBytes)) p.collisionBitLength 0
        row
      -- Each set low bit of `leaf` marks a pending left sibling.
      let mut height := 0
      while (leaf >>> height) &&& 1 = 1 do
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
        -- On success the merged subtree's indices are `left || right`,
        -- which is their order in `indices`.
        for (l, i) in (← slice? left collisionBytes left.length).zipIdx do
          row := row.set i (l ^^^ (← row[collisionBytes + i]?))
        height := height + 1
      let len := rowLen - height * collisionBytes
      pending ← copyFromSlice? pending (height * rowLen) (← slice? row 0 len)
  -- Hashes were trimmed, so the root holds one collision's worth of bytes.
  let root ← slice? pending (p.k * rowLen) (p.k * rowLen + collisionBytes)
  if root.all (· == 0) then
    return ()
  else
    none

/-- `is_valid_solution` (lines 269–280): `some ()` exactly when the Rust returns `Ok(())` for
    `soln`, a minimally encoded solution for `input ‖ nonce` with parameters `n` and `k`.

`LeafHasher::new` runs the portable kernel here (see `LeafHasher.new?`). -/
def isValidSolution? (n k : ℕ) (input nonce soln : List ℕ) : Option Unit := do
  let p ← Params.new? n k
  let indices ← indicesFromMinimal? p soln
  let hasher ← LeafHasher.new? p input nonce
  validateTree? p indices fun blocks digests => hasher.hash? blocks digests

end Equihash.Verifier
