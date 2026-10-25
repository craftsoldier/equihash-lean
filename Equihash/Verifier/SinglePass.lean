/-
`src/verify.rs`: the single-pass Equihash verifier.

A Rust panic is `none`; a function returning a Rust `Result` is into `ExceptT Kind Option`
(`Verifier/Error.lean`).
-/
module

public import Equihash.Verifier.Error
public import Equihash.Verifier.Minimal
public import Equihash.Verifier.Params

@[expose] public section

namespace Equihash.Verifier

/-- `HASH_BATCH` (line 287): the leaves hashed per call to `validate_tree`'s `hash`. -/
def HASH_BATCH : ℕ := 64

/-- `validate_tree` (lines 294–380): checks the solution tree for `indices` in one pass over
    its leaves, keeping the unmerged left subtree of each height.

`hash blocks digests` is the closure call `hash(blocks, digests)`, returning `digests` as the
closure leaves them, or `none` where it panics. `sort_unstable` is `List.mergeSort`: both
sort, and a list of numbers has one sorted order, so which algorithm sorts does not matter.
Rust's subtractions `leaf + 1 - (1 << height)` and `right_start - (1 << height)` cannot
underflow, since bits `0 .. height` of `leaf` are set; `leaf >> height` and `1 << height` cannot
overflow, since `leaf < 2^k` keeps `height ≤ k`, and `Params::new` keeps `k ≤ 63`.
`row[i] = …` panics out of bounds, as `set?` does. `*block = …` writes through `iter_mut`, which
indexes nothing, so it is `bs.set j` with `j` below `bs.len()`. -/
def validateTree? (p : Params) (indices : List ℕ)
    (hash : List ℕ → List (List ℕ) → Option (List (List ℕ))) : ExceptT Kind Option Unit := do
  -- Anything else would leave the tree, or its root, partly unvisited.
  let leaves := indices.length
  if p.solutionIndices? ≠ some leaves then
    throw .InvalidParams
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
          throw .Collision
        if (← (rightIndices[0]? : Option ℕ)) < (← (leftIndices[0]? : Option ℕ)) then
          throw .OutOfOrder
        if !allDistinct && leftIndices.any (fun i => rightIndices.contains i) then
          throw .DuplicateIdxs
        -- On success the merged subtree's indices are `left || right`,
        -- which is their order in `indices`.
        for (l, i) in (← slice? left collisionBytes left.length).zipIdx do
          row ← set? row i (l ^^^ (← (row[collisionBytes + i]? : Option ℕ)))
        height := height + 1
      let len := rowLen - height * collisionBytes
      pending ← copyFromSlice? pending (height * rowLen) (← slice? row 0 len)
  -- Hashes were trimmed, so the root holds one collision's worth of bytes.
  let root ← slice? pending (p.k * rowLen) (p.k * rowLen + collisionBytes)
  if root.all (· == 0) then
    return ()
  else
    throw .NonZeroRootHash

end Equihash.Verifier
