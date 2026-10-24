/-
`src/verify.rs`: the recursive Equihash verifier.

A Rust panic, and a Rust `Err`, are both `none`: the verifier did not accept.
-/
module

public import Equihash.Verifier.Blake2b
public import Equihash.Verifier.Minimal
public import Equihash.Verifier.Params

@[expose] public section

namespace Equihash.Verifier

/-- `BLAKE2B_PERSONALIZATION_PREFIX` (`src/lib.rs`, line 40): `*b"ZcashPoW"`. -/
def BLAKE2B_PERSONALIZATION_PREFIX : List ℕ := [90, 99, 97, 115, 104, 80, 111, 87]

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

end Equihash.Verifier
