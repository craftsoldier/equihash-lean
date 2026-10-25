/-
`zakura-equihash 4.0.0`'s `is_valid_solution` on the two real blocks of `Tests/Spec.lean`, and
the cases of the crate's own tests of it (`src/verify.rs`).
-/
import Equihash.Tests.Verifier

open Equihash.Verifier

-- `mainnet_block_415000` (`src/verify.rs`, lines 476–496): valid; still valid with the whole
-- 140-byte prefix as `input`; a changed nonce is rejected.
#guard isValidSolution? 200 9 blockHeader blockNonce solution = some ()
#guard isValidSolution? 200 9 (blockHeader ++ blockNonce) [] solution = some ()
#guard isValidSolution? 200 9 blockHeader (blockNonce.set 31 (blockNonce[31]! ^^^ 1)) solution =
  none

-- `regtest_genesis` (lines 499–527): valid; rejected with any one bit of the solution or the
-- nonce flipped; rejected with mainnet parameters.
#guard isValidSolution? 48 5 regtestHeader regtestNonce regtestSolution = some ()
#guard (List.range (regtestSolution.length * 8)).all fun i =>
  isValidSolution? 48 5 regtestHeader regtestNonce
    (regtestSolution.set (i / 8) (regtestSolution[i / 8]! ^^^ 1 <<< (i % 8))) == none
#guard (List.range (regtestNonce.length * 8)).all fun i =>
  isValidSolution? 48 5 regtestHeader
    (regtestNonce.set (i / 8) (regtestNonce[i / 8]! ^^^ 1 <<< (i % 8))) regtestSolution == none
#guard isValidSolution? 200 9 regtestHeader regtestNonce regtestSolution = none

-- `rejects_unsupported_parameters` (lines 530–594): what `Params::new` rejects and accepts;
-- rejected parameters with an empty and a one-byte solution; `(264, 32)`, whose `2^32` leaves are
-- counted, not wrapped; and `(512, 63)`, whose solution length overflows.
#guard [(520, 64), (1024, 3), (48, 7), (200, 7), (104, 3), (448, 63),
    (134217736, 16777216)].all fun (n, k) => (Params.new? n k).isNone
#guard [(200, 9), (48, 5), (96, 5), (144, 5), (96, 3), (512, 63)].all fun (n, k) =>
  (Params.new? n k).isSome
#guard [(448, 63), (134217736, 16777216)].all fun (n, k) =>
  [[], [0]].all fun soln => isValidSolution? n k blockHeader blockNonce soln == none
#guard (Params.new? 264 32).isSome
#guard Params.solutionIndices? ⟨264, 32⟩ = some (2 ^ 32)
#guard isValidSolution? 264 32 blockHeader blockNonce [0] = none
#guard Params.solutionBytes? ⟨512, 63⟩ = none
#guard isValidSolution? 512 63 blockHeader blockNonce (List.replicate 9 0) = none

-- `validate_tree_rejects_wrong_leaf_counts` (lines 597–607).
#guard [0, 1, 511, 513].all fun leaves =>
  validateTree? ⟨200, 9⟩ (List.range leaves)
    (fun _ ds => some (ds.map fun _ => List.replicate 64 0)) == none

-- `rejects_other_input_lengths` (lines 627–653): other prefix lengths; with no prefix, other
-- parameters and a solution one byte short.
#guard isValidSolution? 200 9 (blockHeader.take 107) blockNonce solution = none
#guard isValidSolution? 200 9 blockHeader (blockNonce.take 31) solution = none
#guard isValidSolution? 200 9 (blockHeader ++ [0]) blockNonce solution = none
#guard isValidSolution? 200 9 [] [] solution = none
#guard isValidSolution? 200 8 [] [] solution = none
#guard isValidSolution? 200 9 [] [] solution.tail = none

-- The leaf hasher on the 140-byte prefix: the digests of the reference closure, for blocks from
-- the first to the last one a `(200, 9)` solution can name.
#guard (do
  let lh ← LeafHasher.new? ⟨200, 9⟩ blockHeader blockNonce
  let blocks := [0, 1, 2, 1000, 524287]
  let digests := List.replicate blocks.length (List.replicate 64 0)
  return (← lh.hash? blocks digests) ==
    (← referenceHash ⟨200, 9⟩ blockHeader blockNonce blocks digests)) = some true
