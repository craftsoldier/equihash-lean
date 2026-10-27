/-
Each release's `is_valid_solution` on the two real blocks of `Tests/Spec.lean`, and the cases of
the crate's own tests of it (`src/verify.rs`), with the error the crate expects: first
`zakura-equihash 4.0.0`, then `equihash 0.3.0`, then `equihash 0.3.1`. The blocks are verified
under every leaf-hashing kernel, and the kernels are compared with `blake2b_simd` as the crate
compares them; the rest runs the portable kernel.
-/
import Equihash.Tests.Verifier

open Equihash.Verifier Equihash.Verifier.LeafHash

/-- An `Err`, of any kind, and not a panic: what the crate's `unwrap_err()` checks. -/
def isErr (r : Option (Except Kind Unit)) : Bool :=
  match r with
  | some (.error _) => true
  | _ => false

/-- `Kernel::ALL` (`src/leaf_hash.rs`, lines 295–303), on a CPU that supports every kernel. -/
def kernels : List Kernel := [.portable, .avx2, .neon, .neonSha3]

-- `mainnet_block_415000` (`src/verify.rs`, lines 476–496): valid, under every kernel; still
-- valid with the whole 140-byte prefix as `input`; a changed nonce is rejected.
#guard kernels.all fun kernel =>
  (isValidSolution? kernel 200 9 blockHeader blockNonce solution).run == some (.ok ())
#guard (isValidSolution? .portable 200 9 (blockHeader ++ blockNonce) [] solution).run =
  some (.ok ())
#guard isErr (isValidSolution? .portable 200 9 blockHeader
  (blockNonce.set 31 (blockNonce[31]! ^^^ 1)) solution).run

-- `regtest_genesis` (lines 499–527): valid, under every kernel; rejected with any one bit of the
-- solution or the nonce flipped; rejected with mainnet parameters.
#guard kernels.all fun kernel =>
  (isValidSolution? kernel 48 5 regtestHeader regtestNonce regtestSolution).run == some (.ok ())
#guard (List.range (regtestSolution.length * 8)).all fun i =>
  isErr (isValidSolution? .portable 48 5 regtestHeader regtestNonce
    (regtestSolution.set (i / 8) (regtestSolution[i / 8]! ^^^ 1 <<< (i % 8)))).run
#guard (List.range (regtestNonce.length * 8)).all fun i =>
  isErr (isValidSolution? .portable 48 5 regtestHeader
    (regtestNonce.set (i / 8) (regtestNonce[i / 8]! ^^^ 1 <<< (i % 8))) regtestSolution).run
#guard isErr (isValidSolution? .portable 200 9 regtestHeader regtestNonce regtestSolution).run

-- `rejects_unsupported_parameters` (lines 530–594): what `Params::new` rejects and accepts;
-- rejected parameters with an empty and a one-byte solution; `(264, 32)`, whose `2^32` leaves are
-- counted, not wrapped; and `(512, 63)`, whose solution length overflows.
#guard [(520, 64), (1024, 3), (48, 7), (200, 7), (104, 3), (448, 63),
    (134217736, 16777216)].all fun (n, k) => (Params.new? n k).isNone
#guard [(200, 9), (48, 5), (96, 5), (144, 5), (96, 3), (512, 63)].all fun (n, k) =>
  (Params.new? n k).isSome
#guard [(448, 63), (134217736, 16777216)].all fun (n, k) =>
  [[], [0]].all fun soln =>
    (isValidSolution? .portable n k blockHeader blockNonce soln).run ==
      some (.error .InvalidParams)
#guard (Params.new? 264 32).isSome
#guard Params.solutionIndices? ⟨264, 32⟩ = some (2 ^ 32)
#guard (isValidSolution? .portable 264 32 blockHeader blockNonce [0]).run =
  some (.error .InvalidParams)
#guard Params.solutionBytes? ⟨512, 63⟩ = none
#guard (isValidSolution? .portable 512 63 blockHeader blockNonce (List.replicate 9 0)).run =
  some (.error .InvalidParams)

-- `validate_tree_rejects_wrong_leaf_counts` (lines 597–607).
#guard [0, 1, 511, 513].all fun leaves =>
  (validateTree? ⟨200, 9⟩ (List.range leaves)
    (fun _ ds => some (ds.map fun _ => List.replicate 64 0))).run == some (.error .InvalidParams)

-- `rejects_other_input_lengths` (lines 627–653): other prefix lengths; with no prefix, other
-- parameters and a solution one byte short, reported first.
#guard (isValidSolution? .portable 200 9 (blockHeader.take 107) blockNonce solution).run =
  some (.error .UnsupportedInputLength)
#guard (isValidSolution? .portable 200 9 blockHeader (blockNonce.take 31) solution).run =
  some (.error .UnsupportedInputLength)
#guard (isValidSolution? .portable 200 9 (blockHeader ++ [0]) blockNonce solution).run =
  some (.error .UnsupportedInputLength)
#guard (isValidSolution? .portable 200 9 [] [] solution).run =
  some (.error .UnsupportedInputLength)
#guard (isValidSolution? .portable 200 8 [] [] solution).run = some (.error .InvalidParams)
#guard (isValidSolution? .portable 200 9 [] [] solution.tail).run =
  some (.error .InvalidParams)

-- The leaf hasher on the 140-byte prefix, under every kernel: the digests of the reference
-- closure, for blocks from the first to the last one a `(200, 9)` solution can name.
#guard kernels.all fun kernel => (do
  let some lh ← LeafHasher.new? ⟨200, 9⟩ blockHeader blockNonce kernel | none
  let blocks := [0, 1, 2, 1000, 524287]
  let digests := List.replicate blocks.length (List.replicate 64 0)
  return (← lh.hash? blocks digests) ==
    (← referenceHash ⟨200, 9⟩ blockHeader blockNonce blocks digests)) == some true

-- `kernels_match_blake2b_simd` (`src/leaf_hash.rs`, lines 419–455): every kernel, on 71 block
-- indices (an odd count leaves a portable tail after every lane width), under five parameter
-- sets and four splits of a 140-byte prefix, writes `blake2b_simd`'s digests over `0xa5` bytes.
#guard
  let blocks := ((List.range 67).map fun i => i * 0x9e3779b9 % 2 ^ 32) ++
    [0, 1, 2 ^ 32 - 1, 2 ^ 32 - 2]
  let header := (List.range (HEADER_BYTES + NONCE_BYTES)).map fun i => (i * 31 + 7) % 256
  [(200, 9), (48, 5), (96, 5), (144, 5), (96, 3)].all fun (n, k) =>
    [HEADER_BYTES, 0, 128, HEADER_BYTES + NONCE_BYTES].all fun split =>
      kernels.all fun kernel => (do
        let (input, nonce) := (header.take split, header.drop split)
        let some lh ← LeafHasher.withKernel? ⟨n, k⟩ input nonce kernel | none
        let out := List.replicate blocks.length (List.replicate 64 0xa5)
        return (← lh.hash? blocks out) == (← referenceHash ⟨n, k⟩ input nonce blocks
          (List.replicate blocks.length (List.replicate 64 0)))) == some true

-- `rejects_other_prefix_lengths` (lines 492–499): `LeafHasher::new` takes 140-byte prefixes only.
#guard [0, 12, 107, 139, 141, 268].all fun len =>
  let r := LeafHasher.new? ⟨200, 9⟩ (List.replicate len 0) [] .portable
  r.isSome && r.join.isNone
#guard (LeafHasher.new? ⟨200, 9⟩ (List.replicate HEADER_BYTES 0) (List.replicate NONCE_BYTES 0)
  .portable).join.isSome

/-! ## `equihash 0.3.0` -/

-- The mainnet and Regtest blocks: valid, also with the whole prefix as `input`; any one bit of
-- the Regtest solution or nonce flipped is rejected.
#guard (isValidSolution_equihash_0_3_0? 200 9 blockHeader blockNonce solution).run =
  some (.ok ())
#guard (isValidSolution_equihash_0_3_0? 200 9 (blockHeader ++ blockNonce) [] solution).run =
  some (.ok ())
#guard (isValidSolution_equihash_0_3_0? 48 5 regtestHeader regtestNonce regtestSolution).run =
  some (.ok ())
#guard (List.range (regtestSolution.length * 8)).all fun i =>
  isErr (isValidSolution_equihash_0_3_0? 48 5 regtestHeader regtestNonce
    (regtestSolution.set (i / 8) (regtestSolution[i / 8]! ^^^ 1 <<< (i % 8)))).run
#guard (List.range (regtestNonce.length * 8)).all fun i =>
  isErr (isValidSolution_equihash_0_3_0? 48 5 regtestHeader
    (regtestNonce.set (i / 8) (regtestNonce[i / 8]! ^^^ 1 <<< (i % 8))) regtestSolution).run

/-- The input of 0.3.0's `all_bits_matter` (`src/verify.rs`, lines 291–317): 72 bytes. -/
def allBitsInput : List ℕ :=
  bytes "Equihash is an asymmetric PoW based on the Generalised Birthday problem."

/-- Its `(96, 5)` solution, minimally encoded. -/
def allBitsSolution : List ℕ := [
  0x04, 0x6a, 0x8e, 0xd4, 0x51, 0xa2, 0x19, 0x73, 0x32, 0xe7, 0x1f, 0x39, 0xdb, 0x9c,
  0x79, 0xfb, 0xf9, 0x3f, 0xc1, 0x44, 0x3d, 0xa5, 0x8f, 0xb3, 0x8d, 0x05, 0x99, 0x17,
  0x21, 0x16, 0xd5, 0x55, 0xb1, 0xb2, 0x1f, 0x32, 0x70, 0x5c, 0xe9, 0x98, 0xf6, 0x0d,
  0xa8, 0x52, 0xf7, 0x7f, 0x0e, 0x7f, 0x4d, 0x63, 0xfc, 0x2d, 0xd2, 0x30, 0xa3, 0xd9,
  0x99, 0x53, 0xa0, 0x78, 0x7d, 0xfe, 0xfc, 0xab, 0x34, 0x1b, 0xde, 0xc8]

-- `all_bits_matter`: valid with a 72-byte input, which Zakura rejects as a length it does not
-- support; any one bit of the solution flipped is rejected.
#guard (isValidSolution_equihash_0_3_0? 96 5 allBitsInput (nonce [1]) allBitsSolution).run =
  some (.ok ())
#guard (isValidSolution? .portable 96 5 allBitsInput (nonce [1]) allBitsSolution).run =
  some (.error .UnsupportedInputLength)
#guard (List.range (allBitsSolution.length * 8)).all fun i =>
  isErr (isValidSolution_equihash_0_3_0? 96 5 allBitsInput (nonce [1])
    (allBitsSolution.set (i / 8) (allBitsSolution[i / 8]! ^^^ 1 <<< (i % 8)))).run

-- Lengths that overflow (`isValidSolution_equihash_0_3_0?_448_63` and `_520_64`): 0.3.0 panics
-- where Zakura returns `InvalidParams`.
#guard (isValidSolution_equihash_0_3_0? 448 63 blockHeader blockNonce []).run = none
#guard (isValidSolution_equihash_0_3_0? 520 64 blockHeader blockNonce [0]).run = none
#guard (isValidSolution? .portable 448 63 blockHeader blockNonce []).run =
  some (.error .InvalidParams)
#guard (isValidSolution? .portable 520 64 blockHeader blockNonce [0]).run =
  some (.error .InvalidParams)

-- Parameters 0.3.0's `Params::new` accepts and Zakura's rejects: unusual collision widths panic
-- on a solution of the length they expect (`(48, 7)`: 112 bytes; `(104, 3)`: 27 bytes).
#guard (Params.newUnbounded? 48 7).isSome && (Params.new? 48 7).isNone
#guard (isValidSolution_equihash_0_3_0? 48 7 blockHeader blockNonce (List.replicate 112 0)).run =
  none
#guard (isValidSolution_equihash_0_3_0? 104 3 blockHeader blockNonce (List.replicate 27 0)).run =
  none

/-! ## `equihash 0.3.1` -/

-- A default build has only the portable kernel; one with `unsafe-verifier` has them all.

-- `zcash_block_headers` (`src/verify.rs`, lines 329–362): the mainnet and Regtest blocks are
-- valid, under every kernel, also with the whole prefix as `input`; any one bit of either
-- solution flipped is rejected.
#guard kernels.all fun kernel =>
  (isValidSolution_equihash_0_3_1? kernel 200 9 blockHeader blockNonce solution).run ==
    some (.ok ())
#guard (isValidSolution_equihash_0_3_1? .portable 200 9 (blockHeader ++ blockNonce) []
  solution).run = some (.ok ())
#guard (List.range (solution.length * 8)).all fun i =>
  isErr (isValidSolution_equihash_0_3_1? .portable 200 9 blockHeader blockNonce
    (solution.set (i / 8) (solution[i / 8]! ^^^ 1 <<< (i % 8)))).run
#guard kernels.all fun kernel =>
  (isValidSolution_equihash_0_3_1? kernel 48 5 regtestHeader regtestNonce regtestSolution).run ==
    some (.ok ())
#guard (isValidSolution_equihash_0_3_1? .portable 48 5 (regtestHeader ++ regtestNonce) []
  regtestSolution).run = some (.ok ())
#guard (List.range (regtestSolution.length * 8)).all fun i =>
  isErr (isValidSolution_equihash_0_3_1? .portable 48 5 regtestHeader regtestNonce
    (regtestSolution.set (i / 8) (regtestSolution[i / 8]! ^^^ 1 <<< (i % 8)))).run

-- `all_bits_matter` (lines 365–391): valid with a 72-byte input, hashed with `blake2b_simd`, as
-- the leaf hasher takes only 140-byte prefixes; any one bit of the solution flipped is rejected.
#guard (isValidSolution_equihash_0_3_1? .portable 96 5 allBitsInput (nonce [1])
  allBitsSolution).run = some (.ok ())
#guard (List.range (allBitsSolution.length * 8)).all fun i =>
  isErr (isValidSolution_equihash_0_3_1? .portable 96 5 allBitsInput (nonce [1])
    (allBitsSolution.set (i / 8) (allBitsSolution[i / 8]! ^^^ 1 <<< (i % 8)))).run

-- The `blake2b_simd` path on the mainnet block: a prefix one byte short or long is not a length
-- the verifier refuses, as Zakura does, but one its solution fails for.
#guard (isValidSolution_equihash_0_3_1? .portable 200 9 (blockHeader.take 107) blockNonce
  solution).run = some (.error .Collision)
#guard (isValidSolution_equihash_0_3_1? .portable 200 9 (blockHeader ++ [0]) blockNonce
  solution).run = some (.error .Collision)

-- `solution_length_overflow_is_rejected` (`src/minimal.rs`, lines 170–175): `(512, 63)`, whose
-- solution length overflows, passes `Params::new` and fails `indices_from_minimal`.
#guard (Params.newUnbounded? 512 63).isSome
#guard Params.solutionBytes? ⟨512, 63⟩ = none
#guard [[], [0]].all fun soln => indicesFromMinimal? ⟨512, 63⟩ soln == some none
#guard (isValidSolution_equihash_0_3_1? .portable 512 63 blockHeader blockNonce []).run =
  some (.error .InvalidParams)

-- The lengths 0.3.0 wraps (`isValidSolution_equihash_0_3_1?_448_63` and `_520_64`): rejected.
#guard (isValidSolution_equihash_0_3_1? .portable 448 63 blockHeader blockNonce []).run =
  some (.error .InvalidParams)
#guard (isValidSolution_equihash_0_3_1? .portable 520 64 blockHeader blockNonce [0]).run =
  some (.error .InvalidParams)

-- Parameters `Params::new` accepts and Zakura's rejects still panic on a solution of the length
-- they expect, as in 0.3.0.
#guard (isValidSolution_equihash_0_3_1? .portable 48 7 blockHeader blockNonce
  (List.replicate 112 0)).run = none
#guard (isValidSolution_equihash_0_3_1? .portable 104 3 blockHeader blockNonce
  (List.replicate 27 0)).run = none
