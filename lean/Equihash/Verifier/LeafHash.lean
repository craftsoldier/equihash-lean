/-
`src/leaf_hash.rs`: BLAKE2b of each leaf's block, from the midstate of the 140-byte prefix
`input ‖ nonce` that every leaf shares; the portable, one-lane kernel.

The crate also has AVX2 and NEON kernels, which `Kernel::detect` picks on CPUs that support
them. They are not transcribed here: the verifier below runs the portable kernel.
-/
module

public import Equihash.Verifier.Lib
public import Equihash.Verifier.Params

@[expose] public section

namespace Equihash.Verifier

/-- `blake2b_simd::BLOCKBYTES` (`blake2b_simd 1.0.4`, `src/lib.rs`, line 77): 128 bytes. -/
def BLOCKBYTES : ℕ := 128

namespace LeafHash

/-- `IV` (`src/leaf_hash.rs`, lines 25–34). -/
def IV : Array UInt64 := #[
  0x6A09E667F3BCC908, 0xBB67AE8584CAA73B, 0x3C6EF372FE94F82B, 0xA54FF53A5F1D36F1,
  0x510E527FADE682D1, 0x9B05688C2B3E6C1F, 0x1F83D9ABFB41BD6B, 0x5BE0CD19137E2179]

/-- `SIGMA` (lines 36–49): twelve rows, one per round. -/
def SIGMA : Array (Array ℕ) := #[
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
  #[14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
  #[11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
  #[7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
  #[9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
  #[2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
  #[12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
  #[13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
  #[6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
  #[10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
  #[14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3]]

/-- `HEADER_BYTES` (line 52): a Zcash block header without its nonce and solution. -/
def HEADER_BYTES : ℕ := 108

/-- `NONCE_BYTES` (line 55): a Zcash block header nonce. -/
def NONCE_BYTES : ℕ := 32

/-- `TAIL_BYTES` (line 58): the prefix bytes left in the final block. -/
def TAIL_BYTES : ℕ := (HEADER_BYTES + NONCE_BYTES) % BLOCKBYTES

/-- `g` (lines 126–137) for one lane (`L = u64`, lines 84–123): `add` is `wrapping_add`,
    and `xor_rotrN` is `(self ^ other).rotate_right(N)`. -/
def g (v : Array UInt64) (a b c d : ℕ) (x y : UInt64) : Array UInt64 :=
  let v := v.set! a (v[a]! + v[b]! + x)
  let v := v.set! d (rotateRight (v[d]! ^^^ v[a]!) 32)
  let v := v.set! c (v[c]! + v[d]!)
  let v := v.set! b (rotateRight (v[b]! ^^^ v[c]!) 24)
  let v := v.set! a (v[a]! + v[b]! + y)
  let v := v.set! d (rotateRight (v[d]! ^^^ v[a]!) 16)
  let v := v.set! c (v[c]! + v[d]!)
  v.set! b (rotateRight (v[b]! ^^^ v[c]!) 63)

/-- `rounds!(v, word; 0 1 2 3 4 5 6 7 8 9 10 11)` (lines 141–153): the macro writes out one
    round per row of `SIGMA`, here a loop over the rows. -/
def rounds (v : Array UInt64) (word : ℕ → UInt64) : Array UInt64 := Id.run do
  let mut v := v
  for r in [0:12] do
    let S := SIGMA[r]!
    v := g v 0 4 8 12 (word S[0]!) (word S[1]!)
    v := g v 1 5 9 13 (word S[2]!) (word S[3]!)
    v := g v 2 6 10 14 (word S[4]!) (word S[5]!)
    v := g v 3 7 11 15 (word S[6]!) (word S[7]!)
    v := g v 0 5 10 15 (word S[8]!) (word S[9]!)
    v := g v 1 6 11 12 (word S[10]!) (word S[11]!)
    v := g v 2 7 8 13 (word S[12]!) (word S[13]!)
    v := g v 3 4 9 14 (word S[14]!) (word S[15]!)
  return v

/-- `compress_prefix_block` (lines 156–171): compresses one non-final 128-byte block into `h`,
    with `count` bytes hashed so far. -/
def compressPrefixBlock (h : Array UInt64) (block : List ℕ) (count : UInt64) : Array UInt64 :=
  Id.run do
  let m := (List.range 16).toArray.map fun i => u64FromLeBytes ((block.drop (8 * i)).take 8)
  let word := fun i => m[i]!
  let mut v := h ++ IV
  v := v.set! 12 (v[12]! ^^^ count)
  v := rounds v word
  let mut h := h
  for i in [0:8] do
    h := h.set! i (h[i]! ^^^ (v[i]! ^^^ v[i + 8]!))
  return h

/-- `Midstate` (lines 175–183): the prefix state shared by every leaf of one solution. -/
structure Midstate where
  h : Array UInt64
  m0 : UInt64
  m1Low : UInt64
  count : UInt64

/-- `Midstate::new` (lines 189–226): the state after the prefix's first block, and the 12
    prefix bytes left for the final block; `none` unless `input ‖ nonce` is 140 bytes.

`checked_add` of two slice lengths cannot overflow, so it is a plain `+` here. The closing
`debug_assert_eq!(filled, TAIL_BYTES)` holds for every 140-byte prefix
(`Midstate.new?_spec`), so it is left out. -/
def Midstate.new? (p : Params) (input nonce : List ℕ) : Option Midstate := do
  if input.length + nonce.length ≠ HEADER_BYTES + NONCE_BYTES then
    none
  let count : UInt64 := UInt64.ofNat (HEADER_BYTES + NONCE_BYTES + 4)
  let mut h := IV
  h := h.set! 0 (h[0]! ^^^ (0x01010000 ||| UInt64.ofNat p.hashOutput))
  h := h.set! 6 (h[6]! ^^^ u64FromLeBytes BLAKE2B_PERSONALIZATION_PREFIX)
  h := h.set! 7 (h[7]! ^^^ (UInt64.ofNat p.n ||| UInt64.ofNat p.k <<< 32))
  let mut block := List.replicate BLOCKBYTES 0
  let mut filled := 0
  let mut compressed : UInt64 := 0
  for part in [input, nonce] do
    let mut part := part
    while !part.isEmpty do
      -- Keep the tail in `block`: BLAKE2b compresses a block as
      -- non-final only once more input follows it.
      if filled = BLOCKBYTES then
        compressed := compressed + UInt64.ofNat BLOCKBYTES
        h := compressPrefixBlock h block compressed
        filled := 0
      let take := min part.length (BLOCKBYTES - filled)
      block ← copyFromSlice? block filled (part.take take)
      filled := filled + take
      part := part.drop take
  return {
    h := h
    m0 := u64FromLeBytes (block.take 8)
    m1Low := UInt64.ofNat (u32FromLeBytes ((block.drop 8).take 4))
    count := count }

/-- `Midstate::compress` (lines 231–267) for one lane (`L = u64`): `digest` with the BLAKE2b
    digest of block index `block` written over its 64 bytes. `compress_portable` calls it with
    one block and one digest, as its `debug_assert_eq!`s require. -/
def Midstate.compress (self : Midstate) (block : ℕ) (digest : List ℕ) : List ℕ := Id.run do
  let zero : UInt64 := 0
  let m0 := self.m0
  let m1 := self.m1Low ||| UInt64.ofNat block <<< 32
  let word := fun i => match i with
    | 0 => m0
    | 1 => m1
    | _ => zero
  let mut v := Array.replicate 16 zero
  for i in [0:8] do
    v := v.set! i self.h[i]!
    v := v.set! (8 + i) IV[i]!
  v := v.set! 12 (IV[4]! ^^^ self.count)
  -- Final-block flag.
  v := v.set! 14 (~~~IV[6]!)
  v := rounds v word
  let mut digest := digest
  for i in [0:8] do
    let word := self.h[i]! ^^^ (v[i]! ^^^ v[i + 8]!)
    digest := digest.take (8 * i) ++ u64ToLeBytes word ++ digest.drop (8 * i + 8)
  return digest

/-- `Midstate::compress_portable` (lines 269–277): `compress` for each block and its digest. -/
def Midstate.compressPortable (self : Midstate) (blocks : List ℕ) (out : List (List ℕ)) :
    List (List ℕ) :=
  (blocks.zip out).map fun (block, digest) => self.compress block digest

end LeafHash

open LeafHash

/-- `LeafHasher` (lines 336–340), with the portable kernel. -/
structure LeafHasher where
  midstate : Midstate
  hashLen : ℕ

/-- `LeafHasher::new` (lines 344–346) and `with_kernel` (lines 351–365), with the portable
    kernel, which every CPU supports; `none` unless `input ‖ nonce` is 140 bytes. -/
def LeafHasher.new? (p : Params) (input nonce : List ℕ) : Option LeafHasher := do
  let midstate ← Midstate.new? p input nonce
  return { midstate, hashLen := p.hashOutput }

/-- `LeafHasher::hash` (lines 369–396) with the portable kernel, of one lane: the digest of
    each block index, its bytes past the digest length zero; `none` where the Rust panics.

`digest[self.hash_len..]` cannot panic: `hash_len` is `hash_output`, at most `512 / 8 = 64`. -/
def LeafHasher.hash? (self : LeafHasher) (blocks : List ℕ) (out : List (List ℕ)) :
    Option (List (List ℕ)) := do
  guard (blocks.length = out.length)
  let lanes := 1
  let whole := blocks.length / lanes * lanes
  let (blocks, tailBlocks) := (blocks.take whole, blocks.drop whole)
  let (out, tailOut) := (out.take whole, out.drop whole)
  let out := self.midstate.compressPortable blocks out
  let tailOut := self.midstate.compressPortable tailBlocks tailOut
  -- The kernels write all eight state words; keep the documented zero
  -- bytes past the digest length.
  return (out ++ tailOut).map fun digest =>
    digest.take self.hashLen ++ List.replicate (digest.length - self.hashLen) 0

end Equihash.Verifier
