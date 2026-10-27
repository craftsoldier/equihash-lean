/-
`src/leaf_hash.rs`: BLAKE2b of each leaf's block, from the midstate of the 140-byte prefix
`input ‖ nonce` that every leaf shares. One compression program, `Midstate::compress`, over a
type of `Lanes`: the portable kernel runs it on `u64`, one lane; the AVX2 kernel
(`src/leaf_hash/x86_64.rs`) on `__m256i`, four lanes; the NEON kernels
(`src/leaf_hash/aarch64.rs`) on a pair of `uint64x2_t`, four lanes. `Kernel::detect` picks one
the running CPU supports; here the kernel is a parameter.

The state arrays are Rust's `[u64; 8]`, `[u64; 16]` and `[u64; 4]`, indexed only by constants
and loop counters below those lengths, so their indexing cannot panic; `a[i]!` and `a.set! i`
stand for it.
-/
module

public import Equihash.Verifier.Lib
public import Equihash.Verifier.Params
public import Equihash.Verifier.Simd

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

/-- `MAX_LANES` (line 61): the widest lane count any backend uses. -/
def MAX_LANES : ℕ := 4

/-- `Lanes` (lines 67–82): `LANES` independent BLAKE2b state words. `load` reads the first
    `LANES` words of a `[u64; MAX_LANES]`, `store` writes them; `xor_rotrN` is
    `(self ^ other).rotate_right(N)` on each lane. -/
class Lanes (L : Type) where
  LANES : ℕ
  splat : UInt64 → L
  load : Array UInt64 → L
  store : L → Array UInt64 → Array UInt64
  add : L → L → L
  xor : L → L → L
  xorRotr32 : L → L → L
  xorRotr24 : L → L → L
  xorRotr16 : L → L → L
  xorRotr63 : L → L → L

/-- `impl Lanes for u64` (lines 84–123): one lane; `add` is `wrapping_add`. -/
instance : Lanes UInt64 where
  LANES := 1
  splat x := x
  load words := words[0]!
  store self words := words.set! 0 self
  add self other := self + other
  xor self other := self ^^^ other
  xorRotr32 self other := rotateRight (self ^^^ other) 32
  xorRotr24 self other := rotateRight (self ^^^ other) 24
  xorRotr16 self other := rotateRight (self ^^^ other) 16
  xorRotr63 self other := rotateRight (self ^^^ other) 63

open Lanes in
/-- `g` (lines 126–137). -/
def g {L : Type} [Lanes L] [Inhabited L] (v : Array L) (a b c d : ℕ) (x y : L) : Array L :=
  let v := v.set! a (add (add v[a]! v[b]!) x)
  let v := v.set! d (xorRotr32 v[d]! v[a]!)
  let v := v.set! c (add v[c]! v[d]!)
  let v := v.set! b (xorRotr24 v[b]! v[c]!)
  let v := v.set! a (add (add v[a]! v[b]!) y)
  let v := v.set! d (xorRotr16 v[d]! v[a]!)
  let v := v.set! c (add v[c]! v[d]!)
  v.set! b (xorRotr63 v[b]! v[c]!)

/-- `rounds!(v, word; 0 1 2 3 4 5 6 7 8 9 10 11)` (lines 141–153): the macro writes out one
    round per row of `SIGMA`, here a loop over the rows. -/
def rounds {L : Type} [Lanes L] [Inhabited L] (v : Array L) (word : ℕ → L) : Array L :=
  Id.run do
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
    prefix bytes left for the final block; `some none` (`None`) unless `input ‖ nonce` is
    140 bytes.

`checked_add` of two slice lengths cannot overflow, so it is a plain `+` here. The closing
`debug_assert_eq!(filled, TAIL_BYTES)` is not evaluated in a release build; it holds for every
140-byte prefix anyway (`Midstate.new?_spec`). -/
def Midstate.new? (p : Params) (input nonce : List ℕ) : Option (Option Midstate) := do
  if input.length + nonce.length ≠ HEADER_BYTES + NONCE_BYTES then
    return none
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
  return some {
    h := h
    m0 := u64FromLeBytes (block.take 8)
    m1Low := UInt64.ofNat (u32FromLeBytes ((block.drop 8).take 4))
    count := count }

open Lanes in
/-- `Midstate::compress` (lines 231–267): each digest of `out` with the BLAKE2b digest of the
    block index of `blocks` at its position written over its 64 bytes, one lane per block. The
    callers pass `L::LANES` blocks and digests, as its `debug_assert_eq!`s require; `zip` stops
    at the shorter of each pair it joins. -/
def Midstate.compress {L : Type} [Lanes L] [Inhabited L] (self : Midstate) (blocks : List ℕ)
    (out : List (List ℕ)) : List (List ℕ) := Id.run do
  let mut words : Array UInt64 := Array.replicate MAX_LANES 0
  for (block, j) in blocks.zipIdx do
    words := words.set! j (self.m1Low ||| UInt64.ofNat block <<< 32)
  let zero : L := splat 0
  let m0 : L := splat self.m0
  let m1 : L := load words
  let word := fun i => match i with
    | 0 => m0
    | 1 => m1
    | _ => zero
  let mut v := Array.replicate 16 zero
  for i in [0:8] do
    v := v.set! i (splat self.h[i]!)
    v := v.set! (8 + i) (splat IV[i]!)
  v := v.set! 12 (splat (IV[4]! ^^^ self.count))
  -- Final-block flag.
  v := v.set! 14 (splat (~~~IV[6]!))
  v := rounds v word
  let mut out := out
  for i in [0:8] do
    words := store (xor (splat self.h[i]!) (xor v[i]! v[i + 8]!)) words
    out := (out.zip words.toList).map fun (digest, word) =>
      digest.take (8 * i) ++ u64ToLeBytes word ++ digest.drop (8 * i + 8)
  return out

/-- `Midstate::compress_portable` (lines 269–277): `compress::<u64>` on each block and its
    digest, as one-entry slices; each call returns its one digest. -/
def Midstate.compressPortable (self : Midstate) (blocks : List ℕ) (out : List (List ℕ)) :
    List (List ℕ) :=
  (blocks.zip out).flatMap fun (block, digest) => self.compress (L := UInt64) [block] [digest]

/-! ## `src/leaf_hash/x86_64.rs`: the AVX2 kernel -/

open X86_64

/-- `impl Lanes for __m256i` (`src/leaf_hash/x86_64.rs`, lines 22–76): four lanes. `xor` is
    the implementation's own `xor` (line 42); `0b10_11_00_01` selects, within each 128-bit
    lane, 32-bit elements `1, 0, 3, 2`. -/
instance : Lanes M256i where
  LANES := 4
  splat x := mm256Set1Epi64x x
  load words := mm256LoaduSi256 words
  store self _ := mm256StoreuSi256 self
  add self other := mm256AddEpi64 self other
  xor self other := mm256XorSi256 self other
  xorRotr32 self other := mm256ShuffleEpi32 0b10110001 (mm256XorSi256 self other)
  xorRotr24 self other :=
    let bytes := mm256SetrEpi8 [3, 4, 5, 6, 7, 0, 1, 2, 11, 12, 13, 14, 15, 8, 9, 10,
      3, 4, 5, 6, 7, 0, 1, 2, 11, 12, 13, 14, 15, 8, 9, 10]
    mm256ShuffleEpi8 (mm256XorSi256 self other) bytes
  xorRotr16 self other :=
    let bytes := mm256SetrEpi8 [2, 3, 4, 5, 6, 7, 0, 1, 10, 11, 12, 13, 14, 15, 8, 9,
      2, 3, 4, 5, 6, 7, 0, 1, 10, 11, 12, 13, 14, 15, 8, 9]
    mm256ShuffleEpi8 (mm256XorSi256 self other) bytes
  xorRotr63 self other :=
    let x := mm256XorSi256 self other
    mm256OrSi256 (mm256SrliEpi64 63 x) (mm256AddEpi64 x x)

/-- `compress_avx2` (lines 81–84): `compress::<__m256i>`. `has_avx2` (lines 11–20) asks the
    CPU whether it may run; here the kernel is a parameter (`Kernel`). -/
def compressAvx2 (midstate : Midstate) (blocks : List ℕ) (out : List (List ℕ)) :
    List (List ℕ) :=
  midstate.compress (L := M256i) blocks out

/-! ## `src/leaf_hash/aarch64.rs`: the NEON kernels -/

open Aarch64

/-- `ROTR24` (`src/leaf_hash/aarch64.rs`, line 22). -/
def ROTR24 : List ℕ := [3, 4, 5, 6, 7, 0, 1, 2, 11, 12, 13, 14, 15, 8, 9, 10]

/-- `ROTR16` (line 23). -/
def ROTR16 : List ℕ := [2, 3, 4, 5, 6, 7, 0, 1, 10, 11, 12, 13, 14, 15, 8, 9]

/-- `NeonLanes` (lines 133–151) and `NeonSha3Lanes` (lines 153–159), `sha3` telling them
    apart: `[uint64x2_t; 2]`, two vectors of two lanes each. -/
structure NeonLanes (sha3 : Bool) where
  v0 : Uint64x2
  v1 : Uint64x2
deriving Inhabited

/-- `neon_lanes!`'s `rotr32`: `NeonLanes`'s (lines 135–138) or `NeonSha3Lanes`'s (line 155). -/
def neonRotr32 : Bool → Uint64x2 → Uint64x2 → Uint64x2
  | false, a, b =>
    let x := veorqU64 a b
    vreinterpretqU64U32 (vrev64qU32 (vreinterpretqU32U64 x))
  | true, a, b => vxarqU64 32 a b

/-- `neon_lanes!`'s `rotr24`: `NeonLanes`'s (lines 139–142) or `NeonSha3Lanes`'s (line 156). -/
def neonRotr24 : Bool → Uint64x2 → Uint64x2 → Uint64x2
  | false, a, b =>
    let x := vreinterpretqU8U64 (veorqU64 a b)
    vreinterpretqU64U8 (vqtbl1qU8 x (vld1qU8 ROTR24))
  | true, a, b => vxarqU64 24 a b

/-- `neon_lanes!`'s `rotr16`: `NeonLanes`'s (lines 143–146) or `NeonSha3Lanes`'s (line 157). -/
def neonRotr16 : Bool → Uint64x2 → Uint64x2 → Uint64x2
  | false, a, b =>
    let x := vreinterpretqU8U64 (veorqU64 a b)
    vreinterpretqU64U8 (vqtbl1qU8 x (vld1qU8 ROTR16))
  | true, a, b => vxarqU64 16 a b

/-- `neon_lanes!`'s `rotr63`: `NeonLanes`'s (lines 147–150) or `NeonSha3Lanes`'s (line 158). -/
def neonRotr63 : Bool → Uint64x2 → Uint64x2 → Uint64x2
  | false, a, b =>
    let x := veorqU64 a b
    vsriqNU64 63 (vaddqU64 x x) x
  | true, a, b => vxarqU64 63 a b

/-- `neon_lanes!` (lines 25–131): `impl Lanes` for both types, each operation on both
    vectors; the four rotations are the macro's arguments. -/
instance (sha3 : Bool) : Lanes (NeonLanes sha3) where
  LANES := 4
  splat x := ⟨vdupqNU64 x, vdupqNU64 x⟩
  load words := ⟨vld1qU64 words 0, vld1qU64 words 2⟩
  store self words := vst1qU64 (vst1qU64 words 0 self.v0) 2 self.v1
  add self other := ⟨vaddqU64 self.v0 other.v0, vaddqU64 self.v1 other.v1⟩
  xor self other := ⟨veorqU64 self.v0 other.v0, veorqU64 self.v1 other.v1⟩
  xorRotr32 self other := ⟨neonRotr32 sha3 self.v0 other.v0, neonRotr32 sha3 self.v1 other.v1⟩
  xorRotr24 self other := ⟨neonRotr24 sha3 self.v0 other.v0, neonRotr24 sha3 self.v1 other.v1⟩
  xorRotr16 self other := ⟨neonRotr16 sha3 self.v0 other.v0, neonRotr16 sha3 self.v1 other.v1⟩
  xorRotr63 self other := ⟨neonRotr63 sha3 self.v0 other.v0, neonRotr63 sha3 self.v1 other.v1⟩

/-- `compress_neon` (lines 164–167): `compress::<NeonLanes>`. -/
def compressNeon (midstate : Midstate) (blocks : List ℕ) (out : List (List ℕ)) :
    List (List ℕ) :=
  midstate.compress (L := NeonLanes false) blocks out

/-- `compress_neon_sha3` (lines 173–176): `compress::<NeonSha3Lanes>`. `has_sha3` (lines
    11–20) asks the CPU whether it may run; here the kernel is a parameter (`Kernel`). -/
def compressNeonSha3 (midstate : Midstate) (blocks : List ℕ) (out : List (List ℕ)) :
    List (List ℕ) :=
  midstate.compress (L := NeonLanes true) blocks out

end LeafHash

open LeafHash

/-! ## `src/leaf_hash.rs`: the kernels and the hasher -/

/-- `Kernel` (lines 282–290): a leaf-hashing backend. `Avx2` is compiled on `x86_64`, `Neon`
    and `NeonSha3` on `aarch64` with NEON. -/
inductive Kernel
  | portable
  | avx2
  | neon
  | neonSha3
deriving DecidableEq, Repr

/-- `Kernel::lanes` (lines 324–332). -/
def Kernel.lanes : Kernel → ℕ
  | .portable => 1
  | .avx2 => 4
  | .neon | .neonSha3 => 4

/-- `LeafHasher` (lines 336–340). -/
structure LeafHasher where
  midstate : Midstate
  kernel : Kernel
  hashLen : ℕ

/-- `LeafHasher::with_kernel` (lines 351–365): `some none` (`None`) unless `input ‖ nonce` is
    140 bytes. Its first check, that the running CPU supports `kernel` (`Kernel::supported`,
    lines 306–318, which asks `has_avx2` and `has_sha3`), is not transcribed: `kernel` here
    stands for a kernel the CPU supports. -/
def LeafHasher.withKernel? (p : Params) (input nonce : List ℕ) (kernel : Kernel) :
    Option (Option LeafHasher) := do
  let some midstate ← Midstate.new? p input nonce | return none
  return some { midstate, kernel, hashLen := p.hashOutput }

/-- `LeafHasher::new` (lines 344–346): `with_kernel` with `Kernel::detect()` (lines 320–322),
    the fastest kernel the running CPU supports, here `kernel`. -/
def LeafHasher.new? (p : Params) (input nonce : List ℕ) (kernel : Kernel) :
    Option (Option LeafHasher) :=
  LeafHasher.withKernel? p input nonce kernel

/-- `LeafHasher::hash` (lines 369–396): the digest of each block index, its bytes past the
    digest length zero; `none` where the Rust panics.

`chunks_exact(lanes)` of `whole` entries, a multiple of `lanes`, is `chunks(lanes)`, here
`chunksSucc (lanes - 1)` as `lanes ≥ 1`. `digest[self.hash_len..]` cannot panic: `hash_len`
is `hash_output`, at most `512 / 8 = 64`. -/
def LeafHasher.hash? (self : LeafHasher) (blocks : List ℕ) (out : List (List ℕ)) :
    Option (List (List ℕ)) := do
  guard (blocks.length = out.length)
  let (midstate, kernel) := (self.midstate, self.kernel)
  let lanes := kernel.lanes
  let whole := blocks.length / lanes * lanes
  let (blocks, tailBlocks) := (blocks.take whole, blocks.drop whole)
  let (out, tailOut) := (out.take whole, out.drop whole)
  let out := ((chunksSucc (lanes - 1) blocks).zip (chunksSucc (lanes - 1) out)).flatMap
    fun (blocks, out) =>
      match kernel with
      | .portable => midstate.compressPortable blocks out
      | .avx2 => compressAvx2 midstate blocks out
      | .neon => compressNeon midstate blocks out
      | .neonSha3 => compressNeonSha3 midstate blocks out
  let tailOut := midstate.compressPortable tailBlocks tailOut
  -- The kernels write all eight state words; keep the documented zero
  -- bytes past the digest length.
  return (out ++ tailOut).map fun digest =>
    digest.take self.hashLen ++ List.replicate (digest.length - self.hashLen) 0

end Equihash.Verifier
