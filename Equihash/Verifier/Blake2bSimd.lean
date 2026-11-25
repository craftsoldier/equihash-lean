/-
`blake2b_simd 1.0.4` (`rust/blake2b_simd-1.0.4/`), the parts the verifiers call: `Params` and
its `hash_length` and `personal` setters, `State` with `update` and `finalize`, `Hash::as_bytes`,
and the two single-stream compression loops, portable (`src/portable.rs`) and AVX2
(`src/avx2.rs`). `Implementation::detect` (`src/guts.rs`, lines 28–44) picks the AVX2 loop when
the CPU has AVX2, and otherwise the portable one, which an SSE4.1 CPU also runs (lines 96–116);
here the implementation is a parameter.

`arrayref`'s macros (`arrayref 0.3.9`, `src/lib.rs`, lines 57–255) and the AVX2 loop's raw block
read (`src/avx2.rs`, line 471) give references to parts of arrays; here they are those parts.
Arrays are indexed only by constants and by offsets below their lengths, so `a[i]!`, `a.set! i`
and `List.take`/`drop` stand for indexing and slicing that cannot panic.
-/
module

public import Equihash.Verifier.LeafHash

@[expose] public section

namespace Equihash.Verifier.Blake2b

open X86_64

/-! ## Constants (`src/lib.rs`) -/

/-- `OUTBYTES` (line 68): the largest output length, in bytes. -/
def outBytes : ℕ := 64

/-- `PERSONALBYTES` (line 74): the length of a personalization, in bytes. -/
def personalBytes : ℕ := 16

/-- `IV` (lines 79–88). -/
def IV : Array UInt64 := #[
  0x6A09E667F3BCC908, 0xBB67AE8584CAA73B, 0x3C6EF372FE94F82B, 0xA54FF53A5F1D36F1,
  0x510E527FADE682D1, 0x9B05688C2B3E6C1F, 0x1F83D9ABFB41BD6B, 0x5BE0CD19137E2179]

/-- `SIGMA` (lines 90–103): twelve rows, one per round. -/
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

/-! ## `src/guts.rs` -/

/-- `Implementation` (lines 16–25), as `compress1_loop` (lines 96–116) uses it: the AVX2 loop,
    or the portable one. -/
inductive Implementation where
  | portable
  | avx2

/-- `count_low` (lines 204–206): the low 64 bits of the 128-bit count. -/
def countLow (count : ℕ) : UInt64 := UInt64.ofNat count

/-- `count_high` (lines 208–210): the high 64 bits of the 128-bit count. -/
def countHigh (count : ℕ) : UInt64 := UInt64.ofNat (count / 2 ^ 64)

/-- `flag_word` (lines 217–223): all ones, or zero. -/
def flagWord (flag : Bool) : UInt64 := if flag then ~~~0 else 0

/-- `final_block` (lines 232–250), for `Stride::Serial`: the 128-byte block at `offset`, or the
    bytes left there copied to the front of a zero buffer, and how many bytes of input it holds. -/
def finalBlock (input : List ℕ) (offset : ℕ) : List ℕ × ℕ :=
  let offsetSlice := input.drop (min offset input.length)
  if offsetSlice.length ≥ BLOCKBYTES then (offsetSlice.take BLOCKBYTES, BLOCKBYTES)
  else (offsetSlice ++ List.replicate (BLOCKBYTES - offsetSlice.length) 0, offsetSlice.length)

/-- `compress1_loop` (`src/portable.rs`, lines 119–168, and `src/avx2.rs`, lines 437–490, the
    same loop around each file's `compress_block`), for `Stride::Serial` and `LastNode::No`:
    every block of `input` compressed into `words`, the count advanced by each block's input
    bytes, the last block flagged when `finalize`. -/
def compress1Loop
    (compressBlock : List ℕ → Array UInt64 → ℕ → UInt64 → UInt64 → Array UInt64)
    (input : List ℕ) (words : Array UInt64) (count : ℕ) (finalize : Bool) : Array UInt64 :=
  let finOffset := (input.length - 1) - (input.length - 1) % BLOCKBYTES
  let (finBlock, finLen) := finalBlock input finOffset
  let step := fun (s : Array UInt64 × ℕ) (j : ℕ) =>
    let offset := BLOCKBYTES * j
    let (block, countDelta, lastBlock) :=
      if offset = finOffset then (finBlock, finLen, flagWord finalize)
      else ((input.drop offset).take BLOCKBYTES, BLOCKBYTES, flagWord false)
    let count := (s.2 + countDelta) % 2 ^ 128
    (compressBlock block s.1 count lastBlock (flagWord false), count)
  ((List.range (finOffset / BLOCKBYTES + 1)).foldl step (words, count)).1

/-! ## `src/portable.rs` -/

namespace Portable

/-- `g` (lines 15–24). -/
def g (v : Array UInt64) (a b c d : ℕ) (x y : UInt64) : Array UInt64 :=
  let v := v.set! a (v[a]! + v[b]! + x)
  let v := v.set! d (rotateRight (v[d]! ^^^ v[a]!) 32)
  let v := v.set! c (v[c]! + v[d]!)
  let v := v.set! b (rotateRight (v[b]! ^^^ v[c]!) 24)
  let v := v.set! a (v[a]! + v[b]! + y)
  let v := v.set! d (rotateRight (v[d]! ^^^ v[a]!) 16)
  let v := v.set! c (v[c]! + v[d]!)
  v.set! b (rotateRight (v[b]! ^^^ v[c]!) 63)

/-- `round` (lines 29–44). -/
def round (r : ℕ) (m : Array UInt64) (v : Array UInt64) : Array UInt64 :=
  let s := SIGMA[r]!
  let v := g v 0 4 8 12 m[s[0]!]! m[s[1]!]!
  let v := g v 1 5 9 13 m[s[2]!]! m[s[3]!]!
  let v := g v 2 6 10 14 m[s[4]!]! m[s[5]!]!
  let v := g v 3 7 11 15 m[s[6]!]! m[s[7]!]!
  let v := g v 0 5 10 15 m[s[8]!]! m[s[9]!]!
  let v := g v 1 6 11 12 m[s[10]!]! m[s[11]!]!
  let v := g v 2 7 8 13 m[s[12]!]! m[s[13]!]!
  g v 3 4 9 14 m[s[14]!]! m[s[15]!]!

/-- `compress_block` (lines 47–117): the state words, `IV` and the flags, twelve rounds
    (`round(0, …)` to `round(11, …)`, lines 96–107), then `words[i] ^= v[i] ^ v[i + 8]`. -/
def compressBlock (block : List ℕ) (words : Array UInt64) (count : ℕ)
    (lastBlock lastNode : UInt64) : Array UInt64 :=
  let v := words ++ #[IV[0]!, IV[1]!, IV[2]!, IV[3]!, IV[4]! ^^^ countLow count,
    IV[5]! ^^^ countHigh count, IV[6]! ^^^ lastBlock, IV[7]! ^^^ lastNode]
  let m := (List.range 16).toArray.map fun i => u64FromLeBytes ((block.drop (8 * i)).take 8)
  let v := (List.range 12).foldl (fun v r => round r m v) v
  (List.range 8).toArray.map fun i => words[i]! ^^^ v[i]! ^^^ v[i + 8]!

end Portable

/-! ## `src/avx2.rs` -/

namespace Avx2

/-- `rot32`, `rot24`, `rot16`, `rot63` (lines 87–104): two shifts and an or. -/
def rot (n : ℕ) (x : M256i) : M256i := mm256OrSi256 (mm256SrliEpi64 n x) (mm256SlliEpi64 (64 - n) x)

/-- The state's four rows `a`, `b`, `c`, `d`, which `g1`, `g2`, `diagonalize` and
    `undiagonalize` take as `&mut __m256i` and update. -/
abbrev Rows := M256i × M256i × M256i × M256i

/-- `g1` (lines 107–117). -/
def g1 (s : Rows) (m : M256i) : Rows :=
  let (a, b, c, d) := s
  let a := mm256AddEpi64 (mm256AddEpi64 a m) b
  let d := rot 32 (mm256XorSi256 d a)
  let c := mm256AddEpi64 c d
  let b := rot 24 (mm256XorSi256 b c)
  (a, b, c, d)

/-- `g2` (lines 120–130). -/
def g2 (s : Rows) (m : M256i) : Rows :=
  let (a, b, c, d) := s
  let a := mm256AddEpi64 (mm256AddEpi64 a m) b
  let d := rot 16 (mm256XorSi256 d a)
  let c := mm256AddEpi64 c d
  let b := rot 63 (mm256XorSi256 b c)
  (a, b, c, d)

/-- `_MM_SHUFFLE!(z, y, x, w)` (lines 71–75). -/
def mmShuffle (z y x w : ℕ) : ℕ := z <<< 6 ||| y <<< 4 ||| x <<< 2 ||| w

/-- `diagonalize` (lines 136–142): `a`, `c` and `d` rotated by one, three and two words, `b`
    left in place. -/
def diagonalize (s : Rows) : Rows :=
  let (a, b, c, d) := s
  (mm256Permute4x64Epi64 (mmShuffle 2 1 0 3) a, b, mm256Permute4x64Epi64 (mmShuffle 0 3 2 1) c,
    mm256Permute4x64Epi64 (mmShuffle 1 0 3 2) d)

/-- `undiagonalize` (lines 145–151). -/
def undiagonalize (s : Rows) : Rows :=
  let (a, b, c, d) := s
  (mm256Permute4x64Epi64 (mmShuffle 0 3 2 1) a, b, mm256Permute4x64Epi64 (mmShuffle 2 1 0 3) c,
    mm256Permute4x64Epi64 (mmShuffle 1 0 3 2) d)

/-- One of the shuffles that build `t0` and `t1` from the message vectors `m0 … m7`:
    `_mm256_unpacklo_epi64(mX, mY)`, `_mm256_unpackhi_epi64(mX, mY)`,
    `_mm256_alignr_epi8(mX, mY, 8)`, `_mm256_blend_epi32(mX, mY, 0x33)`, or
    `_mm256_shuffle_epi32(mX, _MM_SHUFFLE!(1, 0, 3, 2))`. -/
inductive Shuffle where
  | lo (x y : ℕ)
  | hi (x y : ℕ)
  | alignr (x y : ℕ)
  | blend (x y : ℕ)
  | swap (x : ℕ)
deriving Inhabited

/-- The vector a `Shuffle` makes from the message vectors `m`. -/
def Shuffle.apply (m : Array M256i) : Shuffle → M256i
  | .lo x y => mm256UnpackloEpi64 m[x]! m[y]!
  | .hi x y => mm256UnpackhiEpi64 m[x]! m[y]!
  | .alignr x y => mm256AlignrEpi8 8 m[x]! m[y]!
  | .blend x y => mm256BlendEpi32 0x33 m[x]! m[y]!
  | .swap x => mm256ShuffleEpi32 (mmShuffle 1 0 3 2) m[x]!

open Shuffle in
/-- The rounds of `compress_block` (lines 186–424), each written out there as four steps: for
    column `g1`, column `g2`, diagonal `g1` and diagonal `g2`, the two shuffles giving `t0` and
    `t1`, then `b0 = _mm256_blend_epi32(t0, t1, 0xF0)`. Row `r` is lines `186 + 20r` to
    `204 + 20r`. -/
def rounds : List (List (Shuffle × Shuffle)) := [
  [(lo 0 1, lo 2 3), (hi 0 1, hi 2 3), (lo 7 4, lo 5 6), (hi 7 4, hi 5 6)],
  [(lo 7 2, hi 4 6), (lo 5 4, alignr 3 7), (hi 2 0, blend 5 0), (alignr 6 1, blend 3 1)],
  [(alignr 6 5, hi 2 7), (lo 4 0, blend 6 1), (alignr 5 4, hi 1 3), (lo 2 7, blend 0 3)],
  [(hi 3 1, hi 6 5), (hi 4 0, lo 6 7), (alignr 1 7, swap 2), (lo 4 3, lo 5 0)],
  [(hi 4 2, lo 1 5), (blend 3 0, blend 7 2), (alignr 7 1, alignr 3 5), (hi 6 0, lo 6 4)],
  [(lo 1 3, lo 0 4), (lo 6 5, hi 5 1), (alignr 2 0, hi 3 7), (hi 4 6, alignr 7 2)],
  [(blend 0 6, lo 7 2), (hi 2 7, alignr 5 6), (lo 4 0, blend 4 3), (hi 5 3, swap 1)],
  [(hi 6 3, blend 1 6), (alignr 7 5, hi 0 4), (blend 2 1, alignr 4 7), (lo 5 0, lo 2 3)],
  [(lo 3 7, alignr 0 5), (hi 7 4, alignr 4 1), (lo 5 6, hi 6 0), (alignr 1 2, alignr 2 3)],
  [(lo 5 4, hi 3 0), (lo 1 2, blend 2 3), (hi 6 7, hi 4 1), (blend 5 0, lo 7 6)],
  [(lo 0 1, lo 2 3), (hi 0 1, hi 2 3), (lo 7 4, lo 5 6), (hi 7 4, hi 5 6)],
  [(lo 7 2, hi 4 6), (lo 5 4, alignr 3 7), (hi 2 0, blend 5 0), (alignr 6 1, blend 3 1)]]

/-- `b0`, from the shuffles giving `t0` and `t1`. -/
def b0 (m : Array M256i) (t : Shuffle × Shuffle) : M256i :=
  mm256BlendEpi32 0xF0 (t.1.apply m) (t.2.apply m)

/-- One round: `g1`, `g2`, `diagonalize`, `g1`, `g2`, `undiagonalize`, each `g` given its `b0`. -/
def round (m : Array M256i) (r : List (Shuffle × Shuffle)) (s : Rows) : Rows :=
  undiagonalize (g2 (g1 (diagonalize (g2 (g1 s (b0 m r[0]!)) (b0 m r[1]!))) (b0 m r[2]!))
    (b0 m r[3]!))

/-- `compress_block` (lines 154–434): the state words, `IV` and the flags as four rows `a`, `b`,
    `c`, `d`; the eight 16-byte message chunks, each broadcast to both 128-bit lanes; the twelve
    rounds; then `a ^ c ^ iv0` and `b ^ d ^ iv1` stored back. -/
def compressBlock (block : List ℕ) (words : Array UInt64) (count : ℕ)
    (lastBlock lastNode : UInt64) : Array UInt64 :=
  let a := mm256LoaduSi256 (words.extract 0 4)
  let b := mm256LoaduSi256 (words.extract 4 8)
  let c := mm256LoaduSi256 (IV.extract 0 4)
  let flags := mm256SetrEpi64x (countLow count) (countHigh count) lastBlock lastNode
  let d := mm256XorSi256 (mm256LoaduSi256 (IV.extract 4 8)) flags
  let m := (List.range 8).toArray.map fun k =>
    mm256Broadcastsi128Si256 (mmLoaduSi128 ((block.drop (16 * k)).take 16))
  let (a', b', c', d') := rounds.foldl (fun s r => round m r s) (a, b, c, d)
  let a' := mm256XorSi256 (mm256XorSi256 a' c') a
  let b' := mm256XorSi256 (mm256XorSi256 b' d') b
  mm256StoreuSi256 a' ++ mm256StoreuSi256 b'

end Avx2

/-- The `compress_block` each implementation's loop calls. -/
def Implementation.compressBlock :
    Implementation → List ℕ → Array UInt64 → ℕ → UInt64 → UInt64 → Array UInt64
  | .avx2 => Avx2.compressBlock
  | .portable => Portable.compressBlock

/-- `Implementation::compress1_loop` (`src/guts.rs`, lines 96–116): the AVX2 loop on an AVX2
    implementation, the portable loop otherwise. -/
def Implementation.compress1Loop (impl : Implementation) :
    List ℕ → Array UInt64 → ℕ → Bool → Array UInt64 :=
  Blake2b.compress1Loop impl.compressBlock

end Equihash.Verifier.Blake2b
