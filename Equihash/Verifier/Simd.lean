/-
The `core::arch` intrinsics the SIMD leaf-hash kernels use (`src/leaf_hash/x86_64.rs`,
`src/leaf_hash/aarch64.rs`), as their vendors define them: each `_mm256_*` intrinsic by the
"Operation" pseudocode of its entry in the Intel Intrinsics Guide, each `v*q_*` intrinsic by
the instruction it compiles to (named in its doc comment), as the Arm Architecture Reference
Manual for A-profile architecture defines it.

A vector is its 64-bit words, least significant first: word `w` holds bits `64w .. 64w + 63`.
The kernels load, store, add and xor 64-bit elements; the byte and 32-bit views the shuffles use
are read out of the words. `vreinterpretq_*` changes only the view, so it is the identity.
-/
module

public import Equihash.Verifier.Std

@[expose] public section

namespace Equihash.Verifier

/-- Bits `8k .. 8k + 7` of a vector whose word `w` is `word w`. -/
def vecByte (word : ℕ → UInt64) (k : ℕ) : UInt64 :=
  (word (k / 8) >>> UInt64.ofNat (8 * (k % 8))) &&& 0xff

/-- Bits `32k .. 32k + 31` of a vector whose word `w` is `word w`. -/
def vecDword (word : ℕ → UInt64) (k : ℕ) : UInt64 :=
  (word (k / 2) >>> UInt64.ofNat (32 * (k % 2))) &&& 0xffffffff

/-- Word `w` of a vector whose byte `k` is `byte k`. -/
def wordOfBytes (byte : ℕ → UInt64) (w : ℕ) : UInt64 :=
  byte (8 * w) ||| byte (8 * w + 1) <<< 8 ||| byte (8 * w + 2) <<< 16 |||
    byte (8 * w + 3) <<< 24 ||| byte (8 * w + 4) <<< 32 ||| byte (8 * w + 5) <<< 40 |||
    byte (8 * w + 6) <<< 48 ||| byte (8 * w + 7) <<< 56

/-! ## `core::arch::x86_64` -/

namespace X86_64

/-- `__m256i`: 256 bits, as four words, `w0` the least significant. -/
structure M256i where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
deriving Inhabited

/-- Word `w` of the 256 bits. -/
def M256i.word (a : M256i) : ℕ → UInt64
  | 0 => a.w0
  | 1 => a.w1
  | 2 => a.w2
  | 3 => a.w3
  | _ => 0

/-- The 256 bits whose word `w` is `f w`. -/
def M256i.ofWords (f : ℕ → UInt64) : M256i := ⟨f 0, f 1, f 2, f 3⟩

/-- `_mm256_set1_epi64x(a)`: `a` in each 64-bit element. -/
def mm256Set1Epi64x (a : UInt64) : M256i := .ofWords fun _ => a

/-- `_mm256_loadu_si256(p)`: the 256 bits at `p`, here a `[u64; 4]`. -/
def mm256LoaduSi256 (p : Array UInt64) : M256i := .ofWords fun w => p[w]!

/-- `_mm256_storeu_si256(p, a)`: `a` written to the 256 bits at `p`, here a `[u64; 4]`, which
    it fills. -/
def mm256StoreuSi256 (a : M256i) : Array UInt64 := #[a.w0, a.w1, a.w2, a.w3]

/-- `_mm256_add_epi64(a, b)`: each 64-bit element the sum of `a`'s and `b`'s. -/
def mm256AddEpi64 (a b : M256i) : M256i := .ofWords fun w => a.word w + b.word w

/-- `_mm256_xor_si256(a, b)`: bitwise xor. -/
def mm256XorSi256 (a b : M256i) : M256i := .ofWords fun w => a.word w ^^^ b.word w

/-- `_mm256_or_si256(a, b)`: bitwise or. -/
def mm256OrSi256 (a b : M256i) : M256i := .ofWords fun w => a.word w ||| b.word w

/-- `_mm256_srli_epi64::<IMM8>(a)`: each 64-bit element shifted right by `IMM8` bits, zero when
    `IMM8` exceeds 63. -/
def mm256SrliEpi64 (imm8 : ℕ) (a : M256i) : M256i :=
  .ofWords fun w => if imm8 > 63 then 0 else a.word w >>> UInt64.ofNat imm8

/-- `_mm256_setr_epi8(e0, …, e31)`: byte `k` is `e_k`, here the `k`-th entry of `e`. -/
def mm256SetrEpi8 (e : List ℕ) : M256i := .ofWords (wordOfBytes fun k => UInt64.ofNat (e.getD k 0))

/-- `_mm256_shuffle_epi8(a, b)`: within each 128-bit lane, byte `j` of the result is zero when
    bit 7 of byte `j` of `b` is set, and otherwise byte `b[j] & 0x0F` of `a`'s lane. -/
def mm256ShuffleEpi8 (a b : M256i) : M256i := .ofWords (wordOfBytes fun k =>
  let sel := vecByte b.word k
  if sel &&& 0x80 = 0 then vecByte a.word (16 * (k / 16) + (sel &&& 0x0f).toNat) else 0)

/-- `_mm256_shuffle_epi32::<IMM8>(a)`: within each 128-bit lane, 32-bit element `j` of the
    result is element `(IMM8 >> 2j) & 3` of `a`'s lane. -/
def mm256ShuffleEpi32 (imm8 : ℕ) (a : M256i) : M256i := .ofWords fun w =>
  let sel := fun j => vecDword a.word (4 * (w / 2) + (imm8 >>> (2 * j)) % 4)
  sel (2 * (w % 2)) ||| sel (2 * (w % 2) + 1) <<< 32

end X86_64

/-! ## `core::arch::aarch64` -/

namespace Aarch64

/-- `uint64x2_t`: 128 bits, as two words, `w0` the least significant. `uint8x16_t` and
    `uint32x4_t` are the same bits viewed as bytes or as 32-bit elements, so they are this type
    too. -/
structure Uint64x2 where
  w0 : UInt64
  w1 : UInt64
deriving Inhabited

/-- Word `w` of the 128 bits. -/
def Uint64x2.word (a : Uint64x2) : ℕ → UInt64
  | 0 => a.w0
  | 1 => a.w1
  | _ => 0

/-- The 128 bits whose word `w` is `f w`. -/
def Uint64x2.ofWords (f : ℕ → UInt64) : Uint64x2 := ⟨f 0, f 1⟩

/-- `vdupq_n_u64(a)` (DUP): `a` in each 64-bit element. -/
def vdupqNU64 (a : UInt64) : Uint64x2 := .ofWords fun _ => a

/-- `vld1q_u64(p)` (LD1): the two words at `p`, here `words[at..].as_ptr()`. -/
def vld1qU64 (words : Array UInt64) («at» : ℕ) : Uint64x2 := .ofWords fun w => words[«at» + w]!

/-- `vst1q_u64(p, a)` (ST1): `a`'s two words written at `p`, here `words[at..].as_mut_ptr()`. -/
def vst1qU64 (words : Array UInt64) («at» : ℕ) (a : Uint64x2) : Array UInt64 :=
  (words.set! «at» a.w0).set! («at» + 1) a.w1

/-- `vaddq_u64(a, b)` (ADD): each 64-bit element the sum of `a`'s and `b`'s. -/
def vaddqU64 (a b : Uint64x2) : Uint64x2 := .ofWords fun w => a.word w + b.word w

/-- `veorq_u64(a, b)` (EOR): bitwise xor. -/
def veorqU64 (a b : Uint64x2) : Uint64x2 := .ofWords fun w => a.word w ^^^ b.word w

/-- `vreinterpretq_u32_u64`: the same bits. -/
def vreinterpretqU32U64 (a : Uint64x2) : Uint64x2 := a

/-- `vreinterpretq_u64_u32`: the same bits. -/
def vreinterpretqU64U32 (a : Uint64x2) : Uint64x2 := a

/-- `vreinterpretq_u8_u64`: the same bits. -/
def vreinterpretqU8U64 (a : Uint64x2) : Uint64x2 := a

/-- `vreinterpretq_u64_u8`: the same bits. -/
def vreinterpretqU64U8 (a : Uint64x2) : Uint64x2 := a

/-- `vrev64q_u32(a)` (REV64): the two 32-bit elements of each 64-bit element swapped. -/
def vrev64qU32 (a : Uint64x2) : Uint64x2 :=
  .ofWords fun w => vecDword a.word (2 * w + 1) ||| vecDword a.word (2 * w) <<< 32

/-- `vld1q_u8(p)` (LD1): the 16 bytes at `p`, here a `[u8; 16]`. -/
def vld1qU8 (p : List ℕ) : Uint64x2 := .ofWords (wordOfBytes fun k => UInt64.ofNat (p.getD k 0))

/-- `vqtbl1q_u8(t, idx)` (TBL): byte `j` of the result is byte `idx[j]` of `t`, or zero when
    `idx[j]` is 16 or more. -/
def vqtbl1qU8 (t idx : Uint64x2) : Uint64x2 := .ofWords (wordOfBytes fun k =>
  let sel := vecByte idx.word k
  if sel < 16 then vecByte t.word sel.toNat else 0)

/-- `vsriq_n_u64::<N>(a, b)` (SRI): each 64-bit element of `b` shifted right by `N` bits and
    inserted into `a`'s element, whose top `N` bits stay. -/
def vsriqNU64 (n : ℕ) (a b : Uint64x2) : Uint64x2 := .ofWords fun w =>
  (a.word w &&& ~~~UInt64.ofNat (2 ^ (64 - n) - 1)) ||| (b.word w >>> UInt64.ofNat n)

/-- `vxarq_u64::<N>(a, b)` (XAR, the SHA3 extension): each 64-bit element of `a ^ b` rotated
    right by `N` bits. -/
def vxarqU64 (n : ℕ) (a b : Uint64x2) : Uint64x2 :=
  .ofWords fun w => rotateRight (a.word w ^^^ b.word w) (UInt64.ofNat n)

end Aarch64

end Equihash.Verifier
