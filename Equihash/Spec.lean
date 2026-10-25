/-
# Zcash Equihash Specification

* Parameters, valid solutions and their encoding (§7.7.1).
* The hash values a solution is made of (§5.4.1.11).
* Bytes and bits (§5.1, §5.2).
-/
module

public import Mathlib.Data.List.Lex
public import Mathlib.Data.Vector.Basic

@[expose] public section

namespace Equihash

/-! ## Bytes, bits and BLAKE2b -/

/-- A byte. -/
abbrev Byte := BitVec 8

/-- The parameters of `BLAKE2b-ℓ(p, x)` (§5.4.1.2): the output length in bytes, `ℓ / 8`,
    and the personalization `p`. -/
structure HashParams where
  len : ℕ
  personal : List Byte

/-- `BLAKE2b-ℓ(p, x)`: `ℓ / 8` output bytes for any input bytes `x`. -/
abbrev HashFn := (p : HashParams) → List Byte → List.Vector Byte p.len

end Equihash

namespace Equihash.Spec

/-- Bit sequences. The specification indexes them from 1. -/
abbrev Bits := List Bool

/-- `I2LEOSP_ℓ(x)` (§5.1): the `⌈ℓ/8⌉` bytes representing `x` in little-endian order. -/
def I2LEOSP (ℓ x : ℕ) : List Byte :=
  (List.range ((ℓ + 7) / 8)).map fun j => BitVec.ofNat 8 (x / 256 ^ j)

/-- `I2BEBSP_ℓ(x)` (§5.1): the `ℓ` bits representing `x` in big-endian order. -/
def I2BEBSP (ℓ x : ℕ) : Bits :=
  (List.range ℓ).map fun j => x.testBit (ℓ - 1 - j)

/-- The bits of a byte sequence, each byte's most significant bit first.

**Not stated in the specification.** §5.4.1.11 takes bits of the BLAKE2b output `T`, a byte
sequence, without saying in which order. This is the order §5.2 uses ("the bits ordered
from most significant to least significant"). -/
def bitsOfBytes (bs : List Byte) : Bits :=
  bs.flatMap fun b => (List.range 8).map fun j => b.getMsbD j

/-! ## Parameters (§7.7.1) -/

/-- > An instance of the Equihash algorithm is parameterized by positive integers `n` and
    > `k`, such that `n` is a multiple of `k + 1`. We assume `k ≥ 3`.

**Not stated in the specification.** §5.4.1.11 only makes sense when `m = ⌊512/n⌋ ≥ 1`, so
`n ≤ 512`, and when `BLAKE2b-(n·m)` outputs whole bytes, so `8 ∣ n·m`. -/
structure Params where
  n : ℕ
  k : ℕ
  n_pos : 0 < n
  k_ge : 3 ≤ k
  n_dvd : (k + 1) ∣ n
  n_le : n ≤ 512
  bytes_dvd : 8 ∣ n * (512 / n)

namespace Params

variable (p : Params)

/-- `n / (k + 1)`: the number of bits each level of a solution checks. -/
def digitBits : ℕ := p.n / (p.k + 1)

/-- > In Equihash, `N = 2^(n/(k+1)+1)` -/
def N : ℕ := 2 ^ (p.digitBits + 1)

/-- > `m = ⌊512/n⌋` (§5.4.1.11) -/
def m : ℕ := 512 / p.n

end Params

/-! ## The Equihash generator (§5.4.1.11) -/

/-- The ASCII bytes of `"ZcashPoW"`. -/
def zcashPoW : List Byte := [0x5A, 0x63, 0x61, 0x73, 0x68, 0x50, 0x6F, 0x57]

/-- > Let `powtag := 64-bit "ZcashPoW" ‖ 32-bit n ‖ 32-bit k`.

The 32-bit integers are little-endian (§5.1, and the note at the end of §7.7.1). -/
def powtag (p : Params) : List Byte := zcashPoW ++ I2LEOSP 32 p.n ++ I2LEOSP 32 p.k

/-- > Let `powcount(g) := 32-bit g`. -/
def powcount (g : ℕ) : List Byte := I2LEOSP 32 g

/-- `BLAKE2b-(n·m)` personalized by `powtag`: `n·m / 8` output bytes. -/
def genHashParams (p : Params) : HashParams where
  len := p.n * p.m / 8
  personal := powtag p

/-- > Let `EquihashGen_{n,k}(S, i) := T_{h+1 .. h+n}`, where
    > * `m = ⌊512/n⌋`;
    > * `h = (i − 1 mod m) · n`;
    > * `T = BLAKE2b-(n·m)(powtag, S ‖ powcount(⌊(i−1)/m⌋))`.
    >
    > Indices of bits in `T` are 1-based. -/
def equihashGen (H : HashFn) (p : Params) (S : List Byte) (i : ℕ) : Bits :=
  let h := ((i - 1) % p.m) * p.n
  let T := bitsOfBytes (H (genHashParams p) (S ++ powcount ((i - 1) / p.m))).toList
  (T.drop h).take p.n

/-! ## Valid solutions (§7.7.1) -/

/-- > For `i ∈ {1 .. N}`, let `X_i = EquihashGen_{n,k}(powheader, i)`. -/
def X (H : HashFn) (p : Params) (powheader : List Byte) (i : ℕ) : Bits :=
  equihashGen H p powheader i

/-- `a ⊕ b`: bitwise exclusive or. -/
def xor (a b : Bits) : Bits := List.zipWith (· ^^ ·) a b

/-- `⊕_j x_j`: the exclusive or of `n`-bit strings. -/
def xorAll (n : ℕ) (xs : List Bits) : Bits := xs.foldl xor (List.replicate n false)

/-- `x` has (at least) `z` leading zeros. -/
def HasLeadingZeros (z : ℕ) (x : Bits) : Prop := ∀ b ∈ x.take z, b = false

/-- `i_{a .. b}`: the elements of `i` at positions `a` to `b`, counting from 1. -/
def range (i : List ℕ) (a b : ℕ) : List ℕ := (i.drop (a - 1)).take (b + 1 - a)

/-- > **Generalized Birthday condition** `⊕_{j=1}^{2^k} X_{i_j} = 0`. -/
def GeneralizedBirthday (H : HashFn) (p : Params) (powheader : List Byte) (i : List ℕ) :
    Prop :=
  xorAll p.n (i.map (X H p powheader)) = List.replicate p.n false

/-- > **Algorithm Binding conditions**
    > * For all `r ∈ {1 .. k−1}`, for all `w ∈ {0 .. 2^(k−r) − 1}`:
    >   `⊕_{j=1}^{2^r} X_{i_{w·2^r + j}}` has `n·r/(k+1)` leading zeros; and -/
def CollisionCondition (H : HashFn) (p : Params) (powheader : List Byte) (i : List ℕ) :
    Prop :=
  ∀ r, 1 ≤ r → r ≤ p.k - 1 → ∀ w < 2 ^ (p.k - r),
    HasLeadingZeros (p.n * r / (p.k + 1))
      (xorAll p.n ((range i (w * 2 ^ r + 1) (w * 2 ^ r + 2 ^ r)).map (X H p powheader)))

/-- > * For all `r ∈ {1 .. k}`, for all `w ∈ {0 .. 2^(k−r) − 1}`:
    >   `i_{w·2^r + 1 .. w·2^r + 2^(r−1)} < i_{w·2^r + 2^(r−1) + 1 .. w·2^r + 2^r}`
    >   lexicographically. -/
def OrderingCondition (p : Params) (i : List ℕ) : Prop :=
  ∀ r, 1 ≤ r → r ≤ p.k → ∀ w < 2 ^ (p.k - r),
    List.Lex (· < ·)
      (range i (w * 2 ^ r + 1) (w * 2 ^ r + 2 ^ (r - 1)))
      (range i (w * 2 ^ r + 2 ^ (r - 1) + 1) (w * 2 ^ r + 2 ^ r))

/-- > A valid Equihash solution is then a sequence `i : {1 .. N}^(2^k)` that satisfies the
    > following conditions: [the Generalized Birthday and Algorithm Binding conditions]

`powheader` is the block header followed by the nonce. -/
structure ValidSolution (H : HashFn) (p : Params) (powheader : List Byte) (i : List ℕ) :
    Prop where
  length : i.length = 2 ^ p.k
  bounds : ∀ j ∈ i, 1 ≤ j ∧ j ≤ p.N
  birthday : GeneralizedBirthday H p powheader i
  collision : CollisionCondition H p powheader i
  ordering : OrderingCondition p i

/-! ## The solution encoding (§7.7.1) -/

/-- > An Equihash solution with `n = 200` and `k = 9` is encoded in the `solution` field of a
    > block header as follows:
    > `I2BEBSP_21(i_1 − 1) ‖ I2BEBSP_21(i_2 − 1) ‖ ⋯ ‖ I2BEBSP_21(i_512 − 1)`
    >
    > Recall from §5.2 that the bits in the above diagram are ordered from most to least
    > significant in each byte.

`solution` encodes `i` when its bits, each byte's most significant bit first, are those of
the indices in turn.

**Not stated in the specification.** The encoding for other parameters: each index in
`n/(k+1) + 1` bits, which is 21 for `n = 200, k = 9`. -/
def EncodesSolution (p : Params) (solution : List Byte) (i : List ℕ) : Prop :=
  bitsOfBytes solution = i.flatMap fun j => I2BEBSP (p.digitBits + 1) (j - 1)

end Equihash.Spec
