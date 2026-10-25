/-
`src/minimal.rs`: expanding a byte array into fixed-width digits, and decoding a minimally
encoded solution into its indices.
-/
module

public import Equihash.Verifier.Params

@[expose] public section

namespace Equihash.Verifier

/-- `expanded_len` (`src/minimal.rs`, lines 58–60):
    `8 * (bit_len.div_ceil(8) + byte_pad) * vin_len / bit_len`. -/
def expandedLen (vinLen bitLen bytePad : ℕ) : ℕ :=
  8 * (divCeil bitLen 8 + bytePad) * vinLen / bitLen

/-- `expand_array_into` (lines 64–107): writes each `bit_len`-bit digit of `vin`, big-endian,
    into `out_width` bytes of `vout`, the first `byte_pad` of them zero. `none` where the Rust
    panics.

`vout[j + x] = v` writes in place, panicking out of bounds, as `set?` does; no write is out of
bounds (`expandArrayInto?_eq_fold`). The right shifts are by at most 31 bits at every call site,
where `out_width` is at most 4 and `acc_bits` is below 8 after the subtraction, so a `u32` shift
and a natural-number shift agree. -/
def expandArrayInto? (vin : List ℕ) (bitLen bytePad : ℕ) (vout : List ℕ) : Option (List ℕ) := do
  guard (bitLen ≥ 8)
  guard (32 ≥ 7 + bitLen)
  let outWidth := divCeil bitLen 8 + bytePad
  guard (vout.length = expandedLen vin.length bitLen bytePad)
  -- Shortcut for parameters where expansion is a no-op.
  if vout.length = vin.length then
    return vin
  -- The padding bytes of each output element are never written below.
  let mut vout := vout.map fun _ => 0
  let bitLenMask := 2 ^ bitLen - 1
  -- The `accBits` least significant bits of `accValue` are a big-endian bit sequence.
  let mut accBits := 0
  let mut accValue := 0
  let mut j := 0
  for b in vin do
    -- `acc_value << 8` on a `u32` drops the bits shifted past 32.
    accValue := (accValue <<< 8) % 2 ^ 32 ||| b
    accBits := accBits + 8
    -- When there are `bit_len` or more bits, write the next output element.
    if accBits ≥ bitLen then
      accBits := accBits - bitLen
      for x in [bytePad:outWidth] do
        vout ← set? vout (j + x)
          ((accValue >>> (accBits + 8 * (outWidth - x - 1)) &&&
            (bitLenMask >>> (8 * (outWidth - x - 1)) &&& 0xFF)) % 256)
      j := j + outWidth
  return vout

/-- `expand_array` (lines 50–54): a new vector of `expanded_len` zero bytes, expanded into. -/
def expandArray? (vin : List ℕ) (bitLen bytePad : ℕ) : Option (List ℕ) :=
  let vout := List.replicate (expandedLen vin.length bitLen bytePad) 0
  expandArrayInto? vin bitLen bytePad vout

/-- `equihash 0.3.0`'s `expand_array` (`src/minimal.rs`, lines 50–93): the shortcut and loop of
    `expand_array_into`, into a vector of `out_len` zero bytes it allocates itself, so without
    `expand_array_into`'s check of the output's length and its zeroing, which that vector meets.

`vout[j + x] = v` writes in place, panicking out of bounds, as `set?` does; this function is
`expandArray?` (`expandArrayAlloc?_eq`), which writes nothing out of bounds, and whose right
shifts agree with `u32`'s at both of its call sites, `Node::new` and `indices_from_minimal`. -/
def expandArrayAlloc? (vin : List ℕ) (bitLen bytePad : ℕ) : Option (List ℕ) := do
  guard (bitLen ≥ 8)
  guard (32 ≥ 7 + bitLen)
  let outWidth := divCeil bitLen 8 + bytePad
  let outLen := 8 * outWidth * vin.length / bitLen
  -- Shortcut for parameters where expansion is a no-op.
  if outLen = vin.length then
    return vin
  let mut vout := List.replicate outLen 0
  let bitLenMask := 2 ^ bitLen - 1
  -- The `accBits` least significant bits of `accValue` are a big-endian bit sequence.
  let mut accBits := 0
  let mut accValue := 0
  let mut j := 0
  for b in vin do
    -- `acc_value << 8` on a `u32` drops the bits shifted past 32.
    accValue := (accValue <<< 8) % 2 ^ 32 ||| b
    accBits := accBits + 8
    -- When there are `bit_len` or more bits, write the next output element.
    if accBits ≥ bitLen then
      accBits := accBits - bitLen
      for x in [bytePad:outWidth] do
        vout ← set? vout (j + x)
          ((accValue >>> (accBits + 8 * (outWidth - x - 1)) &&&
            (bitLenMask >>> (8 * (outWidth - x - 1)) &&& 0xFF)) % 256)
      j := j + outWidth
  return vout

/-- `read_u32_be` (lines 135–139): the next four bytes as a big-endian `u32`, and the advanced
    cursor; `none` for `Err(UnexpectedEof)`. -/
def readU32Be? (csr : Cursor) : Option (ℕ × Cursor) := do
  let (n, csr) ← csr.readExact? 4
  return (u32FromBeBytes n, csr)

/-- `indices_from_minimal` (lines 142–163): the indices a minimally encoded solution holds,
    each expanded to four big-endian bytes and read back; `some none` for `None` (a solution of
    the wrong length, or parameters whose length overflows), and `none` where the Rust panics.

`len_indices` only sizes the vector's capacity, which does not change the result. In a release
build `u32::BITS as usize * minimal.len()` wraps, and the capacity stays below `2^61` four-byte
elements (`c_bit_len + 1 ≥ 8` once `expand_array` passes its checks), under `isize::MAX` bytes,
so `Vec::with_capacity` cannot panic; an allocation that fails aborts, outside the model. -/
def indicesFromMinimal? (p : Params) (minimal : List ℕ) : Option (Option (List ℕ)) := do
  let cBitLen := p.collisionBitLength
  let some solutionBytes := p.solutionBytes? | return none
  if minimal.length ≠ solutionBytes then
    return none
  guard (divCeil (cBitLen + 1) 8 ≤ 4)
  let bytePad := 4 - divCeil (cBitLen + 1) 8
  let mut csr : Cursor := { inner := ← expandArray? minimal (cBitLen + 1) bytePad, pos := 0 }
  let mut ret := []
  -- `while let Ok(i) = read_u32_be(&mut csr)`
  repeat
    match readU32Be? csr with
    | some (i, csr') =>
      csr := csr'
      ret := ret ++ [i]
    | none => break
  return some ret

/-- `equihash 0.3.0`'s `indices_from_minimal` (`src/minimal.rs`, lines 127–148): as
    `indicesFromMinimal?`, except that the length it expects is computed without overflow
    checks. In a release build `1 << p.k` shifts by `p.k` modulo `usize::BITS`, and the product
    wraps modulo `2^64`. `some none` for `None` (a solution of the wrong length), and `none` where
    the Rust panics.

`len_indices` only sizes the vector's capacity, as in `indicesFromMinimal?`. -/
def indicesFromMinimalWrapping? (p : Params) (minimal : List ℕ) : Option (Option (List ℕ)) := do
  let cBitLen := p.collisionBitLength
  -- Division is exact because k >= 3.
  if minimal.length ≠ (1 <<< (p.k % USIZE_BITS)) * (cBitLen + 1) % 2 ^ USIZE_BITS / 8 then
    return none
  guard (divCeil (cBitLen + 1) 8 ≤ 4)
  let bytePad := 4 - divCeil (cBitLen + 1) 8
  let mut csr : Cursor := { inner := ← expandArrayAlloc? minimal (cBitLen + 1) bytePad, pos := 0 }
  let mut ret := []
  -- `while let Ok(i) = read_u32_be(&mut csr)`
  repeat
    match readU32Be? csr with
    | some (i, csr') =>
      csr := csr'
      ret := ret ++ [i]
    | none => break
  return some ret

end Equihash.Verifier
