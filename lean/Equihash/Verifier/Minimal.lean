/-
`src/minimal.rs`: expanding a byte array into fixed-width digits.
-/
module

public import Equihash.Verifier.Std

@[expose] public section

namespace Equihash.Verifier

/-- `expanded_len` (`src/minimal.rs`, lines 58–60):
    `8 * (bit_len.div_ceil(8) + byte_pad) * vin_len / bit_len`. -/
def expandedLen (vinLen bitLen bytePad : ℕ) : ℕ :=
  8 * (divCeil bitLen 8 + bytePad) * vinLen / bitLen

/-- `expand_array_into` (lines 64–107): writes each `bit_len`-bit digit of `vin`, big-endian,
    into `out_width` bytes of `vout`, the first `byte_pad` of them zero. `none` where the Rust
    panics.

`vout[j + x] = v` writes in place; here it is `vout.set (j + x) v`. The proof of
`expandArrayInto?` shows every such write is in bounds. -/
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
        vout := vout.set (j + x)
          ((accValue >>> (accBits + 8 * (outWidth - x - 1)) &&&
            (bitLenMask >>> (8 * (outWidth - x - 1)) &&& 0xFF)) % 256)
      j := j + outWidth
  return vout

/-- `expand_array` (lines 50–54): a new vector of `expanded_len` zero bytes, expanded into. -/
def expandArray? (vin : List ℕ) (bitLen bytePad : ℕ) : Option (List ℕ) :=
  let vout := List.replicate (expandedLen vin.length bitLen bytePad) 0
  expandArrayInto? vin bitLen bytePad vout

end Equihash.Verifier
