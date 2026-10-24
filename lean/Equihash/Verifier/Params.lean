/-
`src/params.rs`: the Equihash parameters `n` and `k`, and the sizes derived from them.
-/
module

public import Equihash.Verifier.Std

@[expose] public section

namespace Equihash.Verifier

/-- `Params` (`src/params.rs`, lines 2–5). `Params::new` builds it only for parameters it
    accepts, so `n` is never zero below. -/
structure Params where
  n : ℕ
  k : ℕ

namespace Params

variable (self : Params)

/-- `indices_per_hash_output` (lines 45–47): `512 / self.n`. -/
def indicesPerHashOutput : ℕ := 512 / self.n

/-- `hash_output` (lines 48–50): `(self.indices_per_hash_output() * self.n / 8) as u8`. -/
def hashOutput : ℕ := self.indicesPerHashOutput * self.n / 8 % 256

/-- `collision_bit_length` (lines 51–53): `(self.n / (self.k + 1)) as usize`. -/
def collisionBitLength : ℕ := self.n / (self.k + 1)

/-- `collision_byte_length` (lines 54–56): `self.collision_bit_length().div_ceil(8)`. -/
def collisionByteLength : ℕ := divCeil self.collisionBitLength 8

end Params

end Equihash.Verifier
