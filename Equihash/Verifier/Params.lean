/-
`src/params.rs`: the Equihash parameters `n` and `k`, and the sizes derived from them.
-/
module

public import Equihash.Verifier.Std

@[expose] public section

namespace Equihash.Verifier

/-- `Params` (`src/params.rs`, lines 2–5). `Params::new` builds it only for parameters it
    accepts, so `n` is never zero below.

`n` and `k` are `u32`s in Rust and naturals here, which agree below `2^32`, the only values
Rust can pass: no `u32` arithmetic on them overflows there, since `k + 1 ≤ n` (`k < n` is
checked first) and `indices_per_hash_output() * n` is at most 512. -/
structure Params where
  n : ℕ
  k : ℕ

namespace Params

/-- `Params::new` (lines 9–30): the parameters, when they are ones the verifier supports. -/
def new? (n k : ℕ) : Option Params :=
  if n % 8 = 0 ∧ k ≥ 3 ∧ k < n ∧ n % (k + 1) = 0 ∧ n ≤ 512 ∧
      8 ≤ n / (k + 1) ∧ n / (k + 1) ≤ 24 then
    some { n, k }
  else none

/-- `equihash 0.3.0`'s and 0.3.1's `Params::new` (`src/params.rs`, lines 9–20 in both): the
    first four of the checks `new?` makes, without `n ≤ 512` and the bounds on `n / (k + 1)`. -/
def newUnbounded? (n k : ℕ) : Option Params :=
  if n % 8 = 0 ∧ k ≥ 3 ∧ k < n ∧ n % (k + 1) = 0 then
    some { n, k }
  else none

variable (self : Params)

/-- `indices_per_hash_output` (lines 45–47): `512 / self.n`. -/
def indicesPerHashOutput : ℕ := 512 / self.n

/-- `hash_output` (lines 48–50): `(self.indices_per_hash_output() * self.n / 8) as u8`. -/
def hashOutput : ℕ := self.indicesPerHashOutput * self.n / 8 % 256

/-- `collision_bit_length` (lines 51–53): `(self.n / (self.k + 1)) as usize`. -/
def collisionBitLength : ℕ := self.n / (self.k + 1)

/-- `collision_byte_length` (lines 54–56): `self.collision_bit_length().div_ceil(8)`. -/
def collisionByteLength : ℕ := divCeil self.collisionBitLength 8

/-- `hash_length` (lines 57–59): `((self.k as usize) + 1) * self.collision_byte_length()`. -/
def hashLength : ℕ := (self.k + 1) * self.collisionByteLength

/-- `solution_indices` (lines 32–34): `1usize.checked_shl(self.k)`. -/
def solutionIndices? : Option ℕ := checkedShl? 1 self.k

/-- `solution_bytes` (lines 37–44):
    `self.solution_indices()?.checked_mul(self.collision_bit_length() + 1)? / 8`. -/
def solutionBytes? : Option ℕ := do
  let indices ← self.solutionIndices?
  let bits ← checkedMul? indices (self.collisionBitLength + 1)
  return bits / 8

end Params

end Equihash.Verifier
