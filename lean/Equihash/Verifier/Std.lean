/-
The Rust standard library operations the verifier uses.

Rust's fixed-width integers are natural numbers here. No computation in the verifier comes
near `2^32`, so no addition or multiplication overflows; where Rust discards bits on purpose
(`<<` on a `u32`, `as u8`), the code says so with an explicit `%`.
-/
module

public import Mathlib.Data.List.Basic

@[expose] public section

namespace Equihash.Verifier

/-- `usize::div_ceil`:

```rust
let d = self / rhs;
let r = self % rhs;
if r > 0 { d + 1 } else { d }
``` -/
def divCeil (self rhs : ℕ) : ℕ :=
  let d := self / rhs
  let r := self % rhs
  if r > 0 then d + 1 else d

/-- `u32::to_le_bytes`: the four bytes of `x`, least significant first. -/
def u32ToLeBytes (x : ℕ) : List ℕ := [x % 256, x / 256 % 256, x / 256 ^ 2 % 256, x / 256 ^ 3 % 256]

/-- `&s[start..end]`: the elements at positions `start .. end`, panicking (`none`) unless
    `start ≤ end ≤ s.len()`. -/
def slice? {α : Type} (s : List α) (start «end» : ℕ) : Option (List α) :=
  if start ≤ «end» ∧ «end» ≤ s.length then some ((s.drop start).take («end» - start)) else none

end Equihash.Verifier
