/-
The Rust standard library operations the verifier uses, and `corez`'s in-memory `Cursor`.

Rust's fixed-width integers are natural numbers here. Where Rust discards bits on purpose
(`<<` on a `u32`, `as u8`), the code says so with an explicit `%`; where it checks for overflow
(`checked_shl`, `checked_mul`), so does the Lean, for a 64-bit `usize`. Elsewhere no addition or
multiplication overflows for any input shorter than `2^32` bytes.

The model is a release build, as Zcash nodes run: arithmetic that overflows wraps rather than
panicking, and `debug_assert!` is not evaluated. A function that can panic returns `none` for the
panic; one that can also return a Rust `None` returns `Option (Option α)`, `some none` for that
`None`. A function that cannot panic returns Rust's own `Option` (`checkedMul?`,
`Params.solutionBytes?`), or `none` for an `Err` its doc names (`Cursor.readExact?`).
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

/-- `s[i] = v`: `s` with position `i` set to `v`, panicking (`none`) unless `i < s.len()`. -/
def set? {α : Type} (s : List α) (i : ℕ) (v : α) : Option (List α) :=
  if i < s.length then some (s.set i v) else none

/-- `usize::BITS` on the 64-bit targets Zcash nodes run on. -/
def USIZE_BITS : ℕ := 64

/-- `usize::checked_shl`: `self << rhs`, or `None` when `rhs` is at least `usize::BITS`. -/
def checkedShl? (self rhs : ℕ) : Option ℕ :=
  if rhs < USIZE_BITS then some ((self <<< rhs) % 2 ^ USIZE_BITS) else none

/-- `usize::checked_mul`: `self * rhs`, or `None` when it does not fit in a `usize`. -/
def checkedMul? (self rhs : ℕ) : Option ℕ :=
  if self * rhs < 2 ^ USIZE_BITS then some (self * rhs) else none

/-- `Chunks::next` repeated, for chunks of `size + 1` elements: split off the first
    `min(len, size + 1)` elements until none are left. -/
def chunksSucc {α : Type} (size : ℕ) : List α → List (List α)
  | [] => []
  | x :: xs => (x :: xs).take (size + 1) :: chunksSucc size ((x :: xs).drop (size + 1))
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-- `s.chunks(size)`: consecutive runs of `size` elements, the last possibly shorter;
    panicking (`none`) when `size` is zero. -/
def chunks? {α : Type} (s : List α) : ℕ → Option (List (List α))
  | 0 => none
  | size + 1 => some (chunksSucc size s)

/-- `dst[start..][..src.len()].copy_from_slice(src)`: `dst` with `src` written from position
    `start`, panicking (`none`) unless it fits. -/
def copyFromSlice? {α : Type} (dst : List α) (start : ℕ) (src : List α) : Option (List α) :=
  if start + src.length ≤ dst.length then
    some (dst.take start ++ src ++ dst.drop (start + src.length))
  else none

/-- `u32::from_be_bytes`: the number four bytes denote, most significant first. -/
def u32FromBeBytes (bytes : List ℕ) : ℕ := bytes.foldl (fun acc b => 256 * acc + b) 0

/-- `u32::from_le_bytes`: the number four bytes denote, least significant first. -/
def u32FromLeBytes (bytes : List ℕ) : ℕ := bytes.foldr (fun b acc => 256 * acc + b) 0

/-- `u64::from_le_bytes`: the word eight bytes denote, least significant first. -/
def u64FromLeBytes (bytes : List ℕ) : UInt64 :=
  (List.range 8).foldr (fun j w => (w <<< 8) ||| UInt64.ofNat (bytes.getD j 0)) 0

/-- `u64::to_le_bytes`: the eight bytes of `x`, least significant first. -/
def u64ToLeBytes (x : UInt64) : List ℕ :=
  (List.range 8).map fun i => (x >>> UInt64.ofNat (8 * i)).toNat % 256

/-- `u64::rotate_right`. -/
def rotateRight (x n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))

/-- `corez::io::Cursor` (`corez 0.1.1`, `src/io/cursor.rs`, lines 14–17): a buffer and a
    read position. -/
structure Cursor where
  inner : List ℕ
  pos : ℕ

/-- `Cursor::read_exact` (`src/io/cursor.rs`, lines 69–79): the next `len` bytes and the
    advanced cursor, or `none` for `Err(UnexpectedEof)` when fewer remain.

```rust
let start = cmp::min(self.pos, slice.len() as u64) as usize;
let remaining = &slice[start..];
if buf.len() > remaining.len() { return Err(Error::from(ErrorKind::UnexpectedEof)); }
buf.copy_from_slice(&remaining[..buf.len()]);
self.pos += buf.len() as u64;
``` -/
def Cursor.readExact? (self : Cursor) (len : ℕ) : Option (List ℕ × Cursor) :=
  let start := min self.pos self.inner.length
  let remaining := self.inner.drop start
  if len > remaining.length then none
  else some (remaining.take len, { self with pos := self.pos + len })

end Equihash.Verifier
