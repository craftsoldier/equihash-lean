/-
# BLAKE2b (§5.4.1.2)

`BLAKE2b-ℓ(p, x)`: unkeyed BLAKE2b in sequential mode, `ℓ/8` output bytes, personalization `p`,
input `x`, as ANWW2013 defines it.
-/
module

public import Equihash.Spec

@[expose] public section

namespace Equihash.Spec.Blake2b

/-- A 64-bit word. -/
abbrev Word := BitVec 64

/-- `IV` (ANWW2013, Appendix A.1). -/
def iv : Vector Word 8 :=
  #v[0x6a09e667f3bcc908#64, 0xbb67ae8584caa73b#64, 0x3c6ef372fe94f82b#64, 0xa54ff53a5f1d36f1#64,
     0x510e527fade682d1#64, 0x9b05688c2b3e6c1f#64, 0x1f83d9abfb41bd6b#64, 0x5be0cd19137e2179#64]

/-- `σ₀ … σ₉` (ANWW2013, Table 5). -/
def sigma : Vector (Vector (Fin 16) 16) 10 :=
  #v[#v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
     #v[14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
     #v[11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
     #v[7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
     #v[9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
     #v[2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
     #v[12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
     #v[13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
     #v[6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
     #v[10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]

/-- `G` (ANWW2013, §2.4) on words `a`, `b`, `c`, `d` of `v`, with message words `x` and `y`.

**Not stated in the specification.** `+` is addition modulo `2^64` (RFC 7693, §3.1); `≫` is
rotation to the right (ANWW2013, §2.2: "four 64-bit word rotations"). -/
def G (v : Vector Word 16) (a b c d : Fin 16) (x y : Word) : Vector Word 16 :=
  let va := v[a] + v[b] + x
  let vd := (v[d] ^^^ va).rotateRight 32
  let vc := v[c] + vd
  let vb := (v[b] ^^^ vc).rotateRight 24
  let va := va + vb + y
  let vd := (vd ^^^ va).rotateRight 16
  let vc := vc + vd
  let vb := (vb ^^^ vc).rotateRight 63
  (((v.set a va).set b vb).set c vc).set d vd

/-- Round `r` (ANWW2013, Appendix A.1): `G₀ … G₃` on the columns, then `G₄ … G₇` on the
diagonals, `Gᵢ` taking message words `m[σ_r(2i)]` and `m[σ_r(2i+1)]`.

**Not stated in the specification.** Rounds 10 and 11 use `σ_{r mod 10}` (RFC 7693, §3.2;
the BLAKE submission, §2.1.2). -/
def round (m : Vector Word 16) (r : ℕ) (v : Vector Word 16) : Vector Word 16 :=
  let s := sigma[r % 10]'(Nat.mod_lt _ (by decide))
  let v := G v 0 4 8 12 m[s[0]] m[s[1]]
  let v := G v 1 5 9 13 m[s[2]] m[s[3]]
  let v := G v 2 6 10 14 m[s[4]] m[s[5]]
  let v := G v 3 7 11 15 m[s[6]] m[s[7]]
  let v := G v 0 5 10 15 m[s[8]] m[s[9]]
  let v := G v 1 6 11 12 m[s[10]] m[s[11]]
  let v := G v 2 7 8 13 m[s[12]] m[s[13]]
  G v 3 4 9 14 m[s[14]] m[s[15]]

/-- `compress(h, m, t)` (ANWW2013, Appendix A.1): `t` counts the data bytes so far, `last` sets
the finalization flag `f₀` (§2.3); twelve rounds (§2.1).

**Not stated in the specification.** `f₁ = 0` in sequential mode: RFC 7693, §3.2, inverts only
`v₁₄`. -/
def compress (h : Vector Word 8) (m : Vector Word 16) (t : ℕ) (last : Bool) : Vector Word 8 :=
  let f₀ : Word := if last then BitVec.allOnes 64 else 0
  let v : Vector Word 16 := h ++ #v[iv[0], iv[1], iv[2], iv[3],
    BitVec.ofNat 64 t ^^^ iv[4], BitVec.ofNat 64 (t / 2 ^ 64) ^^^ iv[5], f₀ ^^^ iv[6], iv[7]]
  let v := (List.range 12).foldl (fun v r => round m r v) v
  Vector.ofFn fun i : Fin 8 => h[i] ^^^ v[i.val] ^^^ v[i.val + 8]

/-- Word `i` of a byte sequence, little-endian (ANWW2013, Appendix A), zero past its end. -/
def word (bs : List Byte) (i : ℕ) : Word :=
  (List.range 8).foldr (fun j w => (w <<< 8) ||| (bs.getD (8 * i + j) 0).setWidth 64) 0

/-- The parameter block `P` (ANWW2013, §2.8, Table 1), as bytes: the digest length, key length
`0`, fanout `1` and depth `1` ("set to … 1 only in sequential mode"), then the leaf length, node
offset, node depth, inner length and reserved bytes, all zero, the salt, and the
personalization at bytes 48–63.

**Not stated in the specification.** The salt is zero: §5.4.1.2 does not mention one, and
ANWW2013 §2.8 says it is "set to all-NULL by default". -/
def paramBlock (len : ℕ) (p : List.Vector Byte 16) : List Byte :=
  [BitVec.ofNat 8 len, 0, 1, 1] ++ List.replicate 44 0 ++ p.toList

/-- Block `i` of the input: its 128 bytes, zero-padded (ANWW2013, §2.3), as 16 words. -/
def block (x : List Byte) (i : ℕ) : Vector Word 16 :=
  Vector.ofFn fun j : Fin 16 => word ((x.drop (128 * i)).take 128) j

/-- The final state: `h₀ = IV ⊕ P`, then `compress` on each block (ANWW2013, Appendix A.1), the
counter `ℓᵢ` being the data bytes in blocks `0 … i`, the last block flagged final (§2.3).

**Not stated in the specification.** An empty input is one block of zeros (RFC 7693, §3.3);
ANWW2013's `N = ⌈ℓ/128⌉` would compress nothing. -/
def finalState (len : ℕ) (p : List.Vector Byte 16) (x : List Byte) : Vector Word 8 :=
  let n := max 1 ((x.length + 127) / 128)
  let h₀ := Vector.ofFn fun i : Fin 8 => iv[i] ^^^ word (paramBlock len p) i
  (List.range n).foldl (fun h i => compress h (block x i) (min (128 * (i + 1)) x.length)
    (i + 1 == n)) h₀

/-- `BLAKE2b-ℓ(p, x)` (§5.4.1.2), `len = ℓ/8` bytes.

**Not stated in the specification.** The output is the first `len` bytes of the final state,
little-endian (RFC 7693, §3.3); ANWW2013 returns the whole state. -/
def blake2b (len : ℕ) (hlen : len ≤ 64) (p : List.Vector Byte 16) (x : List Byte) :
    List.Vector Byte len :=
  let h := finalState len p x
  ⟨List.ofFn fun k : Fin len => (h[k.val / 8]'(by omega) >>> (8 * (k.val % 8))).setWidth 8,
    by simp⟩

/-- `BLAKE2b-ℓ(p, x)` as the specification's hash function. -/
def hashFn : HashFn := fun p x => blake2b p.len p.len_le p.personal x

end Equihash.Spec.Blake2b
