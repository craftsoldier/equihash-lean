/-
The decoder: `indices_from_minimal` reads a minimally encoded solution back into its `2^k`
indices, each the next `n/(k+1) + 1` bits of the solution, most significant first.
-/
module

public import Equihash.Proofs.SinglePass

@[expose] public section

namespace Equihash.Verifier

open Equihash Equihash.Spec

/-- One pass of `indices_from_minimal`'s `while let` loop (`src/minimal.rs`, lines 157–160):
    read the next index, or stop. -/
def readPass (_ : Unit) (s : Cursor × List ℕ) : Option (ForInStep (Cursor × List ℕ)) :=
  have csr := s.1
  have ret := s.2
  match readU32Be? csr with
  | some (i, csr') => pure (.yield (csr', ret ++ [i]))
  | none => pure (.done (csr, ret))

/-- `indices_from_minimal`, as its loop body. -/
theorem indicesFromMinimal?_eq (p : Params) (minimal : List ℕ) :
    indicesFromMinimal? p minimal = (do
      let sb ← p.solutionBytes?
      if minimal.length ≠ sb then none else do
        guard (divCeil (p.collisionBitLength + 1) 8 ≤ 4)
        let out ← expandArray? minimal (p.collisionBitLength + 1)
          (4 - divCeil (p.collisionBitLength + 1) 8)
        let s ← forIn Lean.Loop.mk (({ inner := out, pos := 0 } : Cursor), ([] : List ℕ)) readPass
        pure s.2) := by
  rfl

/-- **The read loop.** From position `4j` of `4n` bytes, the loop reads the remaining
    `n - j` big-endian words, then stops at the end. -/
theorem forIn_readPass (out : List ℕ) (n : ℕ) (hlen : out.length = 4 * n) :
    ∀ j ≤ n, ∀ ret,
      forIn Lean.Loop.mk (({ inner := out, pos := 4 * j } : Cursor), ret) readPass =
        some (({ inner := out, pos := 4 * n } : Cursor),
          ret ++ (List.range' j (n - j)).map fun t =>
            u32FromBeBytes ((out.drop (4 * t)).take 4)) := by
  intro j hj
  obtain ⟨m, hm⟩ : ∃ m, m = n - j := ⟨_, rfl⟩
  induction m generalizing j with
  | zero =>
    intro ret
    obtain rfl : j = n := by omega
    rw [loop_unfold]
    simp [readPass, readU32Be?, Cursor.readExact?, hlen]
  | succ m ih =>
    intro ret
    rw [loop_unfold]
    have hread : readU32Be? { inner := out, pos := 4 * j } =
        some (u32FromBeBytes ((out.drop (4 * j)).take 4),
          { inner := out, pos := 4 * (j + 1) }) := by
      simp only [readU32Be?, Cursor.readExact?, hlen, List.length_drop]
      rw [Nat.min_eq_left (by omega)]
      split_ifs with h4
      · omega
      · simp [Nat.mul_succ]
    simp only [readPass, hread, Option.pure_def, Option.bind_eq_bind, Option.bind_some]
    rw [ih (j + 1) (by omega) (by omega), show n - j = (n - (j + 1)) + 1 by omega,
      List.range'_succ]
    simp

/-- **`indices_from_minimal`**: a solution of the right length decodes to its `2^k` digits of
    `n/(k+1) + 1` bits each, read most significant bit first; any other length is rejected. -/
theorem indicesFromMinimal?_spec {rp : Params} {p : ZakuraParams} (h : rp.Is p)
    (minimal : List ℕ) (hb : Bytes minimal) :
    indicesFromMinimal? rp minimal = rp.solutionBytes?.bind fun sb =>
      if minimal.length = sb then
        some ((List.range (2 ^ p.k)).map
          (digitVal (p.digitBits + 1) (bitsOfBytes (bytesOf minimal))))
      else none := by
  have hc8 : 8 ≤ p.digitBits := p.digit_ge
  have hc24 : p.digitBits ≤ 24 := p.digit_le
  rw [indicesFromMinimal?_eq, Params.collisionBitLength_eq h]
  rcases hsb : rp.solutionBytes? with _ | sb
  · rfl
  simp only [Option.bind_eq_bind, Option.bind_some, ne_eq, ite_not]
  by_cases hl : minimal.length = sb
  swap
  · simp [hl]
  simp only [hl, ↓reduceIte]
  -- The solution has `2^k·(c + 1)` bits, a whole number of bytes since `k ≥ 3`.
  have hsb' : sb = 2 ^ p.k * (p.digitBits + 1) / 8 := by
    simp only [Params.solutionBytes?, Params.solutionIndices?_eq h, Option.bind_eq_bind,
      Option.bind_some, Params.collisionBitLength_eq h, checkedMul?] at hsb
    split_ifs at hsb
    · simpa using hsb.symm
    · simp at hsb
  have hk8 : 8 ∣ 2 ^ p.k := by
    have := p.k_ge
    exact ⟨2 ^ (p.k - 3), by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← Nat.pow_add, show 3 + (p.k - 3) = p.k by omega]⟩
  have h8 : 8 * minimal.length = 2 ^ p.k * (p.digitBits + 1) := by
    obtain ⟨r, hr⟩ := hk8
    rw [hl, hsb', hr, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
  have hdc : divCeil (p.digitBits + 1) 8 ≤ 4 := by rw [divCeil_eq _ _ (by norm_num)]; omega
  simp only [hdc, guard_true, Option.pure_def, Option.bind_some]
  -- Expansion: each digit into four big-endian bytes.
  obtain ⟨out, hout, hol, hall⟩ := expandArray?_spec minimal hb (p.digitBits + 1)
    (4 - divCeil (p.digitBits + 1) 8) (by omega) (by omega) ⟨2 ^ p.k, by rw [h8, Nat.mul_comm]⟩
  have hw : divCeil (p.digitBits + 1) 8 + (4 - divCeil (p.digitBits + 1) 8) = 4 := by omega
  have hn : 8 * minimal.length / (p.digitBits + 1) = 2 ^ p.k := by
    rw [h8, Nat.mul_div_cancel _ (by omega)]
  rw [hw, hn] at hall
  rw [hw, hn, Nat.mul_comm] at hol
  have hread := forIn_readPass out (2 ^ p.k) hol 0 (Nat.zero_le _) []
  rw [Nat.mul_zero] at hread
  rw [hout, Option.bind_some, hread, Option.bind_some]
  simp only [List.nil_append, Nat.sub_zero, Option.some.injEq]
  rw [← List.range_eq_range']
  apply List.map_congr_left
  intro t ht
  rw [List.mem_range] at ht
  -- Word `t` is digit `t` of the solution's bits.
  have hB : (bitsOfBytes (bytesOf minimal)).length = 8 * minimal.length := by
    simp [length_bitsOfBytes]
  have hV : prefixVal minimal minimal.length = bitsVal (bitsOfBytes (bytesOf minimal)) := by
    rw [bitsVal_bitsOfBytes, map_toNat_bytesOf hb, prefixVal, List.take_of_length_le le_rfl]
  have hfit : (t + 1) * (p.digitBits + 1) ≤ 8 * minimal.length := by
    rw [h8]; exact Nat.mul_le_mul_right _ ht
  have hD : digit (p.digitBits + 1) minimal.length (prefixVal minimal minimal.length) t <
      256 ^ 4 := by
    simp only [digit]
    have := Nat.mod_lt (bitsVal (bitsOfBytes (bytesOf minimal)) /
      2 ^ (8 * minimal.length - (t + 1) * (p.digitBits + 1))) (Nat.two_pow_pos (p.digitBits + 1))
    have h25 : 2 ^ (p.digitBits + 1) ≤ 256 ^ 4 := by
      rw [show (256 : ℕ) ^ 4 = 2 ^ 32 by norm_num]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hV]; omega
  have hchunk : (out.drop (4 * t)).take 4 =
      chunk 4 (digit (p.digitBits + 1) minimal.length (prefixVal minimal minimal.length) t) := by
    apply List.ext_getElem?
    intro x
    rw [List.getElem?_take, List.getElem?_drop]
    by_cases hx : x < 4
    · simp only [hx, ↓reduceIte]
      rw [Nat.mul_comm, hall t ht x hx]
      simp [chunk, hx]
    · simp [hx, chunk]
  rw [hchunk, show u32FromBeBytes = beNat from rfl, beNat_chunk 4 _ hD, hV,
    digit_eq_digitVal _ _ _ _ hB hfit]

end Equihash.Verifier
