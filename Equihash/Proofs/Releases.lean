/-
`is_valid_solution` is correct: on a 140-byte `input ‖ nonce`, it accepts exactly the solution
bytes that encode a §7.7.1-valid solution with no repeated index.
-/
module

public import Equihash.Verifier.Releases
public import Equihash.Proofs.LeafHash

@[expose] public section

namespace Equihash.Verifier

open Equihash Equihash.Spec

/-! ## The encoding -/

theorem length_I2BEBSP (w x : ℕ) : (I2BEBSP w x).length = w := by simp [I2BEBSP]

theorem I2BEBSP_succ (w x : ℕ) : I2BEBSP (w + 1) x = x.testBit w :: I2BEBSP w x := by
  simp only [I2BEBSP, List.range_succ_eq_map, List.map_cons, List.map_map, List.cons.injEq]
  refine ⟨by simp, List.map_congr_left fun j _ => ?_⟩
  simp only [Function.comp, Nat.succ_eq_add_one]
  congr 1
  omega

/-- `I2BEBSP_w(x)`, read back: `x mod 2^w`. -/
theorem bitsVal_I2BEBSP (w x : ℕ) : bitsVal (I2BEBSP w x) = x % 2 ^ w := by
  induction w with
  | zero => simp [I2BEBSP, bitsVal, Nat.mod_one]
  | succ w ih =>
    rw [I2BEBSP_succ, bitsVal_cons, length_I2BEBSP, ih, Nat.toNat_testBit, Nat.pow_succ,
      Nat.mod_mul]
    ring

/-- A bit sequence is `I2BEBSP` of its value. -/
theorem I2BEBSP_bitsVal (b : Bits) : I2BEBSP b.length (bitsVal b) = b :=
  bitsVal_inj (length_I2BEBSP _ _) (by rw [bitsVal_I2BEBSP, Nat.mod_eq_of_lt (bitsVal_lt b)])

/-- `m` chunks of `w` bits, in turn, make up `m·w` bits. -/
theorem flatMap_chunks (w : ℕ) : ∀ (m : ℕ) (B : Bits), B.length = m * w →
    (List.range m).flatMap (fun t => (B.drop (t * w)).take w) = B := by
  intro m
  induction m with
  | zero => intro B hB; simp at hB; simp [hB]
  | succ m ih =>
    intro B hB
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hpre := ih (B.take (m * w)) (by simp [hB, Nat.succ_mul])
    conv_rhs => rw [← List.take_append_drop (m * w) B]
    congr 1
    · rw [← hpre]
      apply List.flatMap_congr
      intro t ht
      rw [List.mem_range] at ht
      have : (t + 1) * w ≤ m * w := Nat.mul_le_mul_right _ ht
      rw [List.drop_take, List.take_take, Nat.min_eq_left (by rw [Nat.succ_mul] at this; omega)]
    · rw [List.take_of_length_le (by simp [hB, Nat.succ_mul])]

/-- Chunk `t` of a concatenation of `w`-bit chunks. -/
theorem chunk_flatMap (w : ℕ) (f : ℕ → Bits) (hf : ∀ x, (f x).length = w) :
    ∀ (l : List ℕ) (t : ℕ) (ht : t < l.length),
      (((l.flatMap f).drop (t * w)).take w) = f l[t] := by
  intro l
  induction l with
  | nil => intro t ht; simp at ht
  | cons x l ih =>
    intro t ht
    rw [List.flatMap_cons]
    rcases t with _ | t
    · simp [List.take_left' (hf x)]
    · rw [Nat.succ_mul, Nat.add_comm, ← List.drop_drop, List.drop_left' (hf x)]
      exact ih t (by simpa using ht)

/-- The digits of a decoded solution encode it. -/
theorem encodes_digits (p : Spec.Params) (soln : List Byte) (m : ℕ)
    (hlen : (bitsOfBytes soln).length = m * (p.digitBits + 1)) :
    EncodesSolution p soln
      (((List.range m).map (digitVal (p.digitBits + 1) (bitsOfBytes soln))).map (· + 1)) := by
  unfold EncodesSolution
  conv_lhs => rw [← flatMap_chunks (p.digitBits + 1) m _ hlen]
  simp only [List.map_map, List.flatMap_map, Function.comp, Nat.add_sub_cancel]
  apply List.flatMap_congr
  intro t ht
  rw [List.mem_range] at ht
  have hfit : (t + 1) * (p.digitBits + 1) ≤ m * (p.digitBits + 1) := Nat.mul_le_mul_right _ ht
  have hc : (((bitsOfBytes soln).drop (t * (p.digitBits + 1))).take (p.digitBits + 1)).length =
      p.digitBits + 1 := by
    rw [List.length_take, List.length_drop, hlen, Nat.succ_mul] at *; omega
  have := I2BEBSP_bitsVal (((bitsOfBytes soln).drop (t * (p.digitBits + 1))).take
    (p.digitBits + 1))
  rw [hc] at this
  rw [digitVal, this]

theorem length_flatMap_const {w : ℕ} (f : ℕ → Bits) (hf : ∀ x, (f x).length = w) (l : List ℕ) :
    (l.flatMap f).length = l.length * w := by
  induction l with
  | nil => simp
  | cons x l ih => simp [List.flatMap_cons, hf, ih, Nat.succ_mul]; ring

/-- An encoded solution of indices in `{1 .. 2^w}`, read back digit by digit, is its indices
    less one. -/
theorem digits_of_encodes (p : Spec.Params) (soln : List Byte) (i : List ℕ)
    (h : EncodesSolution p soln i) (hb : ∀ j ∈ i, 1 ≤ j ∧ j ≤ 2 ^ (p.digitBits + 1)) :
    (bitsOfBytes soln).length = i.length * (p.digitBits + 1) ∧
      ∀ t (ht : t < i.length), digitVal (p.digitBits + 1) (bitsOfBytes soln) t = i[t] - 1 := by
  unfold EncodesSolution at h
  refine ⟨by rw [h, length_flatMap_const _ (fun x => length_I2BEBSP _ _)], fun t ht => ?_⟩
  have hj := hb i[t] (List.getElem_mem ht)
  rw [digitVal, h, chunk_flatMap _ _ (fun x => length_I2BEBSP _ _) i t ht, bitsVal_I2BEBSP,
    Nat.mod_eq_of_lt (by omega)]

/-! ## The parameters -/

/-- `Params::new` accepts exactly the parameters `ZakuraParams` describes. -/
theorem Params.new?_zakura (p : ZakuraParams) : Params.new? p.n p.k = some ⟨p.n, p.k⟩ := by
  have hc : p.n % 8 = 0 ∧ p.k ≥ 3 ∧ p.k < p.n ∧ p.n % (p.k + 1) = 0 ∧ p.n ≤ 512 ∧
      8 ≤ p.n / (p.k + 1) ∧ p.n / (p.k + 1) ≤ 24 :=
    ⟨Nat.mod_eq_zero_of_dvd p.n_dvd_8, p.k_ge, p.k_lt, Nat.mod_eq_zero_of_dvd p.n_dvd, p.n_le,
      p.digit_ge, p.digit_le⟩
  simp only [Params.new?, hc, and_self, ↓reduceIte]

theorem Params.zakura_of_new? {n k : ℕ} {rp : Params} (h : Params.new? n k = some rp) :
    ∃ p : ZakuraParams, p.n = n ∧ p.k = k ∧ rp.Is p := by
  simp only [Params.new?] at h
  split_ifs at h with hc
  obtain ⟨h8, hk, hkn, hdvd, hn, hlo, hhi⟩ := hc
  cases h
  refine ⟨⟨⟨n, k, by omega, hk, Nat.dvd_of_mod_eq_zero hdvd, hn,
    Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h8) _⟩, Nat.dvd_of_mod_eq_zero h8, hkn, hlo, hhi⟩,
    rfl, rfl, rfl, rfl⟩

/-- `solution_bytes`: `2^k·(n/(k+1) + 1)/8`, unless the product overflows a `usize`. -/
theorem Params.solutionBytes?_eq {rp : Params} {p : ZakuraParams} (h : rp.Is p) :
    rp.solutionBytes? = if 2 ^ p.k * (p.digitBits + 1) < 2 ^ 64 then
      some (2 ^ p.k * (p.digitBits + 1) / 8) else none := by
  simp only [Params.solutionBytes?, Params.solutionIndices?_eq h, Option.bind_eq_bind,
    Option.bind_some, Params.collisionBitLength_eq h, checkedMul?, USIZE_BITS]
  split_ifs <;> rfl

/-! ## The hash -/

/-- The personalization `initialise_state` builds is §5.4.1.11's `powtag`. -/
theorem personalOf_eq {rp : Params} {p : ZakuraParams} (h : rp.Is p) :
    (powtag p.toParams).map BitVec.toNat = personalOf rp := by
  simp only [powtag, ← u32ToLeBytes_eq, List.map_append, map_toNat_bytesOf (bytes_u32ToLeBytes _),
    personalOf, h.1, h.2]
  rfl

/-- The hash of block index `b`, from a state that absorbed `input` then `nonce`, is BLAKE2b of
    `input ‖ nonce ‖ b`, as the leaf hasher computes it. -/
theorem generateHash_blake2b {rp : Params} {p : ZakuraParams} (h : rp.Is p) {st₀ : Blake2b.State}
    (hst : StateFor p.toParams [] st₀) (input nonce : List ℕ) (b : ℕ) :
    generateHash ((st₀.update input).update nonce) b =
      Blake2b.blake2b rp.hashOutput (personalOf rp) (input ++ nonce ++ u32ToLeBytes b) := by
  obtain ⟨hl, hp, hS, -⟩ := hst
  have h0 : st₀.input = [] := by simpa [bytesOf] using hS
  simp only [generateHash, Blake2b.State.update, Blake2b.State.finalize, hl, hp, h0,
    personalOf_eq h, genHashParams, ← Params.hashOutput_eq h, List.nil_append]

/-! ## `is_valid_solution` -/

/-- Two `ZakuraParams` with the same `n` and `k` are the same. -/
theorem ZakuraParams.ext' {p q : ZakuraParams} (hn : p.n = q.n) (hk : p.k = q.k) : p = q := by
  obtain ⟨⟨_, _, _, _, _, _, _⟩, _, _, _, _⟩ := p
  obtain ⟨⟨_, _, _, _, _, _, _⟩, _, _, _, _⟩ := q
  simp only at hn hk
  subst hn hk
  rfl

/-- **`is_valid_solution` is correct.** For a 140-byte `input ‖ nonce`, Zakura's Equihash
    verifier accepts the solution bytes `soln` with parameters `n` and `k` exactly when they
    are parameters it supports, whose solution length fits in a 64-bit `usize`, and `soln`
    encodes a solution valid by §7.7.1, for `powheader = input ‖ nonce` under BLAKE2b, with
    no repeated index. -/
theorem isValidSolution?_correct (n k : ℕ) (input nonce soln : List ℕ) (hin : Bytes input)
    (hnon : Bytes nonce) (hsoln : Bytes soln) (hlen : input.length + nonce.length = 140) :
    isValidSolution? n k input nonce soln = some () ↔
      ∃ p : ZakuraParams, p.n = n ∧ p.k = k ∧ 2 ^ p.k * (p.digitBits + 1) < 2 ^ 64 ∧
        ∃ i, EncodesSolution p.toParams (bytesOf soln) i ∧
          ValidSolution Blake2b.hashFn p.toParams (bytesOf (input ++ nonce)) i ∧ i.Nodup := by
  unfold isValidSolution?
  rcases hnew : Params.new? n k with _ | rp
  · -- Parameters `Params::new` rejects.
    simp only [Option.bind_eq_bind, Option.bind_none, reduceCtorEq, false_iff, not_exists,
      not_and]
    intro p hn hk
    rw [← hn, ← hk, Params.new?_zakura] at hnew
    simp at hnew
  obtain ⟨p, hn, hk, h⟩ := Params.zakura_of_new? hnew
  -- Every `ZakuraParams` with this `n` and `k` is `p`.
  have hR : (∃ q : ZakuraParams, q.n = n ∧ q.k = k ∧ 2 ^ q.k * (q.digitBits + 1) < 2 ^ 64 ∧
        ∃ i, EncodesSolution q.toParams (bytesOf soln) i ∧
          ValidSolution Blake2b.hashFn q.toParams (bytesOf (input ++ nonce)) i ∧ i.Nodup) ↔
      2 ^ p.k * (p.digitBits + 1) < 2 ^ 64 ∧ ∃ i, EncodesSolution p.toParams (bytesOf soln) i ∧
        ValidSolution Blake2b.hashFn p.toParams (bytesOf (input ++ nonce)) i ∧ i.Nodup :=
    ⟨fun ⟨q, hqn, hqk, hrest⟩ => ZakuraParams.ext' (hqn.trans hn.symm) (hqk.trans hk.symm) ▸ hrest,
      fun hrest => ⟨p, hn, hk, hrest⟩⟩
  rw [hR]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [indicesFromMinimal?_spec h soln hsoln, Params.solutionBytes?_eq h]
  set B := bitsOfBytes (bytesOf soln) with hB
  have hBl : B.length = 8 * soln.length := by simp [hB, length_bitsOfBytes]
  by_cases hov : 2 ^ p.k * (p.digitBits + 1) < 2 ^ 64
  swap
  · simp only [hov, ↓reduceIte, Option.bind_none, reduceCtorEq, false_and, iff_self]
  simp only [hov, ↓reduceIte, Option.bind_some, true_and]
  obtain ⟨r, hr⟩ : 8 ∣ 2 ^ p.k * (p.digitBits + 1) := by
    have := p.k_ge
    exact Dvd.dvd.mul_right ⟨2 ^ (p.k - 3), by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← Nat.pow_add, show 3 + (p.k - 3) = p.k by omega]⟩ _
  rw [hr, Nat.mul_div_cancel_left _ (by norm_num)]
  by_cases hl : soln.length = r
  swap
  · -- A solution of the wrong length.
    simp only [hl, ↓reduceIte, Option.bind_none, reduceCtorEq, false_iff, not_exists, not_and]
    intro i hE hV _
    have := (digits_of_encodes _ _ i hE fun j hj => hV.bounds j hj).1
    rw [← hB, hBl, hV.length, hr] at this
    omega
  simp only [hl, ↓reduceIte, Option.bind_some]
  -- The decoded indices.
  set L := (List.range (2 ^ p.k)).map (digitVal (p.digitBits + 1) B) with hLdef
  have hL : L.length = 2 ^ p.k := by simp [hLdef]
  have hBL : B.length = 2 ^ p.k * (p.digitBits + 1) := by rw [hBl, hl, hr]
  have hbound : ∀ j ∈ L, j < p.N := by
    intro j hj
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hj
    exact digitVal_lt _ _ _
  -- The leaf hasher, and the state it agrees with.
  obtain ⟨lh, hlh, hhash⟩ := leafHasher_spec h input nonce hin hnon hlen
  obtain ⟨st₀, -, hst₀⟩ := initialiseState?_spec h
  have hst : StateFor p.toParams (bytesOf (input ++ nonce)) ((st₀.update input).update nonce) := by
    simpa [List.map_append] using (hst₀.update input hin).update nonce hnon
  rw [hlh, Option.bind_some]
  rw [(validateTree?_iff h hst (D := fun b =>
      Blake2b.blake2b rp.hashOutput (personalOf rp) (input ++ nonce ++ u32ToLeBytes b) ++
        List.replicate (64 - rp.hashOutput) 0)
    (fun b => by rw [generateHash_blake2b h hst₀]) (fun bs ds hl hd => hhash bs ds hl hd) hL).trans
    (good_iff_validSolution _ _ _ _ hL hbound)]
  constructor
  · rintro ⟨hV, hN⟩
    exact ⟨L.map (· + 1), encodes_digits _ _ _ (by rw [← hB, hBL, Nat.mul_comm]), hV,
      hN.map Nat.succ_injective⟩
  · rintro ⟨i, hE, hV, hN⟩
    obtain ⟨-, hdig⟩ := digits_of_encodes _ _ i hE fun j hj => hV.bounds j hj
    have hi : L.map (· + 1) = i := by
      apply List.ext_getElem (by simp [hL, hV.length])
      intro t h1 h2
      have := (hV.bounds i[t] (List.getElem_mem h2)).1
      simp only [List.getElem_map, hLdef, List.getElem_range]
      rw [hdig t h2]
      omega
    rw [hi]
    refine ⟨hV, ?_⟩
    rw [← hi] at hN
    exact (List.nodup_map_iff Nat.succ_injective).mp hN

/-- **The single-pass verifier gives the recursive one's answer.** On `2^k` indices and a
    140-byte `input ‖ nonce`, `validate_tree` with the leaf hasher accepts exactly when
    `is_valid_solution_recursive` does. -/
theorem validateTree?_eq_recursive {rp : Params} {p : ZakuraParams} (h : rp.Is p)
    (input nonce : List ℕ) (hin : Bytes input) (hnon : Bytes nonce)
    (hlen : input.length + nonce.length = 140) {lh : LeafHasher}
    (hlh : LeafHasher.new? rp input nonce = some lh) (L : List ℕ) (hL : L.length = 2 ^ p.k) :
    validateTree? rp L (fun blocks digests => lh.hash? blocks digests) =
      isValidSolutionRecursive? rp input nonce L := by
  obtain ⟨lh', hlh', hhash⟩ := leafHasher_spec h input nonce hin hnon hlen
  rw [hlh, Option.some.injEq] at hlh'
  subst hlh'
  obtain ⟨st₀, -, hst₀⟩ := initialiseState?_spec h
  have hst : StateFor p.toParams (bytesOf (input ++ nonce)) ((st₀.update input).update nonce) := by
    simpa [List.map_append] using (hst₀.update input hin).update nonce hnon
  have hiff := (validateTree?_iff h hst (D := fun b =>
      Blake2b.blake2b rp.hashOutput (personalOf rp) (input ++ nonce ++ u32ToLeBytes b) ++
        List.replicate (64 - rp.hashOutput) 0)
    (fun b => by rw [generateHash_blake2b h hst₀]) (fun bs ds hl hd => hhash bs ds hl hd) hL).trans
    (isValidSolutionRecursive?_iff h input nonce L hin hnon hL).symm
  rcases hv : validateTree? rp L (fun blocks digests => lh.hash? blocks digests) with _ | ⟨⟩ <;>
    rcases hr : isValidSolutionRecursive? rp input nonce L with _ | ⟨⟩ <;> simp_all

/-! ## Zcash's parameters -/

/-- Mainnet and Testnet: `n = 200`, `k = 9`. -/
def zcashParams : ZakuraParams :=
  ⟨⟨200, 9, by decide, by decide, by decide, by decide, by decide⟩, by decide, by decide,
    by decide, by decide⟩

/-- Regtest: `n = 48`, `k = 5`. -/
def regtestParams : ZakuraParams :=
  ⟨⟨48, 5, by decide, by decide, by decide, by decide, by decide⟩, by decide, by decide,
    by decide, by decide⟩

/-- **`is_valid_solution(200, 9, …)`** accepts exactly the 1344-byte encodings of §7.7.1-valid
    solutions with no repeated index. -/
theorem isValidSolution?_zcash (input nonce soln : List ℕ) (hin : Bytes input)
    (hnon : Bytes nonce) (hsoln : Bytes soln) (hlen : input.length + nonce.length = 140) :
    isValidSolution? 200 9 input nonce soln = some () ↔
      ∃ i, EncodesSolution zcashParams.toParams (bytesOf soln) i ∧
        ValidSolution Blake2b.hashFn zcashParams.toParams (bytesOf (input ++ nonce)) i ∧
          i.Nodup := by
  rw [isValidSolution?_correct 200 9 input nonce soln hin hnon hsoln hlen]
  exact ⟨fun ⟨p, hn, hk, _, hrest⟩ => ZakuraParams.ext' (p := p) (q := zcashParams) hn hk ▸ hrest,
    fun hrest => ⟨zcashParams, rfl, rfl, by decide, hrest⟩⟩

/-- **`is_valid_solution(48, 5, …)`**, likewise. -/
theorem isValidSolution?_regtest (input nonce soln : List ℕ) (hin : Bytes input)
    (hnon : Bytes nonce) (hsoln : Bytes soln) (hlen : input.length + nonce.length = 140) :
    isValidSolution? 48 5 input nonce soln = some () ↔
      ∃ i, EncodesSolution regtestParams.toParams (bytesOf soln) i ∧
        ValidSolution Blake2b.hashFn regtestParams.toParams (bytesOf (input ++ nonce)) i ∧
          i.Nodup := by
  rw [isValidSolution?_correct 48 5 input nonce soln hin hnon hsoln hlen]
  exact ⟨fun ⟨p, hn, hk, _, hrest⟩ =>
      ZakuraParams.ext' (p := p) (q := regtestParams) hn hk ▸ hrest,
    fun hrest => ⟨regtestParams, rfl, rfl, by decide, hrest⟩⟩

-- The build fails if the theorem rests on anything beyond Lean's three axioms.
/--
info: 'Equihash.Verifier.isValidSolution?_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms isValidSolution?_correct

end Equihash.Verifier
