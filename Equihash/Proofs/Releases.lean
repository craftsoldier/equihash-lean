/-
Each release's `is_valid_solution` is correct: it returns `Ok(())` exactly for the solution bytes
that encode a §7.7.1-valid solution with no repeated index; `zakura-equihash 4.0.0` on a 140-byte
`input ‖ nonce`, `equihash 0.3.0` and `0.3.1` on one of any length, each under every leaf-hashing
kernel. And `equihash 0.3.0`'s length check wraps where Zakura's checks for overflow, so that for
`(448, 63)` and `(520, 64)` it accepts a solution of the wrong length, and the verifier then
panics; `0.3.1` rejects every solution for them.
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

/-- The digits of solution bytes of the right length, one-based, are a valid solution with
    distinct indices exactly when the bytes encode one. -/
theorem decoded_iff (p : ZakuraParams) (soln : List ℕ) (S : List Byte)
    (hBL : (bitsOfBytes (bytesOf soln)).length = 2 ^ p.k * (p.digitBits + 1)) :
    (ValidSolution Blake2b.hashFn p.toParams S (((List.range (2 ^ p.k)).map
        (digitVal (p.digitBits + 1) (bitsOfBytes (bytesOf soln)))).map (· + 1)) ∧
      ((List.range (2 ^ p.k)).map
        (digitVal (p.digitBits + 1) (bitsOfBytes (bytesOf soln)))).Nodup) ↔
      ∃ i, EncodesSolution p.toParams (bytesOf soln) i ∧
        ValidSolution Blake2b.hashFn p.toParams S i ∧ i.Nodup := by
  set B := bitsOfBytes (bytesOf soln) with hB
  set L := (List.range (2 ^ p.k)).map (digitVal (p.digitBits + 1) B) with hLdef
  have hL : L.length = 2 ^ p.k := by simp [hLdef]
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

/-- **`is_valid_solution` is correct.** For a 140-byte `input ‖ nonce`, under any kernel,
    Zakura's Equihash verifier returns `Ok(())` for the solution bytes `soln` with parameters
    `n` and `k` exactly when they are parameters it supports, whose solutions are under `2^62`
    bits long, and `soln` encodes a solution valid by §7.7.1, for `powheader = input ‖ nonce`
    under BLAKE2b, with no repeated index. -/
theorem isValidSolution?_correct (kernel : Kernel) (n k : ℕ) (input nonce soln : List ℕ)
    (hin : Bytes input) (hnon : Bytes nonce) (hsoln : Bytes soln)
    (hlen : input.length + nonce.length = 140) :
    (isValidSolution? kernel n k input nonce soln).run = some (.ok ()) ↔
      ∃ p : ZakuraParams, p.n = n ∧ p.k = k ∧ 2 ^ p.k * (p.digitBits + 1) < 2 ^ 62 ∧
        ∃ i, EncodesSolution p.toParams (bytesOf soln) i ∧
          ValidSolution Blake2b.hashFn p.toParams (bytesOf (input ++ nonce)) i ∧ i.Nodup := by
  unfold isValidSolution?
  rcases hnew : Params.new? n k with _ | rp
  · -- Parameters `Params::new` rejects.
    simp only [ExceptT.run_throw, Option.pure_def, Option.some.injEq, reduceCtorEq, false_iff,
      not_exists, not_and]
    intro p hn hk
    rw [← hn, ← hk, Params.new?_zakura] at hnew
    simp at hnew
  obtain ⟨p, hn, hk, h⟩ := Params.zakura_of_new? hnew
  -- Every `ZakuraParams` with this `n` and `k` is `p`.
  have hR : (∃ q : ZakuraParams, q.n = n ∧ q.k = k ∧ 2 ^ q.k * (q.digitBits + 1) < 2 ^ 62 ∧
        ∃ i, EncodesSolution q.toParams (bytesOf soln) i ∧
          ValidSolution Blake2b.hashFn q.toParams (bytesOf (input ++ nonce)) i ∧ i.Nodup) ↔
      2 ^ p.k * (p.digitBits + 1) < 2 ^ 62 ∧ ∃ i, EncodesSolution p.toParams (bytesOf soln) i ∧
        ValidSolution Blake2b.hashFn p.toParams (bytesOf (input ++ nonce)) i ∧ i.Nodup :=
    ⟨fun ⟨q, hqn, hqk, hrest⟩ => ZakuraParams.ext' (hqn.trans hn.symm) (hqk.trans hk.symm) ▸ hrest,
      fun hrest => ⟨p, hn, hk, hrest⟩⟩
  rw [hR]
  dsimp only
  by_cases hfit : 2 ^ p.k * (p.digitBits + 1) < 2 ^ 62
  swap
  · -- Solutions of `2^62` bits or more: the decoder rejects or panics.
    simp only [hfit, false_and, iff_false]
    rcases hI : indicesFromMinimal? rp soln with _ | _ | L
    · simp [ExceptT.run_bind, liftM, monadLift, MonadLift.monadLift, ExceptT.lift]
    · simp
    · exact absurd hI (indicesFromMinimal?_ne_of_big h soln hfit L)
  have hov : 2 ^ p.k * (p.digitBits + 1) < 2 ^ 64 := by omega
  rw [indicesFromMinimal?_spec h soln hsoln hfit, Params.solutionBytes?_eq h]
  simp only [monadLift_some, pure_bind]
  set B := bitsOfBytes (bytesOf soln) with hB
  have hBl : B.length = 8 * soln.length := by simp [hB, length_bitsOfBytes]
  simp only [hov, hfit, ↓reduceIte, Option.bind_some, true_and]
  obtain ⟨r, hr⟩ : 8 ∣ 2 ^ p.k * (p.digitBits + 1) := by
    have := p.k_ge
    exact Dvd.dvd.mul_right ⟨2 ^ (p.k - 3), by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← Nat.pow_add, show 3 + (p.k - 3) = p.k by omega]⟩ _
  rw [hr, Nat.mul_div_cancel_left _ (by norm_num)]
  by_cases hl : soln.length = r
  swap
  · -- A solution of the wrong length.
    simp only [hl, ↓reduceIte, run_throw, Option.some.injEq, reduceCtorEq, false_iff, not_exists,
      not_and]
    intro i hE hV _
    have := (digits_of_encodes _ _ i hE fun j hj => hV.bounds j hj).1
    rw [← hB, hBl, hV.length, hr] at this
    omega
  simp only [hl, ↓reduceIte]
  -- The decoded indices.
  set L := (List.range (2 ^ p.k)).map (digitVal (p.digitBits + 1) B) with hLdef
  have hL : L.length = 2 ^ p.k := by simp [hLdef]
  have hBL : B.length = 2 ^ p.k * (p.digitBits + 1) := by rw [hBl, hl, hr]
  have hbound : ∀ j ∈ L, j < p.N := by
    intro j hj
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hj
    exact digitVal_lt _ _ _
  -- The leaf hasher, and the state it agrees with.
  obtain ⟨lh, hlh, hhash⟩ := leafHasher_spec h input nonce hin hnon hlen kernel
  obtain ⟨st₀, -, hst₀⟩ := initialiseState?_spec h
  have hst : StateFor p.toParams (bytesOf (input ++ nonce)) ((st₀.update input).update nonce) := by
    simpa [List.map_append] using (hst₀.update input hin).update nonce hnon
  rw [hlh]
  simp only [monadLift_some, pure_bind]
  rw [(validateTree?_iff h hst (D := fun b =>
      Blake2b.blake2b rp.hashOutput (personalOf rp) (input ++ nonce ++ u32ToLeBytes b) ++
        List.replicate (64 - rp.hashOutput) 0)
    (fun b => by rw [generateHash_blake2b h hst₀])
    (fun bs ds hl hd => hhash bs ds hl fun d hd' => (hd d hd').1) hL).trans
    (good_iff_validSolution _ _ _ _ hL hbound)]
  exact decoded_iff p soln _ hBL

/-- **The single-pass verifier gives the recursive one's answer.** On `2^k` indices and a
    140-byte `input ‖ nonce`, `validate_tree` with the leaf hasher returns `Ok(())` exactly when
    `is_valid_solution_recursive` does. -/
theorem validateTree?_iff_recursive {rp : Params} {p : ZakuraParams} (h : rp.Is p)
    (input nonce : List ℕ) (hin : Bytes input) (hnon : Bytes nonce)
    (hlen : input.length + nonce.length = 140) (kernel : Kernel) {lh : LeafHasher}
    (hlh : LeafHasher.new? rp input nonce kernel = some (some lh)) (L : List ℕ)
    (hL : L.length = 2 ^ p.k) :
    (validateTree? rp L (fun blocks digests => lh.hash? blocks digests)).run = some (.ok ()) ↔
      (isValidSolutionRecursive? rp input nonce L).run = some (.ok ()) := by
  obtain ⟨lh', hlh', hhash⟩ := leafHasher_spec h input nonce hin hnon hlen kernel
  rw [hlh, Option.some.injEq, Option.some.injEq] at hlh'
  subst hlh'
  obtain ⟨st₀, -, hst₀⟩ := initialiseState?_spec h
  have hst : StateFor p.toParams (bytesOf (input ++ nonce)) ((st₀.update input).update nonce) := by
    simpa [List.map_append] using (hst₀.update input hin).update nonce hnon
  exact (validateTree?_iff h hst (D := fun b =>
      Blake2b.blake2b rp.hashOutput (personalOf rp) (input ++ nonce ++ u32ToLeBytes b) ++
        List.replicate (64 - rp.hashOutput) 0)
    (fun b => by rw [generateHash_blake2b h hst₀])
    (fun bs ds hl hd => hhash bs ds hl fun d hd' => (hd d hd').1) hL).trans
    (isValidSolutionRecursive?_iff h input nonce L hin hnon hL).symm

/-! ## Zcash's parameters -/

/-- Mainnet and Testnet: `n = 200`, `k = 9`. -/
def zcashParams : ZakuraParams :=
  ⟨⟨200, 9, by decide, by decide, by decide, by decide, by decide⟩, by decide, by decide,
    by decide, by decide⟩

/-- Regtest: `n = 48`, `k = 5`. -/
def regtestParams : ZakuraParams :=
  ⟨⟨48, 5, by decide, by decide, by decide, by decide, by decide⟩, by decide, by decide,
    by decide, by decide⟩

/-- **`is_valid_solution(200, 9, …)`** returns `Ok(())` exactly for the 1344-byte encodings of
    §7.7.1-valid solutions with no repeated index. -/
theorem isValidSolution?_zcash (kernel : Kernel) (input nonce soln : List ℕ) (hin : Bytes input)
    (hnon : Bytes nonce) (hsoln : Bytes soln) (hlen : input.length + nonce.length = 140) :
    (isValidSolution? kernel 200 9 input nonce soln).run = some (.ok ()) ↔
      ∃ i, EncodesSolution zcashParams.toParams (bytesOf soln) i ∧
        ValidSolution Blake2b.hashFn zcashParams.toParams (bytesOf (input ++ nonce)) i ∧
          i.Nodup := by
  rw [isValidSolution?_correct kernel 200 9 input nonce soln hin hnon hsoln hlen]
  exact ⟨fun ⟨p, hn, hk, _, hrest⟩ => ZakuraParams.ext' (p := p) (q := zcashParams) hn hk ▸ hrest,
    fun hrest => ⟨zcashParams, rfl, rfl, by decide, hrest⟩⟩

/-- **`is_valid_solution(48, 5, …)`**, likewise. -/
theorem isValidSolution?_regtest (kernel : Kernel) (input nonce soln : List ℕ)
    (hin : Bytes input) (hnon : Bytes nonce) (hsoln : Bytes soln)
    (hlen : input.length + nonce.length = 140) :
    (isValidSolution? kernel 48 5 input nonce soln).run = some (.ok ()) ↔
      ∃ i, EncodesSolution regtestParams.toParams (bytesOf soln) i ∧
        ValidSolution Blake2b.hashFn regtestParams.toParams (bytesOf (input ++ nonce)) i ∧
          i.Nodup := by
  rw [isValidSolution?_correct kernel 48 5 input nonce soln hin hnon hsoln hlen]
  exact ⟨fun ⟨p, hn, hk, _, hrest⟩ =>
      ZakuraParams.ext' (p := p) (q := regtestParams) hn hk ▸ hrest,
    fun hrest => ⟨regtestParams, rfl, rfl, by decide, hrest⟩⟩

/-! ## `equihash 0.3.0` -/

/-- 0.3.0's `expand_array` computes what Zakura's does, on every input. -/
theorem expandArrayAlloc?_eq (vin : List ℕ) (bitLen bytePad : ℕ) :
    expandArrayAlloc? vin bitLen bytePad = expandArray? vin bitLen bytePad := by
  unfold expandArrayAlloc? expandArray? expandArrayInto?
  simp only [List.length_replicate, expandedLen, guard_true, List.map_replicate]
  rfl

/-- 0.3.0's `Node::new` computes what Zakura's does. -/
theorem Node.new_equihash_0_3_0?_eq (p : Params) (state : Blake2b.State) (i : ℕ) :
    Node.new_equihash_0_3_0? p state i = Node.new? p state i := by
  simp only [Node.new_equihash_0_3_0?, Node.new?, expandArrayAlloc?_eq]

/-- 0.3.0's `tree_validator` computes what Zakura's does. -/
theorem treeValidator_equihash_0_3_0?_eq (p : Params) (state : Blake2b.State)
    (indices : List ℕ) :
    treeValidator_equihash_0_3_0? p state indices = treeValidator? p state indices := by
  rw [treeValidator_equihash_0_3_0?, treeValidator?]
  split
  · dsimp only
    rw [treeValidator_equihash_0_3_0?_eq p state (indices.take (indices.length / 2)),
      treeValidator_equihash_0_3_0?_eq p state (indices.drop (indices.length / 2))]
  · simp only [Node.new_equihash_0_3_0?_eq]
termination_by indices.length
decreasing_by all_goals simp only [List.length_take, List.length_drop]; omega

/-- 0.3.0's `is_valid_solution_recursive` computes what Zakura's does. -/
theorem isValidSolutionRecursive_equihash_0_3_0?_eq (p : Params) (input nonce indices : List ℕ) :
    isValidSolutionRecursive_equihash_0_3_0? p input nonce indices =
      isValidSolutionRecursive? p input nonce indices := by
  simp only [isValidSolutionRecursive_equihash_0_3_0?, isValidSolutionRecursive?,
    treeValidator_equihash_0_3_0?_eq]

/-- 0.3.0's `indices_from_minimal`, as its loop body. -/
theorem indicesFromMinimalWrapping?_eq (p : Params) (minimal : List ℕ) :
    indicesFromMinimalWrapping? p minimal =
      (if minimal.length ≠ (1 <<< (p.k % USIZE_BITS)) * (p.collisionBitLength + 1) %
          2 ^ USIZE_BITS / 8 then some none else do
        guard (divCeil (p.collisionBitLength + 1) 8 ≤ 4)
        let out ← expandArrayAlloc? minimal (p.collisionBitLength + 1)
          (4 - divCeil (p.collisionBitLength + 1) 8)
        let s ← forIn Lean.Loop.mk (({ inner := out, pos := 0 } : Cursor), ([] : List ℕ)) readPass
        pure (some s.2)) := by
  rfl

/-- When a solution is under `2^64` bits long, 0.3.0's unchecked length is the checked
    one, and its `indices_from_minimal` is Zakura's. -/
theorem indicesFromMinimalWrapping?_eq_of_fit {rp : Params} {p : ZakuraParams} (h : rp.Is p)
    (hfit : 2 ^ p.k * (p.digitBits + 1) < 2 ^ 64) (minimal : List ℕ) :
    indicesFromMinimalWrapping? rp minimal = indicesFromMinimal? rp minimal := by
  have hk : p.k < 64 := by
    have : 2 ^ p.k < 2 ^ 64 := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by omega)) hfit
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
  have hlen : (1 <<< (rp.k % USIZE_BITS)) * (rp.collisionBitLength + 1) % 2 ^ USIZE_BITS / 8 =
      2 ^ p.k * (p.digitBits + 1) / 8 := by
    rw [h.2, Params.collisionBitLength_eq h, USIZE_BITS, Nat.mod_eq_of_lt hk, Nat.one_shiftLeft,
      Nat.mod_eq_of_lt hfit]
  rw [indicesFromMinimal?_eq, Params.solutionBytes?_eq h]
  simp only [hfit, ↓reduceIte]
  unfold indicesFromMinimalWrapping?
  simp only [hlen, expandArrayAlloc?_eq]
  rfl

/-- 0.3.0's `Params::new` accepts every parameter set Zakura's does. -/
theorem Params.newUnbounded?_zakura (p : ZakuraParams) :
    Params.newUnbounded? p.n p.k = some ⟨p.n, p.k⟩ := by
  have hc : p.n % 8 = 0 ∧ p.k ≥ 3 ∧ p.k < p.n ∧ p.n % (p.k + 1) = 0 :=
    ⟨Nat.mod_eq_zero_of_dvd p.n_dvd_8, p.k_ge, p.k_lt, Nat.mod_eq_zero_of_dvd p.n_dvd⟩
  simp only [Params.newUnbounded?, hc, and_self, ↓reduceIte]

/-- **`equihash 0.3.0`'s `is_valid_solution` is correct**, for parameters Zakura accepts whose
    solutions are under `2^62` bits long, and an `input ‖ nonce` of any length: it returns
    `Ok(())` exactly for the solution bytes that encode a solution valid by §7.7.1, for
    `powheader = input ‖ nonce` under BLAKE2b, with no repeated index. -/
theorem isValidSolution_equihash_0_3_0?_correct (p : ZakuraParams) (input nonce soln : List ℕ)
    (hin : Bytes input) (hnon : Bytes nonce) (hsoln : Bytes soln)
    (hfit : 2 ^ p.k * (p.digitBits + 1) < 2 ^ 62) :
    (isValidSolution_equihash_0_3_0? p.n p.k input nonce soln).run = some (.ok ()) ↔
      ∃ i, EncodesSolution p.toParams (bytesOf soln) i ∧
        ValidSolution Blake2b.hashFn p.toParams (bytesOf (input ++ nonce)) i ∧ i.Nodup := by
  have h : (⟨p.n, p.k⟩ : Params).Is p := ⟨rfl, rfl⟩
  have hov : 2 ^ p.k * (p.digitBits + 1) < 2 ^ 64 := by omega
  unfold isValidSolution_equihash_0_3_0?
  rw [Params.newUnbounded?_zakura]
  dsimp only
  simp only [isValidSolutionRecursive_equihash_0_3_0?_eq]
  rw [indicesFromMinimalWrapping?_eq_of_fit h hov, indicesFromMinimal?_spec h soln hsoln hfit,
    Params.solutionBytes?_eq h]
  simp only [hov, ↓reduceIte, Option.bind_some, monadLift_some, pure_bind]
  have hBl : (bitsOfBytes (bytesOf soln)).length = 8 * soln.length := by
    simp [length_bitsOfBytes]
  obtain ⟨r, hr⟩ : 8 ∣ 2 ^ p.k * (p.digitBits + 1) := by
    have := p.k_ge
    exact Dvd.dvd.mul_right ⟨2 ^ (p.k - 3), by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← Nat.pow_add, show 3 + (p.k - 3) = p.k by omega]⟩ _
  rw [hr, Nat.mul_div_cancel_left _ (by norm_num)]
  by_cases hl : soln.length = r
  swap
  · -- A solution of the wrong length.
    simp only [hl, ↓reduceIte, run_throw, Option.some.injEq, reduceCtorEq, false_iff, not_exists,
      not_and]
    intro i hE hV _
    have := (digits_of_encodes _ _ i hE fun j hj => hV.bounds j hj).1
    rw [hBl, hV.length, hr] at this
    omega
  simp only [hl, ↓reduceIte]
  have hL : ((List.range (2 ^ p.k)).map
      (digitVal (p.digitBits + 1) (bitsOfBytes (bytesOf soln)))).length = 2 ^ p.k := by simp
  rw [isValidSolutionRecursive?_correct h input nonce _ hin hnon hL (fun j hj => by
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hj
    exact digitVal_lt _ _ _)]
  exact decoded_iff p soln _ (by rw [hBl, hl, hr])

/-- **`equihash 0.3.0`'s `is_valid_solution(200, 9, …)`** returns `Ok(())` exactly for the
    1344-byte encodings of §7.7.1-valid solutions with no repeated index, for any input. -/
theorem isValidSolution_equihash_0_3_0?_zcash (input nonce soln : List ℕ) (hin : Bytes input)
    (hnon : Bytes nonce) (hsoln : Bytes soln) :
    (isValidSolution_equihash_0_3_0? 200 9 input nonce soln).run = some (.ok ()) ↔
      ∃ i, EncodesSolution zcashParams.toParams (bytesOf soln) i ∧
        ValidSolution Blake2b.hashFn zcashParams.toParams (bytesOf (input ++ nonce)) i ∧
          i.Nodup :=
  isValidSolution_equihash_0_3_0?_correct zcashParams input nonce soln hin hnon hsoln (by decide)

/-- **`equihash 0.3.0`'s `is_valid_solution(48, 5, …)`**, likewise. -/
theorem isValidSolution_equihash_0_3_0?_regtest (input nonce soln : List ℕ) (hin : Bytes input)
    (hnon : Bytes nonce) (hsoln : Bytes soln) :
    (isValidSolution_equihash_0_3_0? 48 5 input nonce soln).run = some (.ok ()) ↔
      ∃ i, EncodesSolution regtestParams.toParams (bytesOf soln) i ∧
        ValidSolution Blake2b.hashFn regtestParams.toParams (bytesOf (input ++ nonce)) i ∧
          i.Nodup :=
  isValidSolution_equihash_0_3_0?_correct regtestParams input nonce soln hin hnon hsoln
    (by decide)

/-- **`equihash 0.3.0` checks the solution length with wrapping arithmetic.** Its `Params::new`
    accepts `(448, 63)`, whose solutions have `2^63` eight-bit indices, `2^63` bytes. The length
    check computes `2^63 · 8 mod 2^64 / 8 = 0` and accepts the empty solution, which decodes to
    no indices, and the verifier then panics: `tree_validator` reads the first of none. -/
theorem isValidSolution_equihash_0_3_0?_448_63 (input nonce : List ℕ) :
    Params.newUnbounded? 448 63 = some ⟨448, 63⟩ ∧
      indicesFromMinimalWrapping? ⟨448, 63⟩ [] = some (some []) ∧
      (isValidSolution_equihash_0_3_0? 448 63 input nonce []).run = none := by
  have hp : Params.newUnbounded? 448 63 = some ⟨448, 63⟩ := rfl
  have hd : indicesFromMinimalWrapping? ⟨448, 63⟩ [] = some (some []) := by
    rw [indicesFromMinimalWrapping?_eq]
    have he : expandArrayAlloc? [] 8 3 = some [] := rfl
    split
    · exact absurd ‹_› (by decide)
    simp only [Params.collisionBitLength, show divCeil (448 / (63 + 1) + 1) 8 = 1 from rfl,
      show 448 / (63 + 1) + 1 = 8 from rfl, he, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some]
    rw [loop_unfold]
    rfl
  refine ⟨hp, hd, ?_⟩
  unfold isValidSolution_equihash_0_3_0?
  rw [hp]
  dsimp only
  rw [hd]
  simp only [monadLift_some, pure_bind]
  unfold isValidSolutionRecursive_equihash_0_3_0?
  obtain ⟨st, hst⟩ : ∃ st, initialiseState? (⟨448, 63⟩ : Params).n (⟨448, 63⟩ : Params).k
      (⟨448, 63⟩ : Params).hashOutput = some st := ⟨_, rfl⟩
  rw [hst]
  simp only [monadLift_some, pure_bind]
  rw [treeValidator_equihash_0_3_0?]
  rfl

/-- **Likewise `(520, 64)`.** `1 << 64` shifts by `64 mod 64 = 0`, so the length check expects
    `1 · 9 / 8 = 1` byte, though a solution has `2^64` nine-bit indices. Every one-byte solution
    passes it and decodes to no indices, and the verifier then panics: `512 / n = 0`, so
    `initialise_state` asks `blake2b_simd` for a zero-byte digest, which it refuses. -/
theorem isValidSolution_equihash_0_3_0?_520_64 (input nonce : List ℕ) (b : ℕ) :
    Params.newUnbounded? 520 64 = some ⟨520, 64⟩ ∧
      indicesFromMinimalWrapping? ⟨520, 64⟩ [b] = some (some []) ∧
      (isValidSolution_equihash_0_3_0? 520 64 input nonce [b]).run = none := by
  have hp : Params.newUnbounded? 520 64 = some ⟨520, 64⟩ := rfl
  have hd : indicesFromMinimalWrapping? ⟨520, 64⟩ [b] = some (some []) := by
    rw [indicesFromMinimalWrapping?_eq]
    have he : expandArrayAlloc? [b] 9 2 = some [0, 0, 0] := by
      simp [expandArrayAlloc?, divCeil]
    split
    · exact absurd ‹_› (by simp only [List.length_singleton]; decide)
    simp only [Params.collisionBitLength, show divCeil (520 / (64 + 1) + 1) 8 = 2 from rfl,
      show 520 / (64 + 1) + 1 = 9 from rfl, he, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some]
    rw [loop_unfold]
    rfl
  refine ⟨hp, hd, ?_⟩
  unfold isValidSolution_equihash_0_3_0?
  rw [hp]
  dsimp only
  rw [hd]
  simp only [monadLift_some, pure_bind]
  rfl

/-! ## `equihash 0.3.1` -/

/-- `LeafHasher::new` is `None` unless `input ‖ nonce` is 140 bytes. -/
theorem LeafHasher.new?_of_ne (rp : Params) (input nonce : List ℕ) (kernel : Kernel)
    (hlen : input.length + nonce.length ≠ 140) :
    LeafHasher.new? rp input nonce kernel = some none := by
  simp [LeafHasher.new?, LeafHasher.withKernel?, Midstate.new?_eq, LeafHash.HEADER_BYTES,
    LeafHash.NONCE_BYTES, hlen]

/-- The `blake2b_simd` closure gives each block the digest `generate_hash` computes, zero-padded
    to 64 bytes, on digests whose bytes past the digest length are zero. -/
theorem blake2bSimdHash?_spec {rp : Params} {p : ZakuraParams} (h : rp.Is p) {S : List Byte}
    {st : Blake2b.State} (hst : StateFor p.toParams S st) (bs : List ℕ) (ds : List (List ℕ))
    (hl : ds.length = bs.length)
    (hd : ∀ d ∈ ds, d.length = 64 ∧ d.drop rp.hashOutput = List.replicate (64 - rp.hashOutput) 0) :
    blake2bSimdHash? st bs ds =
      some (bs.map fun b => generateHash st b ++ List.replicate (64 - rp.hashOutput) 0) := by
  have hlen : ∀ b, (generateHash st b).length = rp.hashOutput := fun b => by
    rw [generateHash_eq hst, List.length_map, List.Vector.toList_length, Params.hashOutput_eq h]
    rfl
  simp only [blake2bSimdHash?, hlen, List.drop_of_length_le hl.le, List.append_nil,
    Option.pure_def, Option.some.injEq]
  induction bs generalizing ds with
  | nil => simp
  | cons b bs ih =>
    rcases ds with _ | ⟨d, ds⟩
    · simp at hl
    simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq]
    exact ⟨by rw [(hd d (by simp)).2],
      ih ds (by simpa using hl) fun d' hd' => hd d' (by simp [hd'])⟩

/-- **`equihash 0.3.1`'s `is_valid_solution` is correct**, for parameters Zakura accepts and an
    `input ‖ nonce` of any length: it returns `Ok(())` exactly when the solutions are under
    `2^62` bits long and the solution bytes encode a solution valid by §7.7.1, for
    `powheader = input ‖ nonce` under BLAKE2b, with no repeated index. On a 140-byte
    `input ‖ nonce` the leaf hasher computes BLAKE2b, under any kernel; on any other,
    `blake2b_simd` is assumed to. -/
theorem isValidSolution_equihash_0_3_1?_correct (kernel : Kernel) (p : ZakuraParams)
    (input nonce soln : List ℕ) (hin : Bytes input) (hnon : Bytes nonce) (hsoln : Bytes soln) :
    (isValidSolution_equihash_0_3_1? kernel p.n p.k input nonce soln).run = some (.ok ()) ↔
      2 ^ p.k * (p.digitBits + 1) < 2 ^ 62 ∧
      ∃ i, EncodesSolution p.toParams (bytesOf soln) i ∧
        ValidSolution Blake2b.hashFn p.toParams (bytesOf (input ++ nonce)) i ∧ i.Nodup := by
  have h : (⟨p.n, p.k⟩ : Params).Is p := ⟨rfl, rfl⟩
  unfold isValidSolution_equihash_0_3_1?
  rw [Params.newUnbounded?_zakura]
  dsimp only
  by_cases hfit : 2 ^ p.k * (p.digitBits + 1) < 2 ^ 62
  swap
  · -- Solutions of `2^62` bits or more: the decoder rejects or panics.
    simp only [hfit, false_and, iff_false]
    rcases hI : indicesFromMinimal? ⟨p.n, p.k⟩ soln with _ | _ | L
    · simp [ExceptT.run_bind, liftM, monadLift, MonadLift.monadLift, ExceptT.lift]
    · simp
    · exact absurd hI (indicesFromMinimal?_ne_of_big h soln hfit L)
  have hov : 2 ^ p.k * (p.digitBits + 1) < 2 ^ 64 := by omega
  rw [indicesFromMinimal?_spec h soln hsoln hfit, Params.solutionBytes?_eq h]
  simp only [monadLift_some, pure_bind]
  set B := bitsOfBytes (bytesOf soln) with hB
  have hBl : B.length = 8 * soln.length := by simp [hB, length_bitsOfBytes]
  simp only [hov, hfit, ↓reduceIte, Option.bind_some, true_and]
  obtain ⟨r, hr⟩ : 8 ∣ 2 ^ p.k * (p.digitBits + 1) := by
    have := p.k_ge
    exact Dvd.dvd.mul_right ⟨2 ^ (p.k - 3), by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← Nat.pow_add, show 3 + (p.k - 3) = p.k by omega]⟩ _
  rw [hr, Nat.mul_div_cancel_left _ (by norm_num)]
  by_cases hl : soln.length = r
  swap
  · -- A solution of the wrong length.
    simp only [hl, ↓reduceIte, run_throw, Option.some.injEq, reduceCtorEq, false_iff, not_exists,
      not_and]
    intro i hE hV _
    have := (digits_of_encodes _ _ i hE fun j hj => hV.bounds j hj).1
    rw [← hB, hBl, hV.length, hr] at this
    omega
  simp only [hl, ↓reduceIte]
  -- The decoded indices.
  set L := (List.range (2 ^ p.k)).map (digitVal (p.digitBits + 1) B) with hLdef
  have hL : L.length = 2 ^ p.k := by simp [hLdef]
  have hBL : B.length = 2 ^ p.k * (p.digitBits + 1) := by rw [hBl, hl, hr]
  have hbound : ∀ j ∈ L, j < p.N := by
    intro j hj
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hj
    exact digitVal_lt _ _ _
  -- The state `blake2b_simd` would hash from.
  obtain ⟨st₀, hst₀eq, hst₀⟩ := initialiseState?_spec h
  have hst : StateFor p.toParams (bytesOf (input ++ nonce)) ((st₀.update input).update nonce) := by
    simpa [List.map_append] using (hst₀.update input hin).update nonce hnon
  by_cases h140 : input.length + nonce.length = 140
  · -- The leaf hasher.
    obtain ⟨lh, hlh, hhash⟩ := leafHasher_spec h input nonce hin hnon h140 kernel
    rw [hlh]
    simp only [monadLift_some, pure_bind]
    rw [(validateTree?_iff h hst (D := fun b =>
        Blake2b.blake2b (⟨p.n, p.k⟩ : Params).hashOutput (personalOf ⟨p.n, p.k⟩)
          (input ++ nonce ++ u32ToLeBytes b) ++
          List.replicate (64 - (⟨p.n, p.k⟩ : Params).hashOutput) 0)
      (fun b => by rw [generateHash_blake2b h hst₀])
      (fun bs ds hl hd => hhash bs ds hl fun d hd' => (hd d hd').1) hL).trans
      (good_iff_validSolution _ _ _ _ hL hbound)]
    exact decoded_iff p soln _ hBL
  · -- `blake2b_simd`.
    rw [LeafHasher.new?_of_ne _ _ _ _ h140]
    simp only [monadLift_some, pure_bind]
    rw [hst₀eq]
    simp only [monadLift_some, pure_bind]
    rw [(validateTree?_iff h hst (D := fun b => generateHash ((st₀.update input).update nonce) b ++
        List.replicate (64 - (⟨p.n, p.k⟩ : Params).hashOutput) 0)
      (fun b => rfl) (blake2bSimdHash?_spec h hst) hL).trans
      (good_iff_validSolution _ _ _ _ hL hbound)]
    exact decoded_iff p soln _ hBL

/-- **`equihash 0.3.1`'s `is_valid_solution(200, 9, …)`** returns `Ok(())` exactly for the
    1344-byte encodings of §7.7.1-valid solutions with no repeated index, for any input. -/
theorem isValidSolution_equihash_0_3_1?_zcash (kernel : Kernel) (input nonce soln : List ℕ)
    (hin : Bytes input) (hnon : Bytes nonce) (hsoln : Bytes soln) :
    (isValidSolution_equihash_0_3_1? kernel 200 9 input nonce soln).run = some (.ok ()) ↔
      ∃ i, EncodesSolution zcashParams.toParams (bytesOf soln) i ∧
        ValidSolution Blake2b.hashFn zcashParams.toParams (bytesOf (input ++ nonce)) i ∧
          i.Nodup := by
  exact (isValidSolution_equihash_0_3_1?_correct kernel zcashParams input nonce soln hin hnon
    hsoln).trans ⟨fun ⟨_, hrest⟩ => hrest, fun hrest => ⟨by decide, hrest⟩⟩

/-- **`equihash 0.3.1`'s `is_valid_solution(48, 5, …)`**, likewise. -/
theorem isValidSolution_equihash_0_3_1?_regtest (kernel : Kernel) (input nonce soln : List ℕ)
    (hin : Bytes input) (hnon : Bytes nonce) (hsoln : Bytes soln) :
    (isValidSolution_equihash_0_3_1? kernel 48 5 input nonce soln).run = some (.ok ()) ↔
      ∃ i, EncodesSolution regtestParams.toParams (bytesOf soln) i ∧
        ValidSolution Blake2b.hashFn regtestParams.toParams (bytesOf (input ++ nonce)) i ∧
          i.Nodup := by
  exact (isValidSolution_equihash_0_3_1?_correct kernel regtestParams input nonce soln hin hnon
    hsoln).trans ⟨fun ⟨_, hrest⟩ => hrest, fun hrest => ⟨by decide, hrest⟩⟩

/-- **`equihash 0.3.1` checks the solution length for overflow.** Its `Params::new` still
    accepts `(448, 63)`, whose length 0.3.0 wraps, but `solution_bytes` is `None`, `2^63 · 8`
    overflowing a `usize`, so every solution is rejected as `InvalidParams`. -/
theorem isValidSolution_equihash_0_3_1?_448_63 (kernel : Kernel) (input nonce soln : List ℕ) :
    Params.newUnbounded? 448 63 = some ⟨448, 63⟩ ∧ Params.solutionBytes? ⟨448, 63⟩ = none ∧
      (isValidSolution_equihash_0_3_1? kernel 448 63 input nonce soln).run =
        some (.error .InvalidParams) := by
  refine ⟨rfl, rfl, ?_⟩
  unfold isValidSolution_equihash_0_3_1?
  rw [show Params.newUnbounded? 448 63 = some ⟨448, 63⟩ from rfl]
  dsimp only
  rw [indicesFromMinimal?_eq, show Params.solutionBytes? ⟨448, 63⟩ = none from rfl]
  rfl

/-- **Likewise `(520, 64)`**: `1 << 64` overflows, so `solution_indices` is `None`. -/
theorem isValidSolution_equihash_0_3_1?_520_64 (kernel : Kernel) (input nonce soln : List ℕ) :
    Params.newUnbounded? 520 64 = some ⟨520, 64⟩ ∧ Params.solutionIndices? ⟨520, 64⟩ = none ∧
      (isValidSolution_equihash_0_3_1? kernel 520 64 input nonce soln).run =
        some (.error .InvalidParams) := by
  refine ⟨rfl, rfl, ?_⟩
  unfold isValidSolution_equihash_0_3_1?
  rw [show Params.newUnbounded? 520 64 = some ⟨520, 64⟩ from rfl]
  dsimp only
  rw [indicesFromMinimal?_eq, show Params.solutionBytes? ⟨520, 64⟩ = none from rfl]
  rfl

-- The build fails if the theorems rest on anything beyond Lean's three axioms.
/--
info: 'Equihash.Verifier.isValidSolution?_correct' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isValidSolution?_correct

/--
info: 'Equihash.Verifier.isValidSolution_equihash_0_3_0?_correct' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isValidSolution_equihash_0_3_0?_correct

/--
info: 'Equihash.Verifier.isValidSolution_equihash_0_3_1?_correct' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isValidSolution_equihash_0_3_1?_correct

end Equihash.Verifier
