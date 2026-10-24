/-
Leaves: a node for one index holds §5.4.1.11's hash value for it. What `initialise_state`,
`generate_hash` and `Node::new` compute, in terms of `Spec`.
-/
module

public import Equihash.Verifier.Verify
public import Equihash.Proofs.Params
public import Equihash.Proofs.Minimal
public import Equihash.Proofs.Digits

@[expose] public section

namespace Equihash.Verifier

open Equihash Equihash.Spec

/-! ## Bytes -/

/-- Rust bytes as the specification's bytes. -/
abbrev bytesOf (l : List ℕ) : List Byte := l.map (BitVec.ofNat 8)

/-- Every element is a byte, as every element of a Rust `[u8]` is. -/
def Bytes (l : List ℕ) : Prop := ∀ b ∈ l, b < 256

theorem map_toNat_bytesOf {l : List ℕ} (h : Bytes l) : (bytesOf l).map BitVec.toNat = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left fun b hb => by simp [Nat.mod_eq_of_lt (h b hb)]

theorem Bytes.append {l₁ l₂ : List ℕ} (h₁ : Bytes l₁) (h₂ : Bytes l₂) : Bytes (l₁ ++ l₂) :=
  fun b hb => (List.mem_append.mp hb).elim (h₁ b) (h₂ b)

theorem bytes_u32ToLeBytes (x : ℕ) : Bytes (u32ToLeBytes x) := by
  intro b hb
  simp only [u32ToLeBytes, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> exact Nat.mod_lt _ (by norm_num)

theorem bytes_blake2b (outLen : ℕ) (personal input : List ℕ) :
    Bytes (Blake2b.blake2b outLen personal input) := by
  intro b hb
  simp only [Blake2b.blake2b, List.mem_ofFn] at hb
  obtain ⟨i, rfl⟩ := hb
  exact Nat.mod_lt _ (by norm_num)

theorem bytes_toNat (l : List Byte) : Bytes (l.map BitVec.toNat) := by
  intro b hb
  obtain ⟨x, -, rfl⟩ := List.mem_map.mp hb
  exact x.isLt

/-! ## Hashing -/

/-- A BLAKE2b state for §5.4.1.11's `BLAKE2b-(n·m)`, personalized by `powtag`, that has
    absorbed the bytes `S`. -/
def StateFor (p : Spec.Params) (S : List Byte) (st : Blake2b.State) : Prop :=
  st.params.hashLength = (genHashParams p).len ∧
  st.params.personal = (powtag p).map BitVec.toNat ∧
  bytesOf st.input = S ∧ Bytes st.input

/-- `update` absorbs more bytes. -/
theorem StateFor.update {p : Spec.Params} {S : List Byte} {st : Blake2b.State}
    (h : StateFor p S st) (x : List ℕ) (hx : Bytes x) :
    StateFor p (S ++ bytesOf x) (st.update x) := by
  obtain ⟨hl, hp, hS, hb⟩ := h
  exact ⟨hl, hp, by simp [Blake2b.State.update, ← hS], hb.append hx⟩

/-- `generate_hash(state, g)`: §5.4.1.11's `T`, the hash of everything absorbed followed by
    `powcount(g)`. -/
theorem generateHash_eq {p : Spec.Params} {S : List Byte} {st : Blake2b.State}
    (h : StateFor p S st) (g : ℕ) :
    generateHash st g = (Blake2b.hashFn (genHashParams p) (S ++ powcount g)).toList.map
      BitVec.toNat := by
  obtain ⟨hl, hp, hS, hb⟩ := h
  simp only [generateHash, Blake2b.State.update, Blake2b.State.finalize, Blake2b.hashFn,
    List.Vector.toList_mk]
  rw [map_toNat_bytesOf (bytes_blake2b _ _ _), hl, hp, ← hS, powcount, ← u32ToLeBytes_eq,
    ← List.map_append, map_toNat_bytesOf (hb.append (bytes_u32ToLeBytes g))]
  rfl

/-- `initialise_state(n, k, n·m/8)`: a BLAKE2b state for §5.4.1.11's `BLAKE2b-(n·m)`,
    personalized by `powtag`, that has absorbed nothing. -/
theorem initialiseState?_spec {rp : Params} {p : ZakuraParams} (h : rp.Is p) :
    ∃ st, initialiseState? rp.n rp.k rp.hashOutput = some st ∧ StateFor p.toParams [] st := by
  have hlen := genHashParams_len_pos p.toParams
  have hlen' := genHashParams_len_le p.toParams
  have hpow : (powtag p.toParams).map BitVec.toNat =
      BLAKE2B_PERSONALIZATION_PREFIX ++ u32ToLeBytes p.n ++ u32ToLeBytes p.k := by
    simp only [powtag, ← u32ToLeBytes_eq, List.map_append, map_toNat_bytesOf
      (bytes_u32ToLeBytes _)]
    rfl
  simp only [genHashParams] at hlen hlen'
  refine ⟨⟨⟨p.n * p.m / 8, (powtag p.toParams).map BitVec.toNat⟩, []⟩, ?_,
    rfl, rfl, rfl, fun b hb => by simp at hb⟩
  rw [hpow]
  simp [initialiseState?, Blake2b.Params.new, Blake2b.Params.hashLength?,
    Blake2b.Params.personal?, Params.hashOutput_eq h, h.1, h.2, Blake2b.outBytes,
    Blake2b.personalBytes, BLAKE2B_PERSONALIZATION_PREFIX, u32ToLeBytes, hlen,
    show p.n * p.m / 8 ≤ 64 from hlen', Blake2b.Params.toState]

/-! ## Leaves -/

/-- §5.4.1.11's bit slice `T_{h+1 .. h+n}` lies on byte boundaries when `n = 8q`: `X_{i+1}`
    is the bits of bytes `(i mod m)·q .. (i mod m)·q + q` of BLAKE2b output `⌊i/m⌋`. -/
theorem X_succ_eq (H : HashFn) (p : Spec.Params) (S : List Byte) (i q : ℕ) (hq : p.n = 8 * q) :
    X H p S (i + 1) = bitsOfBytes ((((H (genHashParams p) (S ++ powcount (i / p.m))).toList).drop
      ((i % p.m) * q)).take q) := by
  simp only [X, equihashGen, Nat.add_sub_cancel]
  rw [hq, show i % p.m * (8 * q) = 8 * (i % p.m * q) by ring, bitsOfBytes_drop, bitsOfBytes_take]

/-- `expand_array`'s result, read as digits of the input's bits. -/
theorem expandedN_of_expand (vin : List ℕ) (hvin : Bytes vin) (c w : ℕ) (out : List ℕ)
    (hlen : out.length = 8 * vin.length / c * w)
    (hall : ∀ s < 8 * vin.length / c, ∀ x < w, out[s * w + x]? =
      some (beByte w (digit c vin.length (prefixVal vin vin.length) s) x)) :
    ExpandedN c w out (bitsOfBytes (bytesOf vin)) := by
  have hB : (bitsOfBytes (bytesOf vin)).length = 8 * vin.length := by
    simp [length_bitsOfBytes]
  have hV : prefixVal vin vin.length = bitsVal (bitsOfBytes (bytesOf vin)) := by
    rw [bitsVal_bitsOfBytes, map_toNat_bytesOf hvin, prefixVal, List.take_of_length_le le_rfl]
  refine ⟨by simp [hlen, hB], fun t ht x hx => ?_⟩
  rw [hB] at ht
  have hfit : (t + 1) * c ≤ 8 * vin.length :=
    le_trans (Nat.mul_le_mul_right c ht) (Nat.div_mul_le_self _ _)
  rw [hall t ht x hx, hV, digit_eq_digitVal _ _ _ _ hB hfit]

/-- **`Node::new`**: a leaf holding index `i` and the expansion of §5.4.1.11's `X_{i+1}`
    (the hash value of 0-based index `i`) over everything the state absorbed. -/
theorem Node.new?_spec {rp : Params} {p : ZakuraParams} (h : rp.Is p) {S : List Byte}
    {st : Blake2b.State} (hst : StateFor p.toParams S st) (i : ℕ) :
    ∃ node, Node.new? rp st i = some node ∧ node.indices = [i] ∧
      ExpandedN p.digitBits ((p.digitBits + 7) / 8) node.hash
        (X Blake2b.hashFn p.toParams S (i + 1)) := by
  have hc8 : 8 ≤ p.digitBits := p.digit_ge
  have hc24 : p.digitBits ≤ 24 := p.digit_le
  -- The parameters: `n = 8q`, and the `q·m`-byte BLAKE2b output.
  obtain ⟨q, hq⟩ := p.n_dvd_8
  have hm1 : 1 ≤ p.m := one_le_m p.toParams
  have hiq : i % p.m * (8 * q) / 8 = i % p.m * q := by
    rw [show i % p.m * (8 * q) = 8 * (i % p.m * q) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  have ha : (i % p.m) * q + q ≤ q * p.m := by
    have := Nat.mul_le_mul_right q (Nat.mod_lt i (by omega : 0 < p.m))
    rw [Nat.succ_mul] at this; linarith [Nat.mul_comm p.m q]
  -- The hash: `q·m` bytes.
  set T := generateHash st (i / p.m) with hT
  have hTeq := generateHash_eq hst (i / p.m)
  have hTlen : T.length = q * p.m := by
    rw [hT, hTeq, List.length_map, List.Vector.toList_length]
    simp only [genHashParams, hq]
    rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
  have hTb : Bytes T := by rw [hT, hTeq]; exact bytes_toNat _
  -- The leaf's bytes: `(i mod m)·q .. (i mod m)·q + q`.
  set bytes := (T.drop (i % p.m * q)).take q with hbytes
  have hbl : bytes.length = q := by simp [hbytes, hTlen]; omega
  have hbb : Bytes bytes := fun b hb => hTb b (List.mem_of_mem_drop (List.mem_of_mem_take hb))
  -- Their expansion.
  have hdiv : p.digitBits ∣ 8 * bytes.length := by
    rw [hbl, ← hq]; exact ⟨p.k + 1, by rw [n_eq p.toParams]; ring⟩
  obtain ⟨out, hout, hlen, hall⟩ := expandArray?_spec bytes hbb p.digitBits 0 hc8 (by omega) hdiv
  have hw : divCeil p.digitBits 8 + 0 = (p.digitBits + 7) / 8 := by
    rw [Nat.add_zero, divCeil_eq _ _ (by norm_num)]; rfl
  rw [hw] at hlen hall
  refine ⟨⟨out, [i]⟩, ?_, rfl, ?_⟩
  · have hsl : slice? T (i % p.m * q) (i % p.m * q + q) = some bytes := by
      rw [slice?_eq T _ _ (by omega) (by omega), Nat.add_sub_cancel_left]
    simp only [Node.new?, Params.indicesPerHashOutput_eq h, h.1, ← hT, hq, hiq,
      show 8 * q / 8 = q by omega, hsl, Params.collisionBitLength_eq h, hout, Option.pure_def,
      Option.bind_eq_bind, Option.bind_some]
  · have hE := expandedN_of_expand bytes hbb _ _ out hlen hall
    -- Those bytes are §5.4.1.11's `X_{i+1}`.
    rwa [hbytes, hT, hTeq, ← List.map_drop, ← List.map_take, bytesOf, List.map_map,
      show BitVec.ofNat 8 ∘ BitVec.toNat = id from funext fun x => by simp, List.map_id,
      ← X_succ_eq _ _ _ _ q hq] at hE

end Equihash.Verifier
