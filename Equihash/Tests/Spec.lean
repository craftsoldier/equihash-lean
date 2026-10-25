/-
The specification on two real blocks (`zakura-equihash 4.0.0`, `src/test_vectors/zcash.rs`):
Zcash mainnet block 415000 (lines 5–44, `n = 200, k = 9`) and the Regtest genesis block
(lines 50–61, `n = 48, k = 5`). Each solution is valid, and its bytes are its encoding.

§5.4.1.11 takes bits of the BLAKE2b output without saying in which order; `Spec.lean` reads
each byte most significant bit first. The mainnet block is valid read that way, and not the
other.
-/
import Equihash

open Equihash Equihash.Spec Equihash.Verifier

/-! ## Evaluating the specification

Each condition quantifies over a bounded range, so it can be decided by computing. -/

instance (H : HashFn) (p : Spec.Params) (S : List Byte) (i : List ℕ) :
    Decidable (GeneralizedBirthday H p S i) := by
  unfold GeneralizedBirthday; infer_instance

instance (H : HashFn) (p : Spec.Params) (S : List Byte) (i : List ℕ) :
    Decidable (CollisionCondition H p S i) := by
  unfold CollisionCondition HasLeadingZeros; infer_instance

instance (p : Spec.Params) (i : List ℕ) : Decidable (OrderingCondition p i) := by
  unfold OrderingCondition; infer_instance

instance (H : HashFn) (p : Spec.Params) (S : List Byte) (i : List ℕ) :
    Decidable (ValidSolution H p S i) :=
  decidable_of_iff (i.length = 2 ^ p.k ∧ (∀ j ∈ i, 1 ≤ j ∧ j ≤ p.N) ∧
      GeneralizedBirthday H p S i ∧ CollisionCondition H p S i ∧ OrderingCondition p i)
    ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

instance (p : Spec.Params) (s : List Byte) (i : List ℕ) : Decidable (EncodesSolution p s i) := by
  unfold EncodesSolution; infer_instance

/-! ## The blocks -/

/-- The bytes a hexadecimal string denotes. -/
def hex (s : String) : List ℕ :=
  let digits := s.toList.map fun c => (Char.toNat c - if c ≤ '9' then 48 else 87)
  (List.range (digits.length / 2)).map fun i => 16 * digits[2 * i]! + digits[2 * i + 1]!

/-- The `m` indices a solution holds, `w` bits each (`I2BEBSP_w(i_j − 1)`), most significant
    bit first (§7.7.1). -/
def indicesOf (w m : ℕ) (solution : List ℕ) : List ℕ :=
  let bits := solution.flatMap fun b => (List.range 8).map fun j => b / 2 ^ (7 - j) % 2
  (List.range m).map fun j => ((bits.drop (w * j)).take w).foldl (2 * · + ·) 0 + 1

/-- Zcash's parameters: `n = 200`, `k = 9`. -/
def zcash : Spec.Params := ⟨200, 9, by decide, by decide, by decide, by decide, by decide⟩

/-- Regtest's parameters: `n = 48`, `k = 5`. -/
def regtest : Spec.Params := ⟨48, 5, by decide, by decide, by decide, by decide, by decide⟩

/-- Mainnet block 415000's header up to the nonce (lines 5–9). -/
def blockHeader : List ℕ := hex (String.join [
    "040000005274b43b9e4ad8f43e93f78463d24dcfe531aeb4719819f4f97f7e0300000000663073bc4bfa95c9",
    "bec36aad7268a573049797bdfc5aa4c743fbe4820aa393ce0000000000000000000000000000000000000000",
    "000000000000000000000000a8becc5be1ab031c"])

/-- Its nonce (lines 11–12). -/
def blockNonce : List ℕ := hex "c2fd607c776a7a0000000000000000000000000000000000000000003eb21819"

/-- The block header up to the nonce, then the nonce. -/
def powheader : List Byte := bytesOf (blockHeader ++ blockNonce)

/-- The block's solution, minimally encoded (lines 15–44). -/
def solution : List ℕ := hex (String.join [
    "00949d55de0cc633e0cce41e4649ef4aa3349f0100290ffe281b947b3b53fbd2f35b1ce292649b96ac6e0883",
    "af3a6844b95592e74556da344b4701961cd4130c68219cfa1341d5afb5049eb0e8be4a2d92d678c40785e337",
    "05548b5f3a54f0a4c39a2f58ee784a24163cd86f54812327df55e1d55ca84b6e7b887a7cbfb9091a585bdb8e",
    "a4759307c56c1b3dafc669245a6f654b6f730052266a01ad4f9c0b59ed4e17712b3e72df0498aa8de4888f99",
    "3531c60acded1d4b66e89de0b6482cccd4a712f5cf9d4ca83be0f922de2c1dbb3a1407480dbe8795993d8be6",
    "40988abfe7a8a1b33a12131c451e1abc0d83fb851862c637ce724d5fe97aa9a806cf34bab509f4554b0cd10a",
    "7ddfd5821b091ad2c90c1aa1d81eb3d72db41993b648f41e2138ff9531a30ff73b22140e4ebd7baa33848e51",
    "2d99300c5c131c6e75f5714a5c6dcb178b4a4978dac83ad412fbd692019250c553049aad457984bedfc96ae7",
    "01c659bc7007a97d0a9002b945bdec45a945ef6285b2cd553b4c09d907c627863f0399e8725b4ff7fc5979e3",
    "cff22814508448ef8b9831c285959333396aa362a51cf205097afabec15e41fb6e30b622374bf58b37ef9d1b",
    "241ead5a682b98b65749a57568e238d50afd417e1e960e7b5a064fd9f694d783a2cbcd58552dedbb9e5e1123",
    "674ef73a524196cf05d3e524660549ffe7bd6568057135ffd5afd943f6da11cbb597e8ccecd77ecbe909de06",
    "31bfa29cd3e3d5544671ba80256153d6e9990b88ad8e0cf4989bef4be457f9c7b0f1aacd6e0ef320605c29ed",
    "0cd2eb6cfce216c52a317580201cad7a0943d24b7b06d5bf758761dd96e11970b5ded697222b2c77e7f256a6",
    "05ac755549c1651f25adfc9d53d9117e3a0bb409eee4a600120472949c7dda1c2edb3c330c7f961799829164",
    "57d331e96309dd24df74eedd00e7db497ee130f77de666eb557fb316e87adaf1813ce426a458a6eee3a85b2a",
    "b88f6553aadae8de652e211a1d9f334d596b5eb6173407efcc2e8154bb9ca1212aa9a1a1121d2f5a7712cf25",
    "cc8148b8052e0d2e09f20e5ba2a98277e975b0eed9a89206966337163f215c9d04a6598b0958d333d846773c",
    "69e5abfd0a0427f3660614dd82b79adb851a0d58b62df5f0b3ac836e6e25f3a51f49a99ade57796fe9fcc26f",
    "0a1f94ff0819fe52b75087edbed3a81626eb5416c66557f11c0fcedff223d6aa8cd5c35386e5b4b95a0f0392",
    "ca301a38b3687d094493b9e9d264d07a190ce57d116804382a3fabe15af4df4fa043f0287aa1ed5568d9ef5d",
    "12510d010ccdab4eb616f6df13bb3126ef43d9d65735e4e4c04b576348d040b535055a3d5ae191b75f0612f3",
    "b24066a05245f27fe57bda66bd6dec7e4fc9cb236802062adde3cd0e313482c92a0c721102b1f38b015ab8d0",
    "1559cbcb40f674e9efad5ee9c2fe133faa55ca1dd0ff26710f9da819cc1459cb7ed260dad3db0596258d47c7",
    "4c32a8b852b671c5a0caa2001603d90c91a7df2e2d4ee9ae9bf1a6b1ec88151c62360d03024d2e2d0114084f",
    "6b88c5bba24aa7cecfac16e91e0baf3d8653e218093e81d2a63c32eff1d9030f9e1414ece420daa24e0dd5b8",
    "45b3274bb839ca1c53bcc0194242d74b2631b9495a654fbbdcbfad779f7322b60736249880604821d96924e3",
    "fa397f354a5ecca34f614da5456f9b36338c37d8f6fbf626be983477766022872746da10a1771ceb02dd8aac",
    "01ba186bf1488630479e1284da0190fce8b59ac6b0fd416bee56b72f0a5845153557ff0f4950a0dc5be65ce9",
    "42d22e18534c4e0efabb2d1525dc4858b9b0f77d474a125ebc250e08fedbfaa66f453d90932cab3ff4522190",
    "9968e51e6bc254d509adeb75cba76d48fe024e3e66d8df5e"])

/-- The Regtest genesis header up to the nonce (lines 50–54). -/
def regtestHeader : List ℕ := hex (String.join [
    "040000000000000000000000000000000000000000000000000000000000000000000000db4d7a85b768123f",
    "1dff1d4c4cece70083b2d27e117b4ac2e31d087988a5eac40000000000000000000000000000000000000000",
    "000000000000000000000000dae5494d0f0f0f20"])

/-- Its nonce (lines 56–57). -/
def regtestNonce : List ℕ := hex "0900000000000000000000000000000000000000000000000000000000000000"

/-- Its solution, minimally encoded (lines 59–61). -/
def regtestSolution : List ℕ :=
  hex "01936b7db1eb4ac39f151b8704642d0a8bda13ec547d54cd5e43ba142fc6d8877cab07b3"

/-! ## The checks -/

-- Valid, reading BLAKE2b's output most significant bit first, as `Spec.lean` does.
#guard decide (ValidSolution Blake2b.hashFn zcash powheader (indicesOf 21 512 solution))

-- Its bytes are the encoding of its indices.
#guard decide (EncodesSolution zcash (bytesOf solution) (indicesOf 21 512 solution))

-- The Regtest genesis block: valid, and its bytes are its encoding.
#guard decide (ValidSolution Blake2b.hashFn regtest (bytesOf (regtestHeader ++ regtestNonce))
  (indicesOf 9 32 regtestSolution))
#guard decide (EncodesSolution regtest (bytesOf regtestSolution) (indicesOf 9 32 regtestSolution))

-- §7.7.1's own example: indices beginning `69, 42, 2^21` encode to bytes beginning
-- `0, 2, 32, 0, 10, 127, 255`.
#guard bitsOfBytes (bytesOf [0, 2, 32, 0, 10, 127, 255]) =
  ([69, 42, 2 ^ 21].flatMap fun j => I2BEBSP 21 (j - 1)).take 56

/-- Byte `b` with its bits reversed. -/
def reverseBits (b : ℕ) : ℕ := (List.range 8).foldl (fun acc j => 2 * acc + b / 2 ^ j % 2) 0

/-- BLAKE2b with each output byte's bits reversed: reading it most significant bit first reads
    BLAKE2b least significant bit first. -/
def leastSignificantFirst : HashFn := fun p x =>
  (Blake2b.hashFn p x).map fun b => BitVec.ofNat 8 (reverseBits b.toNat)

-- Not valid, reading it least significant bit first.
#guard !decide (ValidSolution leastSignificantFirst zcash powheader (indicesOf 21 512 solution))
