/-
# Zcash Equihash Verifier: verified in Lean

* `Spec.lean`: Equihash as the Zcash protocol specification defines it (§7.7.1, §5.4.1.11).
* `Verifier/`: Zcash's Equihash verifiers (`zakura-equihash 4.0.0`, `equihash 0.3.0`), in Lean.
* `Proofs/`: the Equihash verifiers accept exactly the valid solutions with no repeated index.
-/
module

public import Equihash.Spec
public import Equihash.Verifier.Recursive
public import Equihash.Verifier.Releases
public import Equihash.Proofs.Recursive
public import Equihash.Proofs.Releases
