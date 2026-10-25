import Lake
open Lake DSL

/-- Mathlib `v4.35.0`, at its commit. -/
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "56a005855ea17e0b0958f73ec801ae140b0a1679"

package «equihash» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

@[default_target] lean_lib «Equihash» {}

/-- The specification, the verifier, each release and BLAKE2b on real data. -/
@[default_target] lean_lib «Tests» where
  roots := #[`Equihash.Tests.Spec, `Equihash.Tests.Verifier, `Equihash.Tests.Releases,
    `Equihash.Tests.Blake2b]
