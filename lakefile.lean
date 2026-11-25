import Lake
open Lake DSL

/-- Mathlib `v4.36.0`, at its commit. -/
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "fc4f59e577feb1a4956671bc04ac18aaaf8cd842"

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
