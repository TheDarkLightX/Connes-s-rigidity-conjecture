import Lake
open Lake DSL

package "connes_rigidity" where
  version := v!"0.1.0"
  keywords := #["mathematics", "lean", "operator-algebras", "group-theory"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
  ]

require "leanprover-community" / "mathlib"

@[default_target]
lean_lib «LeanMathlib» where
