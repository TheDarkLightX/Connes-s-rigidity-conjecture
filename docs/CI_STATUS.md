# Standalone Lean CI status

## Toolchain

- Repository: `TheDarkLightX/Connes-s-rigidity-conjecture`
- Branch: `agent/import-lean-rigidity-research-20260804`
- Command: `lake build`
- Lean: `4.30.0-rc2`
- Mathlib revision: `9977002c3c9492b622fb469b0d18acc7e73aed3e`

## Initial standalone audit

The first dedicated-repository build, workflow run `30894406560`, failed in eleven modules. That result corrected the earlier assumption that incremental source-workspace runs established the final imported dependency graph.

Initial failures:

1. `TernaryPrimitiveArithmetic`
2. `TernaryTruncatedInvariant`
3. `TernaryWittCarry`
4. `TernaryReducedPolynomial`
5. `ExponentSeparation`
6. `ExactGroupLike`
7. `FinsuppGroupLike`
8. `SupportOrbitCore`
9. `ApproximateGroupLike`
10. `HopfRoundingEquiv`
11. `AbelianCocycleExtension`

## Last completed build frontier

Workflow run `30900303939`, testing research commit `55030c1f9e644921e4b284739ea34abefd103697`, reduced the failures to six:

1. `TernaryReducedDegree`
2. `TernaryPrimitiveCount`
3. `GroupAlgebraHopfBridge`
4. `TernaryWittExtension`
5. `PolynomialTensorCubeBasis`
6. `SingleShiftOrbit`

That run successfully built the repaired generic cocycle extension, reduced-polynomial foundation, scalar Witt carry, exact and approximate group-like coefficient kernels, Hopf rounding, support separation, and the first all-distinct orbit layers.

## Repairs present after the last completed build

The current branch contains additional repairs not covered by run `30900303939`:

- `SingleShiftOrbit.singleShiftTerm` is explicitly noncomputable because it uses `Finsupp.embDomain`.
- `TernaryWittExtension` proves the exponent-nine identity through the fiber homomorphism and the characteristic-three base coordinate.
- `GroupAlgebraHopfBridge` handles the zero coproduct coefficient case explicitly.
- `TernaryReducedDegree` uses explicit recursive hypotheses and factor-quotient degree statements rather than brittle simplification.
- `TernaryPrimitiveCount` replaces unsupported `omega` power reasoning with explicit power decompositions.
- `PolynomialTensorCubeBasis` now reindexes monomial tensor bases explicitly and states basis vectors as polynomial monomials.

A fresh complete build is required before any of these are promoted.

## Promotion rule

No headline theorem depending transitively on a failing or unaudited module is considered promoted. Every repair requires:

1. a focused module build;
2. a full clean `lake build`;
3. a theorem-dependency review;
4. correction of stale website or repository claims;
5. separate disclosure when `native_decide` supplies finite compiler-checked evidence rather than a small kernel-only derivation.

The failing runs remain part of the public audit trail rather than being replaced by partial green targets.
