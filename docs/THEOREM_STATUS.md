# Theorem status

This repository separates three distinct states:

- **Present:** a theorem statement and proof term exist in the repository.
- **Builds:** the module compiles in the current standalone project.
- **Promoted:** the full dependency chain builds and the mathematical specification has been reviewed as matching the intended claim.

A theorem must satisfy all three conditions before this repository presents it as an established result.

## Current standalone validation

The first complete standalone `lake build` on the dedicated repository failed. The build reported errors in these eleven modules:

- `AbelianCocycleExtension`
- `ApproximateGroupLike`
- `ExactGroupLike`
- `ExponentSeparation`
- `FinsuppGroupLike`
- `HopfRoundingEquiv`
- `SupportOrbitCore`
- `TernaryPrimitiveArithmetic`
- `TernaryReducedPolynomial`
- `TernaryTruncatedInvariant`
- `TernaryWittCarry`

Because several of these are foundational dependencies, downstream modules are **not promoted** merely because their source files are present. See [CI status](CI_STATUS.md).

Incremental source-branch CI runs had compiled many individual kernels, but they do not substitute for a green build of the final imported dependency graph. The dedicated repository's full build is the current source of truth.

## Research claims represented by the imported modules

The repository contains formalization attempts and partially validated proof chains for:

- reconstruction of a group from canonical group-algebra group-like elements;
- bialgebra reconstruction and quantitative Hopf rounding;
- rank-three divided-cube orbit growth under polynomial transvections;
- ternary Witt carries and shifted abelian extensions;
- Frobenius-diagonal and multiplication-by-three identities;
- a ternary degree-three minimum-support argument;
- primitive-vector, dual-shift-kernel, and proposed finite-invariant arithmetic.

These are research targets, not blanket publication claims, until their exact standalone dependency chains are green and independently reviewed.

## Still open at the construction level

- A completed family of pairwise nonisomorphic ICC property-(T) groups with isomorphic group von Neumann algebras.
- The complete spectral-measure/property-(T) transfer.
- The intrinsic finite-conjugacy invariant in the final groups.
- Pontryagin-dual, Haar-measure, crossed-product, and spatial von Neumann-algebra bridges.
- Common complex group rings and full/reduced group C*-algebras for the final family.
