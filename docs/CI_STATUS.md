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

## Latest complete remote audit

Workflow run `30903123149`, testing commit `a8b232bc582c88a5e5ab6ac16e75f78dbe52184a`, reduced the standalone failure frontier to four modules:

1. `LeanMathlib.Rigidity.GroupAlgebraHopfBridge`
2. `LeanMathlib.Rigidity.PolynomialTensorCubeBasis`
3. `LeanMathlib.Rigidity.TernarySupportRecurrence`
4. `LeanMathlib.Rigidity.TernaryWittCoordinate`

That run successfully built the newer repairs to `SingleShiftOrbit`, `TernaryWittExtension`, `TernaryReducedDegree`, and `TernaryPrimitiveCount`, along with the earlier repaired dependency layers. The failing run remains part of the public audit trail.

## Local repair and research batch awaiting CI

The current worktree preserves the remote proofs that passed and replaces the four failing modules with targeted repairs. It also adds the strengthened first-two-symmetric orbit theorem, a Frobenius scalar obstruction, prime-rank detector experiments, exact finite-orbit certificates, and the accompanying discovery and novelty-audit packets.

The batch removes every use of `native_decide` under `LeanMathlib/`. It has passed local syntax, JSON, finite-linear-algebra, exact-oracle, and diff checks. Two dependency-minimized targets also build against the pinned toolchain:

- `LeanMathlib.Rigidity.DetectorTransfer`, including the corrected `3/8` spectral arithmetic and the `1/12`, `1/8`, and `4/45` chart constants;
- `LeanMathlib.Rigidity.FrobeniusTwistObstruction`.

The full graph could not be rebuilt locally because 6,284 Mathlib cache objects returned HTTP 502. These focused successes do not replace the full gate. The batch is **not promoted** until a new clean remote `lake build` succeeds.

## Promotion rule

No headline theorem depending transitively on a failing or unaudited module is considered promoted. Every repair requires:

1. a focused module build;
2. a full clean `lake build`;
3. a theorem-dependency review;
4. correction of stale website or repository claims;
5. separate disclosure if a future proof uses finite compiler-checked evidence rather than a small kernel-only derivation.
