# Standalone Lean CI status

## Latest complete audit

- Repository: `TheDarkLightX/Connes-s-rigidity-conjecture`
- Branch: `agent/import-lean-rigidity-research-20260804`
- Audited branch commit: `f4512cf05c0c704f3bb301333080c1fc9bf1d32e`
- Workflow run: `30894406560`
- Command: `lake build`
- Lean: `4.30.0-rc2`
- Mathlib revision: `9977002c3c9492b622fb469b0d18acc7e73aed3e`
- Result: **failed**

## Failing modules reported by Lake

1. `LeanMathlib.Rigidity.TernaryPrimitiveArithmetic`
2. `LeanMathlib.Rigidity.TernaryTruncatedInvariant`
3. `LeanMathlib.Rigidity.TernaryWittCarry`
4. `LeanMathlib.Rigidity.TernaryReducedPolynomial`
5. `LeanMathlib.Rigidity.ExponentSeparation`
6. `LeanMathlib.Rigidity.ExactGroupLike`
7. `LeanMathlib.Rigidity.FinsuppGroupLike`
8. `LeanMathlib.Rigidity.SupportOrbitCore`
9. `LeanMathlib.Rigidity.ApproximateGroupLike`
10. `LeanMathlib.Rigidity.HopfRoundingEquiv`
11. `LeanMathlib.Rigidity.AbelianCocycleExtension`

## Failure classes

The log shows several categories rather than one common packaging error:

- renamed or unavailable Mathlib lemmas;
- typeclass inference failures in recursively defined structures;
- proof scripts that leave goals unsolved;
- rewrite direction and extensionality failures;
- field-notation errors in the generic cocycle extension;
- arithmetic normalization failures over `ZMod 3`.

## Promotion rule

No headline theorem depending transitively on a failing module is considered promoted. Repairs should proceed in dependency order, with every repair accompanied by:

1. a focused module build;
2. a full `lake build`;
3. a theorem-dependency review;
4. removal of any stale claim in documentation.

The failing CI is intentionally retained as an audit signal rather than replaced by a partial green build.
