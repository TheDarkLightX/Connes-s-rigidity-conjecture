# Connes's Rigidity Conjecture — Formal Research Program

This repository is the canonical public home for Lean formalizations, adversarial audits, and new mathematics related to Connes's rigidity conjecture and the OpenAI/Codex counterexample program.

The standalone project currently contains **49 rigidity research modules** migrated from the Lean development merged into `TheDarkLightX/MathLib` at commit `f77f93d03e678a490f67e7b9fd419471a5d67c23`.

## Main research directions

- Reconstruction of a group from the group-like elements of its canonical group-algebra Hopf structure.
- Quantitative approximate group-like and Hopf-rounding results.
- A rank-three infinite-orbit program for divided cubes over polynomial rings.
- Ternary length-two Witt carries and shifted abelian cocycle extensions.
- Frobenius-diagonal and multiplication-by-three identities.
- A ternary degree-three minimum-support argument.
- Primitive-vector, dual-shift-kernel, and proposed distinguishing-invariant arithmetic.

## Validation status

The first complete standalone `lake build` exposed errors in eleven imported modules. The repository therefore treats the imported files as a **research formalization program**, not as a blanket set of completed Lean proofs.

- [Standalone CI status](docs/CI_STATUS.md)
- [Theorem status and promotion rules](docs/THEOREM_STATUS.md)
- [Research roadmap](docs/RESEARCH_ROADMAP.md)
- [Migration provenance](docs/PROVENANCE.md)

The failing full build is intentionally visible. No headline theorem depending on a failing module is promoted until its complete dependency chain builds and receives specification review.

## Claim boundary

This repository does **not yet claim a completed new counterexample to Connes's rigidity conjecture**.

## Build

```bash
lake build
```

The repository pins the Lean and Mathlib dependency graph used by the source development.
