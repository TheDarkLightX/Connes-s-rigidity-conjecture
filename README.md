# Connes's Rigidity Conjecture — Formal Research Program

This repository is the canonical public home for Lean formalizations, adversarial audits, and new mathematics related to Connes's rigidity conjecture and the OpenAI/Codex counterexample program.

The standalone project currently contains **49 Lean modules** migrated from the Lean development merged into `TheDarkLightX/MathLib` at commit `f77f93d03e678a490f67e7b9fd419471a5d67c23`.

## Main formalized directions

- Exact reconstruction of a group from the group-like elements of its canonical group-algebra Hopf structure.
- Quantitative approximate group-like and Hopf-rounding results.
- A rank-three infinite-orbit theorem for divided cubes over polynomial rings.
- Ternary length-two Witt carries and shifted abelian cocycle extensions.
- Frobenius-diagonal and multiplication-by-three identities.
- An internal Lean proof of the ternary degree-three minimum-support bound.
- Primitive-vector, dual-shift-kernel, and proposed distinguishing-invariant arithmetic.

## Claim boundary

This repository does **not yet claim a completed new counterexample to Connes's rigidity conjecture**. The formalized sub-results and remaining obligations are separated in:

- [Theorem status](docs/THEOREM_STATUS.md)
- [Research roadmap](docs/RESEARCH_ROADMAP.md)
- [Provenance](docs/PROVENANCE.md)

## Build

```bash
lake build
```

The repository pins the Lean and Mathlib dependency graph used by the source development.
