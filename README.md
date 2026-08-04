# Connes rigidity: a formal companion

This repository develops machine-checked and computational results around the
2026 counterexample reports for Connes's rigidity conjecture for ICC
property-(T) groups. Counterexamples were reported in
[OpenAI's binary-carry construction](https://cdn.openai.com/pdf/ten-proofs-oai.pdf#page=95)
and in [Shuoxing Zhou's independent construction](https://arxiv.org/abs/2608.02327).

The repository does not claim priority for those counterexamples. Its purpose
is narrower:

- formalize reusable algebraic components in Lean;
- reproduce bounded cases with independent Julia and Python programs;
- explore ternary and prime-uniform extensions;
- keep proved statements separate from unreviewed proof candidates.

## Machine-checked results

The project contains 51 imported rigidity modules. At the release candidate
head, the complete pinned dependency graph passes `lake build`, and the trust
audit finds no `sorry`, `admit`, declared axioms, `unsafe` declarations,
`native_decide`, or direct `sorryAx` use in the project sources.

Representative Lean theorems include:

- `groupMulEquivOfGroupAlgebraBialgEquiv`: a bialgebra equivalence between
  canonical group algebras induces an isomorphism of the underlying groups;
- `fixed_swapFirstTwo_SL3_orbit_infinite`: over any field, every nonzero tensor
  in `(F[t]^3)^{⊗_F 3}` fixed by swapping its first two tensor factors has an
  infinite orbit under an explicit family of elementary transvections;
- `linear_cube_retraction_forces_frobenius_fixed`: an untwisted linear cube
  retraction forces every scalar to be fixed by the cubic Frobenius map;
- `ternaryShiftedCarry_nine_nsmul`: the formal shifted ternary carry extension
  has exponent dividing nine;
- `card_ternaryShiftedFrobeniusKernel`: the formal shifted-Frobenius dual
  kernel at shift `n` has cardinality `3^(3n)`.

A green Lean build proves the stated theorems relative to the definitions in
this repository. It does not establish novelty, physical interpretation, or
the correctness of an unformalized bridge to operator algebras.

## Exact finite evidence

The finite-oracle workflow independently replays:

- ternary Witt carry identities;
- divided-cube truncations;
- total-degree ternary kernel certificates through degree 12;
- bivariate certificates through degree 3;
- trivariate certificates through degree 2;
- prime-rank detector calculations;
- affine-chart restriction ranks in six boundary cases;
- rank-five divided fifth-power certificates through degree 2;
- binary rank-three divided-square certificates through degree 6;
- prime Witt identities for `p = 2, 3, 5, 7`;
- the constant-kernel `psl3` certificate.

These programs establish only the finite instances they enumerate. Their
success is evidence for the written general arguments, not a proof of those
arguments.

## Research candidates, not established results

The research notes propose:

1. stable-range and odd-critical cyclicity for Frobenius kernels in divided
   `p`th powers;
2. a general polynomial-tensor infinite-orbit theorem extending the formal
   rank-three result;
3. a minimal-rank prime-uniform carry construction;
4. a ternary finite-orbit invariant and common crossed-product construction;
5. a possible simplification of the published binary construction using the
   amenable radical.

These claims have written arguments and selected finite checks, but most are
not yet formalized or independently reviewed. The proposed prime-uniform
counterexample family is not presented as complete.

Start with:

- [Theorem status](docs/THEOREM_STATUS.md)
- [CI and trust status](docs/CI_STATUS.md)
- [Literature and novelty audit](research/notes/LITERATURE_AND_NOVELTY_AUDIT_20260804.md)
- [Stable and critical cyclicity candidate](research/notes/STABLE_RANGE_DIVIDED_POWER_CYCLICITY.md)
- [General tensor-orbit candidate](research/notes/GENERAL_SYMMETRIC_TENSOR_ORBIT_THEOREM.md)
- [Prime-uniform synthesis](research/notes/UNIFORM_PRIME_CARRY_FAMILIES.md)

## Reproduce the formal gate

```bash
python3 scripts/audit_lean_trust.py
lake build
```

The repository pins Lean `4.30.0-rc2` and Mathlib revision
`9977002c3c9492b622fb469b0d18acc7e73aed3e`.

The GitHub workflows also replay the finite certificate suite. Exact commands
and bounded domains are visible in
[the finite-oracle workflow](.github/workflows/julia-experiments.yml).

## Authorship and review boundary

Dana Edwards supplied the research direction, tools, repository stewardship,
and publication decision. OpenAI language models assisted with exploration,
proof drafting, Lean repairs, experiments, and exposition. Model output is not
verification. Claim-specific status comes from the Lean kernel, deterministic
finite programs, cited literature, and, where available, qualified human
review.

See [authorship and AI assistance](docs/AUTHORSHIP_AND_AI_ASSISTANCE.md).
