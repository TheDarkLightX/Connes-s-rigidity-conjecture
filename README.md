# Connes rigidity: a formal companion

This repository develops machine-checked and computational results around the
2026 counterexample reports for Connes's rigidity conjecture for ICC
property-(T) groups. Counterexamples were reported in
[OpenAI's binary-carry construction](https://cdn.openai.com/pdf/ten-proofs-oai.pdf#page=95)
and in [Shuoxing Zhou's independent construction](https://arxiv.org/abs/2608.02327).

The repository does not claim priority for those counterexamples. Its purpose
is narrower:

- formalize reusable algebraic components in Lean;
- reproduce bounded and symbolic cases with independent programs;
- explore ternary and prime-uniform extensions;
- keep proved statements separate from unreviewed proof candidates.

## Machine-checked results

The project contains 53 imported rigidity modules. The complete pinned
dependency graph passes `lake build`, and the trust audit finds no `sorry`,
`admit`, declared axioms, `unsafe` declarations, `native_decide`, or direct
`sorryAx` use in project sources.

Representative Lean theorems include:

- `groupMulEquivOfGroupAlgebraBialgEquiv`: a canonical group-algebra
  bialgebra equivalence induces an isomorphism of the underlying groups;
- `fixed_swapFirstTwo_SL3_orbit_infinite`: every nonzero first-two-symmetric
  rank-three polynomial tensor has an infinite explicit elementary orbit;
- `linear_cube_retraction_forces_frobenius_fixed`: an untwisted linear cube
  retraction forces every scalar to be fixed by cubic Frobenius;
- `ternaryShiftedCarry_nine_nsmul`: the shifted ternary carry extension has
  exponent dividing nine;
- `card_ternaryShiftedFrobeniusKernel`: the shifted-Frobenius dual kernel at
  shift `n` has cardinality `3^(3n)`;
- `prime_choose_cast_eq_zero`: every interior row-`p` binomial coefficient
  vanishes in `F_p`;
- `elementaryOne_diagonal_cancellation` and
  `elementaryTwo_diagonal_cancellation`: the ternary `e_1` and `e_2` spectral
  diagonal coefficients vanish by symmetry and characteristic three.

A green Lean build proves these statements relative to the repository's
formal definitions. It does not establish novelty or an unformalized bridge to
operator algebras.

## Exact finite and symbolic evidence

Twelve deterministic suites independently replay:

- ternary and prime Witt carry identities;
- divided-cube truncations and graded orbit spans;
- ternary kernel certificates in one, two, and three spectral variables;
- prime-rank detector and affine-chart calculations;
- binary rank-three and rank-five divided-power certificates;
- the constant-kernel `psl3` calculation;
- partition, Gaussian-multinomial, Hilbert-numerator, and Koszul-Betti
  identities for the spectral Frobenius-kernel resolution.

The spectral certificate reproduces the complete displayed Betti polynomials
for `p=2,3,5,7`. These programs establish only the identities and bounded
instances they declare.

## New structural candidate

Let

```text
S=F_p[e_1,...,e_p]
```

be the symmetric spectral ring. The new written argument proposes

```text
ker(Gamma^p(F_p^r[t]) -> F_p^r[t]^(Frob))
 ~= (e_1,...,e_(p-1))^r
    direct-sum free mixed-label spectral blocks.
```

If correct, the regular-sequence ideal supplies a prime-uniform minimal free
resolution with

```text
projective dimension = p-2,
depth = 2                     for p>=3.
```

For `p=r=3`, the candidate presentation is

```text
0 -> S(-3)^3
  -> S^7 direct-sum S(-1)^11
       direct-sum S(-2)^11 direct-sum S(-3)
  -> K_(3,3) -> 0.
```

It explains the numerator `7+11q+11q^2-2q^3` as one degree-three free
generator minus three degree-three syzygies. A further corollary identifies the
nonfree locus exactly with the Frobenius small diagonal
`V(e_1,...,e_(p-1))` and gives the closed Betti series

```text
F_mixed(q)
+ (r/z) [ product_(a=1)^(p-1)(1+z q^a) - 1 ].
```

The binomial-cancellation core is Lean checked and the Betti identities are
replayed exactly. The module decomposition, localization statement, and
minimality of the resolution are not yet Lean checked or independently
reviewed.

## Other research candidates

The research notes also propose:

1. stable-range and odd-critical cyclicity for Frobenius kernels in divided
   `p`th powers;
2. a general polynomial-tensor infinite-orbit theorem extending the checked
   rank-three case;
3. a minimal-rank prime-uniform carry construction;
4. a ternary finite-orbit invariant and common crossed-product construction;
5. a possible simplification of the published binary construction using the
   amenable radical.

The proposed prime-uniform counterexample family is not presented as complete.

Start with:

- [Public mathematical note](https://thedarklightx.github.io/Connes-s-rigidity-conjecture/)
- [Spectral Frobenius-kernel resolution](research/notes/SPECTRAL_FROBENIUS_KERNEL_RESOLUTION.md)
- [Betti series and nonfree locus](research/notes/SPECTRAL_BETTI_AND_NONFREE_LOCUS.md)
- [Spectral theorem status](docs/SPECTRAL_FROBENIUS_STATUS.md)
- [Spectral novelty audit](research/notes/SPECTRAL_FROBENIUS_NOVELTY_AUDIT.md)
- [General theorem status](docs/THEOREM_STATUS.md)
- [CI and trust status](docs/CI_STATUS.md)
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

The finite and symbolic commands are listed in
[the oracle workflow](.github/workflows/julia-experiments.yml).

## Authorship and review boundary

Dana Edwards supplied the research direction, tools, repository stewardship,
and publication decision. OpenAI language models assisted with exploration,
proof drafting, Lean repairs, experiments, and exposition. Model output is not
verification. Claim-specific status comes from the Lean kernel, deterministic
programs, cited literature, and qualified human review where available.

See [authorship and AI assistance](docs/AUTHORSHIP_AND_AI_ASSISTANCE.md).
