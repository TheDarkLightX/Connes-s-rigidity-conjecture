# Connes's Rigidity Conjecture — Formal Research Program

This repository is the canonical public home for Lean formalizations,
adversarial audits, and ternary generalizations related to Connes's rigidity
conjecture and the OpenAI/Codex counterexample program. A binary-carry
counterexample architecture is publicly claimed in
[Chapter 4 of *Ten Advances in Mathematics and Theoretical Computer Science*](https://cdn.openai.com/pdf/ten-proofs-oai.pdf#page=95);
an [independent action-shear counterexample by Shuoxing Zhou](https://arxiv.org/abs/2608.02327)
is also public. A [1 August adversarial manuscript](https://philarchive.org/rec/NIEWTC)
disputes both, but its public abstract describes different groups and does not
presently identify a flaw in either construction. This project does not claim
priority for the disproof or its shared measured-action mechanism.

The standalone project currently contains **51 rigidity research modules**,
finite Julia/Python oracles, a public proof-status site, and replayable research
notes. The original 49 modules were migrated from the Lean development merged
into `TheDarkLightX/MathLib` at commit
`f77f93d03e678a490f67e7b9fd419471a5d67c23`.

## New mathematical proof candidates (2026-08-04)

- A stable/critical divided-power theorem. Over every
  `F_p[t₁,…,t_d]`, the divided `p`th-power Frobenius kernel and whole module
  are cyclic in every rank `r>p`, and also on the odd critical diagonal `r=p`.
  This includes binary rank three and every odd prime at rank `p`.
- A general polynomial-tensor orbit theorem: for tensor degree `m<=r`, every
  nonzero tensor has infinite elementary orbit when `r>m`; at `r=m`, symmetry
  in the first two factors suffices. The existing formal rank-three theorem is
  one instance.
- A uniform minimal-rank carry program on `r_p=max(p,3)`. It combines binary
  rank-three fresh-coordinate algebra with the `1/12` chart detector, and odd
  rank-`p` critical algebra with primitive detectors. The proposed intrinsic
  cardinal is `p^(r_p n)`.
- Exact length-two Witt carry exhaustion at `p=2,3,5,7`, including the cocycle,
  Teichmüller coordinate, exponent `p²`, and multiplication-by-`p` formula.
- A complete proof candidate that the ternary divided-cube Frobenius kernel is
  cyclic under `E₃(F₃[t])`, using a finite difference that cancels the quadratic
  divided-power term.
- A corollary that the whole divided cube is cyclic from one pure cube.
- A multivariate extension of both cyclicity statements to every
  `F₃[t₁,…,t_d]`, with independent bivariate and trivariate orbit checks.
- A strengthened formal orbit theorem for every nonzero tensor fixed by the
  first-two-factor swap, not only divided cubes.
- A canonical exact sequence whose finite-orbit subgroup recovers the shift
  parameter with size `3^(3n)`; classical higher-rank lattice theory promotes
  it to an abstract semidirect-product invariant once the Bockstein model is
  constructed.
- A ternary specialization of the published product-Haar/Fourier mechanism,
  giving common group von Neumann algebras and common full and reduced group
  C*-algebras at paper-proof level.
- Paper proofs of finite generation and ICC for the resulting semidirect
  products, conditional on the installed dual-extension construction.
- A shift-forgetting quotient whose Pontryagin dual embeds `G_0` in `G_n` with
  index `3^(3n)`, making the ternary candidate family mutually commensurable.
- A measure-theoretic relative-property-(T) proof candidate: a joint ternary
  detector gives the sharper `1/8` escape bound, contradicting the
  Cornulier–Tessera failure criterion after property-(T) invariantization.
- A two-geometry prime--rank detector theorem. Primitive boxes give
  `c_prim(p,r)=((p-1)/p^2-p^(1-r))/(1-p^(1-r))`, positive exactly when
  `(p-1)p^(r-3)>1`; affine charts give
  `c_chart(p,r)=(r-p)(p-1)/(rp^2)` when `p<r`. Together they cover every prime in
  every rank `r>=3`, recover Zhou's binary rank-three constant `1/12`, and
  recover the ternary rank-three constant `1/8`. An exact block-restriction
  oracle verifies the sharp `r-p` chart count in six boundary cases.
- A candidate simplification of the published binary proof: use
  `SL_4(F_2[t])` directly and recover the abelian layer as the amenable radical,
  eliminating the auxiliary torsion-free congruence-kernel acting group. The
  published orbit extension and `1/7` detector also prove ICC and relative
  property (T) directly, making factor transfer optional for those properties.
- A formal scalar obstruction showing why the cubic diagonal over a general
  characteristic-three field needs a Frobenius twist.

See [the cyclicity proof](research/notes/DIVIDED_CUBE_CYCLICITY_PROOF.md),
[the consolidated discovery packet](research/notes/DISCOVERY_PACKET_20260804.md),
[the stable/critical cyclicity theorem](research/notes/STABLE_RANGE_DIVIDED_POWER_CYCLICITY.md),
[the general tensor-orbit theorem](research/notes/GENERAL_SYMMETRIC_TENSOR_ORBIT_THEOREM.md),
[the uniform prime carry synthesis](research/notes/UNIFORM_PRIME_CARRY_FAMILIES.md),
[the multivariate extension](research/notes/MULTIVARIATE_DIVIDED_CUBE_CYCLICITY.md),
[the finite-orbit invariant](research/notes/FINITE_ORBIT_INVARIANT_PROOF.md),
[the common crossed-product proof](research/notes/COMMON_CROSSED_PRODUCT_PROOF.md),
[the relative-property-(T) proof](research/notes/RELATIVE_PROPERTY_T_PROOF.md),
[the prime--rank detector phase diagram](research/notes/PRIME_RANK_DETECTOR_PHASE_DIAGRAM.md),
[the binary amenable-radical simplification](research/notes/BINARY_AMENABLE_RADICAL_SIMPLIFICATION.md),
[the adversarial status audit](research/notes/ADVERSARIAL_STATUS_AUDIT_20260804.md),
and [the Frobenius correction](research/notes/FROBENIUS_TWIST_CORRECTION.md).

## Main research directions

- Reconstruction of a group from the group-like elements of its canonical group-algebra Hopf structure.
- Quantitative approximate group-like and Hopf-rounding results.
- A rank-three infinite-orbit program for divided cubes over polynomial rings.
- Ternary length-two Witt carries and shifted abelian cocycle extensions.
- Frobenius-diagonal and multiplication-by-three identities.
- A ternary degree-three minimum-support argument.
- Primitive-vector, dual-shift-kernel, and proposed distinguishing-invariant arithmetic.

## Validation status

The first complete standalone `lake build` exposed errors in eleven imported
modules; successive repairs reduced the latest remote failure set to six. The
current local repair batch addresses all six and awaits clean remote CI. The
repository therefore treats the files as a **research formalization program**,
not as a blanket set of completed Lean proofs.

- [Standalone CI status](docs/CI_STATUS.md)
- [Theorem status and promotion rules](docs/THEOREM_STATUS.md)
- [Research roadmap](docs/RESEARCH_ROADMAP.md)
- [Migration provenance](docs/PROVENANCE.md)
- [Authorship and AI assistance](docs/AUTHORSHIP_AND_AI_ASSISTANCE.md)

The failing full build is intentionally visible. No headline theorem depending on a failing module is promoted until its complete dependency chain builds and receives specification review.

## Claim boundary

This repository does **not claim a first or independently validated
counterexample to Connes's rigidity conjecture**. OpenAI's binary-carry family
and Zhou's independent action-shear pair are public claims; a current
adversarial manuscript remains unresolved. The prime-uniform and ternary
results here remain unreviewed proof candidates until their interfaces are
formalized and independently checked.

## Build

```bash
lake build
```

The repository pins the Lean and Mathlib dependency graph used by the source development.
