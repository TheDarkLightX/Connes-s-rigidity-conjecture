# Theorem status

This repository uses four evidence labels.

- **Lean checked:** the theorem and its complete imported dependency graph pass
  the pinned `lake build` and project trust audit.
- **Finite verified:** a deterministic program exhausts a stated finite domain.
- **Paper-proof candidate:** a written mathematical argument exists, but it has
  not been fully formalized or independently reviewed.
- **Open:** an essential construction or implication is still missing.

These labels are not interchangeable. In particular, a finite computation
does not prove its apparent generalization, and a green Lean build does not
prove that a theorem is novel.

## Lean-checked statements

The complete 51-module graph checks the following representative claims.

### Canonical Hopf structure reconstructs the group

`groupMulEquivOfGroupAlgebraBialgEquiv` constructs a group isomorphism from a
bialgebra equivalence between canonical group algebras. The conclusion depends
on preserving the canonical coproduct. It does not say that an arbitrary
algebra isomorphism reconstructs the group.

### A rank-three symmetric tensor has an infinite orbit

`fixed_swapFirstTwo_SL3_orbit_infinite` states that, for every field `F`, every
nonzero element of `(F[t]^3)^{⊗_F 3}` fixed by swapping the first two tensor
factors has an infinite orbit under an explicit tail of elementary
transvections in `SL_3(F[t])`.

`dividedCube_SL3_orbit_infinite` is the divided-cube corollary. These theorems
prove the rank-three critical orbit statement encoded by the repository. They
do not prove the proposed theorem in arbitrary rank and tensor degree.

### General fields require a Frobenius-aware formulation

`linear_cube_retraction_forces_frobenius_fixed` proves that an `F`-linear map
with `d(x^3) = x` for every scalar can exist only when `x^3 = x` for every
scalar. This refutes an earlier untwisted general-field formulation. It does
not construct the correctly twisted map.

### Shifted ternary carry identities

The checked chain constructs a normalized symmetric ternary carry cocycle and
proves:

- three copies of a shifted carry element equal its shifted Frobenius-dual
  fiber term;
- every shifted carry element has exponent dividing nine;
- three-torsion is characterized by the shifted Frobenius-dual kernel;
- that kernel is equivalent to three coordinates of coefficients below degree
  `n` and therefore has cardinality `3^(3n)`.

The cardinality is a coordinate-level invariant in the formal model. It becomes
an abstract group invariant only after the required characteristic-subgroup and
finite-orbit identifications are proved.

## Finite-verified statements

The CI certificate suite checks the exact bounded domains recorded in the
workflow and result files. Important examples are:

- 2,258 of 2,258 ternary total-degree kernel dimensions through degree 12;
- 444 of 444 bivariate and 304 of 304 trivariate certificate targets;
- 1,346 of 1,346 rank-five, degree-two certificates at `p = 5`;
- 120 of 120 binary rank-three certificates through degree 6;
- length-two Witt identities at `p = 2, 3, 5, 7`;
- six affine-chart boundary cases.

These are exact finite results. They are not promoted to all degrees, ranks,
or primes without a proof.

## Paper-proof candidates

The strongest candidates are:

1. cyclicity of the divided `p`th-power Frobenius kernel and full divided power
   over finite-variable polynomial rings when `r > p`, and also when `r = p`
   for odd `p`;
2. infinite elementary orbits for nonzero polynomial tensors when tensor degree
   `m < r`, with a first-two-symmetric critical case at `m = r`;
3. multivariate ternary divided-cube cyclicity;
4. the ternary finite-orbit subquotient and prime-uniform carry synthesis;
5. an amenable-radical simplification of the published binary construction.

TheoremSearch and web searches found no exact match for the first three
formulations, but a search miss is weak evidence. Priority and correctness
remain subject to specialist literature review.

## Open construction steps

The repository does not yet establish a new prime-uniform counterexample
family. The remaining chain includes:

- formalizing the general cyclicity theorem;
- formalizing the general tensor-orbit theorem;
- constructing and checking the prime-uniform functional carry and Bockstein
  interfaces;
- proving that the relevant abelian layer is characteristic in the final
  semidirect products;
- formalizing the finite-orbit identification, relative property (T), ICC, Haar
  measure, Pontryagin duality, and crossed-product bridges;
- obtaining independent specialist review and a targeted novelty audit.

## Promotion rule

A claim is presented as established by this repository only when its exact
statement has an identified evidence class. Written candidates remain
conditional premises for research. They are quarantined rather than discarded,
but they are not silently upgraded by successful examples or neighboring Lean
theorems.
