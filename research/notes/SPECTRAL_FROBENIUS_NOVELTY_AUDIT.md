# Spectral Frobenius-kernel novelty audit

**Date:** 4 August 2026  
**Status:** targeted but incomplete literature audit. Search misses are not
priority evidence.

## 1. Candidate contribution being audited

The candidate theorem is the exact graded decomposition

```text
ker(Gamma^p(F_p^r[t]) -> F_p^r[t]^(Frob))
 ~= (e_1,...,e_(p-1))^r
    direct-sum free mixed-label spectral blocks,
```

followed by the truncated-Koszul minimal resolution over

```text
S=F_p[e_1,...,e_p].
```

The distinctive consequences are:

```text
projective dimension p-2 and depth 2 for p>=3,
```

and, at `p=r=3`,

```text
0 -> S(-3)^3
  -> S^7 + S(-1)^11 + S(-2)^11 + S(-3)
  -> K_(3,3) -> 0.
```

## 2. Clearly classical ingredients

No novelty claim should attach to the following facts by themselves:

1. `F_p[t_1,...,t_p]` is free over its symmetric polynomial subring.
2. Coordinate tuples decompose according to Young-subgroup stabilizers.
3. Proper Young-subgroup invariant rings have Gaussian-multinomial Hilbert
   numerators.
4. `(e_1,...,e_(p-1))` is a homogeneous regular-sequence ideal.
5. Its minimal resolution is the truncated Koszul complex.
6. Divided powers and Frobenius twists are standard positive-characteristic
   polynomial functors.

## 3. Global Weyl and invariant-theory neighborhood

Chari and Loktev identify isotypical components of global Weyl modules with
natural polynomial subspaces and use the classical freeness of
`A_p` over `A_p^(S_p)`:

- Vyjayanthi Chari and Sergey Loktev,
  *An application of global Weyl modules of sl_(n+1)[t] to invariant theory*,
  <https://arxiv.org/abs/1104.4048>.

Their earlier work constructs PBW-type bases for current-algebra Weyl modules:

- Vyjayanthi Chari and Sergey Loktev,
  *Weyl, Fusion and Demazure modules for the current algebra of sl_(r+1)*,
  <https://arxiv.org/abs/math/0502165>.

Chari, Fourier, and Khandai give a categorical account of global and local Weyl
modules and their tensor behavior:

- Vyjayanthi Chari, Ghislain Fourier, and Tanusree Khandai,
  *A categorical approach to Weyl modules*,
  <https://arxiv.org/abs/0906.2014>.

These sources make the symmetric spectral ring and freeness portal classical.
The current candidate differs by isolating the Frobenius-diagonal quotient and
computing the kernel's complete free resolution.

## 4. Modular divided-power neighborhood

A very recent paper directly studies the infinite-variable divided-power
algebra in positive characteristic and its Frobenius-twist structure:

- Karthik Ganapathy,
  *GL-algebras in positive characteristic III: the divided power algebra*,
  <https://arxiv.org/abs/2608.00982>.

Its public abstract establishes that the area is active and that Frobenius
layers are central. The abstract alone is insufficient to determine whether the
finite-degree spectral kernel decomposition here is already present in another
language. The full paper requires specialist comparison before priority claims.

The strict-polynomial literature also treats divided powers and Frobenius
twists as separate functors; it should be searched by exact functor and Ext
language rather than only by the phrase "Frobenius diagonal."

## 5. Search outcome

Queries combining the following terms did not return an exact match:

```text
Frobenius diagonal + divided power kernel,
Gamma^p + Frobenius twist + exact sequence,
global Weyl module + p omega_1 + Frobenius kernel,
divided power kernel + projective resolution + symmetric polynomials.
```

The searches found global-Weyl freeness, modular Weyl-module homomorphisms,
strict-polynomial Frobenius theory, and general divided-power work. They did not
surface the exact decomposition

```text
I_p^r direct-sum free mixed-label sectors
```

or the resulting Betti table.

This is weak evidence only. Terminology may differ substantially across
strict-polynomial functors, Schur algebras, current hyperalgebras, and modular
invariant theory.

## 6. Current assessment

The safest description is:

> **A plausible new structural lemma or repackaging:** an elementary assembly of
> coordinate-orbit invariant theory, a characteristic-`p` diagonal coefficient
> cancellation, and a Koszul resolution, developed for the rigidity carry
> program.

Do not presently describe it as the first such resolution.

## 7. Required expert comparison

Before a priority statement, ask specialists to compare the result with:

1. exact sequences between `Gamma^p`, symmetric powers, and Frobenius twists in
   strict polynomial functors;
2. modular Schur/Weyl module resolutions at highest weight `p omega_1`;
3. global Weyl modules over their highest-weight polynomial algebras;
4. Young-permutation module decompositions in modular invariant theory;
5. current hyperalgebra filtrations and Frobenius kernels.
