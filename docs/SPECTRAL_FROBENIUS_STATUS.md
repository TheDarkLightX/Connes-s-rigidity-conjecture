# Spectral Frobenius-kernel theorem status

## Claim

For `k=F_p`, `V=k^r tensor k[t]`,

```text
P=k[t_1,...,t_p],
S=P^(S_p)=k[e_1,...,e_p],
K_(p,r)=ker(Gamma^p(V) -> V^(Frob)),
```

the coordinate-multiset decomposition gives

```text
K_(p,r)
 ~= (e_1,...,e_(p-1))^r
    direct-sum
    direct-sum_(lambda != (p))
      (P^(H_lambda))^(m_(r,lambda)).
```

The mixed-label summand is graded free over `S`. The regular-sequence ideal
supplies a minimal free resolution of length `p-2` when `p>=3`.

## Evidence classes

### Lean checked arithmetic core

The complete formal graph checks:

- `prime_choose_cast_eq_zero`: for prime `p` and `0<j<p`, the cast of
  `p.choose j` to `ZMod p` is zero;
- `prime_choose_mul_eq_zero`: the corresponding scalar multiple vanishes;
- `elementaryOne_diagonal_cancellation`: the ternary `e_1` diagonal
  coefficient is zero for every symmetric coefficient family;
- `elementaryTwo_diagonal_cancellation`: the ternary `e_2` coefficient is
  zero;
- `elementaryThreeDiagonalCoefficient_succ`: the `e_3` sector shifts all three
  exponents together.

These results certify the characteristic arithmetic behind the spectral
quotient. They do not establish the invariant-module decomposition.

### Paper-proof candidate

The repository contains a complete written module argument in
`research/notes/SPECTRAL_FROBENIUS_KERNEL_RESOLUTION.md` and derived
homological consequences in
`research/notes/SPECTRAL_BETTI_AND_NONFREE_LOCUS.md`.

The candidate consequences include:

```text
projective dimension p-2 and depth 2 for p>=3,
nonfree locus V(e_1,...,e_(p-1)),
```

and the closed Betti generating function

```text
F_mixed(q)
+ (r/z) [ product_(a=1)^(p-1)(1+z q^a) - 1 ].
```

### Exact symbolic certificate

The script `experiments/spectral_frobenius_resolution.py` checks:

- coordinate-orbit multiplicities;
- Gaussian-multinomial numerators;
- spectral ranks;
- Frobenius-quotient numerators;
- every subset-indexed Koszul Betti polynomial;
- the complete alternating-sum identity.

The archived result reproduces the declared cases `p=2,3,5,7` and records the
workflow artifact digest.

### Not yet checked

No Lean theorem currently establishes:

- the invariant-block module equivalence;
- freeness and the precise shifted basis of every Young-subgroup block;
- the global kernel decomposition;
- the localization/nonfree-locus statement;
- exactness and minimality of the full free resolution.

The candidate has not received independent specialist review.

## Ternary consequence

For `p=r=3`, the candidate presentation is

```text
0 -> S(-3)^3
  -> S^7 direct-sum S(-1)^11
       direct-sum S(-2)^11 direct-sum S(-3)
  -> K_(3,3) -> 0.
```

It yields

```text
Hilb(K_(3,3);q)
 = (7+11q+11q^2-2q^3)
   / ((1-q)(1-q^2)(1-q^3)).
```

The coefficient `-2` is explained by one degree-three free generator and three
degree-three syzygies.

## Binary boundary

For `p=2`, the ideal `(e_1)` is principal. The kernel is spectrally free, the
nonfree locus is empty, and the positive-degree Ext statement used for odd
primes does not apply.

## Promotion obligations

1. Formalize the coordinate-orbit equivalence
   `invariants of an induced block ~= P^H`.
2. Lift the checked coefficient cancellation from its arithmetic model to the
   symmetric polynomial ring and the actual Frobenius diagonal.
3. Construct the Young-subgroup free bases or import an adequate invariant-ring
   theorem.
4. Formalize the truncated Koszul resolution and its minimality.
5. Formalize the localization criterion and exact nonfree locus.
6. Obtain strict-polynomial/global-Weyl and modular-invariant-theory review.
7. Run a targeted priority search before using the word "novel" without a
   qualifier.
