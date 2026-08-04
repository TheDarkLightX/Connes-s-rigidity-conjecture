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

## Evidence class

**Paper-proof candidate.** The repository contains a complete written argument
in `research/notes/SPECTRAL_FROBENIUS_KERNEL_RESOLUTION.md`.

**Exact symbolic certificate.** The script
`experiments/spectral_frobenius_resolution.py` checks the partition
multiplicities, Gaussian-multinomial numerators, spectral ranks, quotient
numerators, and all Koszul-Betti alternating sums in the declared cases.

**Not Lean checked.** No Lean theorem currently establishes the invariant-block
module equivalence, the diagonal coefficient lemma, or the minimality of the
resolution.

**Not independently reviewed.** The decomposition uses classical ingredients,
but its exact assembly and claimed application to the rigidity program require
specialist review.

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

## Promotion obligations

1. Formalize the coordinate-orbit equivalence
   `invariants of an induced block ~= P^H`.
2. Formalize the diagonal coefficient identities
   `Delta(e_j f)=0` for `j<p` and `Delta(e_p f)=tau Delta(f)`.
3. Construct the Young-subgroup free bases or import an adequate invariant-ring
   theorem.
4. Formalize the truncated Koszul resolution and its minimality.
5. Obtain strict-polynomial/global-Weyl and modular-invariant-theory review.
6. Run a targeted priority search before using the word "novel" without a
   qualifier.
