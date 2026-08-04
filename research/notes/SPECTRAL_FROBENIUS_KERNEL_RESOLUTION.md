# Spectral decomposition and the Frobenius-kernel resolution

**Status:** complete paper-proof candidate with a deterministic symbolic
certificate. The decomposition is not yet formalized in Lean or independently
reviewed. No priority claim is made.

This note gives an exact structural explanation for the Hilbert series that
appeared in the ternary carry program. The key point is that the divided
`p`th power has two independent structures:

1. the current-group action on the coordinate labels; and
2. a commuting action of the symmetric polynomial ring in the `p` spectral
   variables.

The Frobenius diagonal is supported on a codimension-`p-1` spectral curve. Its
kernel is therefore not merely a large cyclic current-group module: over the
spectral ring it is a direct sum of free mixed-label sectors and `r` copies of
one regular-sequence ideal. This produces an explicit minimal free resolution.

## 1. Setup

Let `p` be prime and let

```text
k = F_p,
U = k^r,
V = U tensor_k k[t],
P = k[t_1,...,t_p],
S = P^(S_p) = k[e_1,...,e_p].
```

The elementary symmetric polynomial `e_j` has degree `j`. All tensor products
below are over `k`.

The symmetric group acts diagonally on

```text
V^tensor-p = U^tensor-p tensor_k P
```

by permuting tensor positions and the corresponding spectral variables. Put

```text
Gamma^p(V) = (V^tensor-p)^(S_p).
```

Over the prime field, the interpolation argument in
`STABLE_RANGE_DIVIDED_POWER_CYCLICITY.md` identifies this with the span of pure
powers. The decomposition below, however, is a statement about the invariant
space itself and does not depend on that interpolation step.

## 2. Coordinate-multiset decomposition

A coordinate tuple

```text
(i_1,...,i_p) in {1,...,r}^p
```

has a multiplicity partition

```text
lambda = (lambda_1 >= ... >= lambda_l > 0),
sum lambda_a = p.
```

Let

```text
H_lambda = S_(lambda_1) x ... x S_(lambda_l)
```

be the stabilizer of a tuple with those multiplicities. If
`a_s(lambda)` is the number of parts of `lambda` equal to `s`, then the number
of coordinate multisets of type `lambda` is

```text
m_(r,lambda)
  = (r!/(r-l)!)/product_s a_s(lambda)! .              (2.1)
```

For one coordinate orbit, diagonal invariants are canonically equivalent to
`P^(H_lambda)`: choose a representative coordinate tuple and recover every
other coordinate block by simultaneous permutation of its labels and spectral
variables. Consequently there is an exact graded `S`-module decomposition

```text
Gamma^p(V)
  ~= direct-sum_(lambda partition p, length(lambda)<=r)
       (P^(H_lambda))^(m_(r,lambda)).                  (2.2)
```

This uses only the orbit decomposition of the permutation basis. It does not
use semisimplicity of the modular `S_p`-representation.

### Proof of the orbit block

Fix a representative tuple `i` with stabilizer `H`. Its coordinate-orbit
subspace is the induced permutation module on `S_p/H`, with one copy of `P`
at each coset. An invariant family is determined by its value `f` at the
representative, and invariance under the stabilizer requires `f in P^H`.
Conversely, such an `f` extends uniquely by

```text
f_(sigma.i) = sigma.f.
```

This construction is `S=P^(S_p)`-linear and gives the desired equivalence.

## 3. Freeness and the Gaussian-multinomial numerator

For a proper multiplicity partition, every part of `lambda` is strictly less
than `p`. Hence `p` does not divide `|H_lambda|`. Averaging over `H_lambda`
shows that `P^(H_lambda)` is a direct summand of `P` as an `S`-module.
Since `P` is free over the symmetric polynomial ring `S`, the summand is
projective; graded Quillen--Suslin then makes it free.

Its Hilbert numerator over `S` is the Gaussian multinomial

```text
C_lambda(q)
 = product_(j=1)^p (1-q^j)
   / product_(a=1)^l product_(j=1)^(lambda_a) (1-q^j).
                                                               (3.1)
```

Thus

```text
Hilb(Gamma^p(V);q)
 = B_(p,r)(q)/product_(j=1)^p (1-q^j),               (3.2)
```

where

```text
B_(p,r)(q)
 = sum_lambda m_(r,lambda) C_lambda(q).               (3.3)
```

At `q=1`,

```text
B_(p,r)(1)=r^p,                                       (3.4)
```

because the rank contribution of a coordinate multiset with stabilizer `H`
is `[S_p:H]`, and these cosets count all ordered coordinate tuples.

Equation (3.4) is the spectral rank expected for the global-Weyl-type tensor
model. It is distinct from the dimension of the constant-degree divided power.

## 4. The spectral diagonal lemma

For a symmetric polynomial `f in S`, define its diagonal extraction by

```text
Delta(f)
 = sum_(n>=0) coefficient(f,t_1^n ... t_p^n) tau^n
   in k[tau].                                         (4.1)
```

The crucial identity is

```text
Delta(e_j f)=0                 for 1<=j<p,
Delta(e_p f)=tau Delta(f).                            (4.2)
```

Indeed, the coefficient of `t_1^n...t_p^n` in `e_j f` is the sum over all
`j`-element subsets `J` of the coefficient of `f` at the exponent vector that
is `n-1` on `J` and `n` elsewhere. Symmetry of `f` makes all these coefficients
equal. There are `binom(p,j)` of them, and

```text
binom(p,j)=0 in F_p,        1<=j<p.
```

The second identity is simply simultaneous exponent shift by one.

Since `S=k[e_1,...,e_p]`, (4.2) proves that `Delta` is exactly the quotient
homomorphism

```text
epsilon:S -> k[tau],
e_j |-> 0      (j<p),
e_p |-> tau.                                          (4.3)
```

In particular,

```text
ker Delta = I_p := (e_1,...,e_(p-1)).                 (4.4)
```

This elementary coefficient-counting lemma is the source of the entire
homological structure below.

## 5. Exact form of the Frobenius diagonal

Let

```text
d_p:Gamma^p(V) -> V^(Frob)
```

be the Frobenius diagonal, with the target graded so that `t^n e_i` has
spectral degree `pn`. On a coordinate orbit with at least two distinct labels,
`d_p` is zero. On each of the `r` all-same-label blocks, whose spectral module
is `S`, it is the quotient (4.3).

Therefore

```text
coker-free block:  S -> S/I_p ~= k[tau],
mixed-label blocks: sent to zero.                    (5.1)
```

Let

```text
K_(p,r)=ker d_p.
```

Combining (2.2) and (5.1) gives the exact decomposition

```text
K_(p,r)
 ~= I_p^r
    direct-sum
    direct-sum_(lambda != (p))
      (P^(H_lambda))^(m_(r,lambda)).                  (5.2)
```

The second summand is graded free over `S`. All nonfreeness is concentrated in
`r` copies of the regular-sequence ideal `I_p`.

The Hilbert numerator is consequently

```text
K_(p,r)(q)
 = B_(p,r)(q)
   - r product_(j=1)^(p-1)(1-q^j).                   (5.3)
```

The quotient has spectral codimension `p-1`, so it has rank zero over `S`.
Hence

```text
rank_S K_(p,r)=rank_S Gamma^p(V)=r^p.                (5.4)
```

## 6. Minimal free resolution

The generators `e_1,...,e_(p-1)` form a homogeneous regular sequence in `S`.
The ideal `I_p` therefore has the truncated Koszul resolution. Write `S(-d)`
for a free generator in degree `d`.

For homological degree `j>=1`, put

```text
F_j
 = [ direct-sum_(J subset {1,...,p-1}, |J|=j+1)
       S(-sum_(a in J) a) ]^r,                       (6.1)
```

for `1<=j<=p-2`. The degree-zero module is

```text
F_0
 = F_mixed
   direct-sum
   [ direct-sum_(a=1)^(p-1) S(-a) ]^r,              (6.2)
```

where `F_mixed` is the free module supplied by all partitions
`lambda!=(p)` in (5.2). Then

```text
0 -> F_(p-2) -> ... -> F_1 -> F_0 -> K_(p,r) -> 0    (6.3)
```

is a minimal graded free resolution.

Consequences:

```text
p=2:   K_(2,r) is S-free,
p>=3:  projective-dimension_S K_(p,r)=p-2,
p>=3:  depth_S K_(p,r)=2.                            (6.4)
```

The top Ext group recovers the Frobenius spectral curve:

```text
Ext_S^(p-2)(K_(p,r),S)
 ~= (S/I_p)^r,                                       (6.5)
```

up to the standard grading shift

```text
1+2+...+(p-1)=p(p-1)/2.
```

Thus the Frobenius quotient leaves a canonical homological fingerprint in its
kernel even though the kernel has the same generic spectral rank as the whole
divided power.

## 7. Ternary specialization

Take `p=r=3`. The coordinate multiplicity types are

```text
(3):       3 blocks with stabilizer S_3,
(2,1):     6 blocks with stabilizer S_2,
(1,1,1):   1 block with trivial stabilizer.           (7.1)
```

Let `P=k[x,y,z]` and `S=k[e_1,e_2,e_3]`.

For a `(2,1)` block,

```text
P^(S_2)=S[z]
```

with free basis

```text
1,z,z^2.                                              (7.2)
```

For the all-distinct block, the standard Artin basis can be taken as

```text
1,z,z^2,y,yz,yz^2,                                   (7.3)
```

with degrees `0,1,2,1,2,3`. Therefore

```text
Gamma^3(F_3^3[t])
 ~= S^10 direct-sum S(-1)^8
    direct-sum S(-2)^8 direct-sum S(-3).              (7.4)
```

Its Hilbert numerator is

```text
10+8q+8q^2+q^3.                                      (7.5)
```

The Frobenius kernel has the minimal presentation

```text
0 -> S(-3)^3
  -> S^7 direct-sum S(-1)^11
       direct-sum S(-2)^11 direct-sum S(-3)
  -> K_(3,3) -> 0.                                   (7.6)
```

Hence

```text
Hilb(K_(3,3);q)
 = (7+11q+11q^2-2q^3)
   / ((1-q)(1-q^2)(1-q^3)).                          (7.7)
```

The previously unexplained negative coefficient is now forced:

```text
+q^3 from a free all-distinct spectral generator,
-3q^3 from the three Koszul syzygies.                 (7.8)
```

So the coefficient `-2` is not a sign of a mistaken dimension count. It is a
homological signature of the three Frobenius-diagonal sectors.

## 8. Binary rank-three specialization

For `p=2,r=3`,

```text
S=k[e_1,e_2],
I_2=(e_1)
```

is principal. The formula gives

```text
Gamma^2(F_2^3[t]) ~= S^6 direct-sum S(-1)^3,
K_(2,3)            ~= S^3 direct-sum S(-1)^6.        (8.1)
```

Thus the binary rank-three Frobenius kernel is spectrally free. The sharp
change from `p=2` to odd primes is therefore not only the availability of
antisymmetrization in the cyclicity proof: it is also the transition from a
principal Frobenius ideal to a higher-codimension regular sequence.

## 9. Geometric interpretation

The ring `S` is the coordinate ring of the symmetric product

```text
Sym^p(A^1).
```

The quotient

```text
S/I_p = k[e_p]
```

is the Frobenius small diagonal. In characteristic `p`, the monic polynomial
with `p` equal roots is

```text
(T-a)^p=T^p-a^p,
```

so all intermediate elementary symmetric coordinates vanish. The map `d_p`
is restriction of the all-same-label spectral sector to this Frobenius curve.

Equation (5.2) says that the kernel consists of:

1. functions vanishing on the Frobenius curve in each all-same-label sector;
2. every mixed-label sector, which the diagonal map cannot see at all.

This geometric picture explains why the quotient is small while the kernel
retains full generic rank.

## 10. Relation to current and global Weyl modules

Classical current-algebra work realizes global Weyl modules indexed by
multiples of the first fundamental weight inside tensor-polynomial modules and
studies their freeness over symmetric polynomial rings. The free rank `r^p`
and the spectral action above are compatible with that portal.

The new conclusion is more specific: the Frobenius kernel is generally not a
free global-Weyl-type module over the same spectral ring. For every `p>=3`, it
has projective dimension `p-2` and depth two. This supplies a rigorous
falsifier for any identification that would force spectral freeness.

A precise positive-characteristic identification of `Gamma^p(U[t])` with a
hyper/current global Weyl module remains a separate representation-theoretic
obligation. The decomposition and resolution above do not require that
identification.

## 11. Interaction with cyclicity

There is no contradiction between

```text
K_(p,r)=span_k(E_r(k[t]).w)
```

and the large minimal number of `S`-module generators in (6.2). The current
group and the spectral ring are different commuting sources of operations. A
single current-group orbit can cross many coordinate-multiplicity sectors that
remain distinct under spectral multiplication alone.

The resolution therefore provides a new strategy for formalizing cyclicity:

1. prove generation on the free mixed-label summands;
2. prove that the same orbit reaches the `e_1,...,e_(p-1)` generators in each
   all-same-label ideal;
3. check compatibility with the Koszul syzygies rather than reducing arbitrary
   tensor expressions directly.

Whether this shortens the stable/critical induction remains open.

## 12. Deterministic certificate

The script

```text
experiments/spectral_frobenius_resolution.py
```

enumerates partitions, Gaussian multinomials, coordinate-orbit
multiplicities, the Frobenius quotient numerator, and the complete Koszul
Betti polynomials. It checks:

```text
B_(p,r)(1)=r^p,
alternating-sum(F_j)=K_(p,r)(q),
```

for the declared prime/rank cases and reproduces (7.5)--(7.7) and (8.1).
The script verifies the combinatorial and Hilbert-series consequences, not the
module isomorphisms themselves.

## 13. Novelty boundary

The following ingredients are classical or close to classical:

- the freeness of a polynomial ring over symmetric polynomials;
- Young-subgroup invariant rings and Gaussian multinomials;
- Koszul resolutions of regular-sequence ideals;
- global Weyl modules over symmetric spectral algebras;
- the need for a Frobenius twist in characteristic `p`.

The possible new contribution is the assembled theorem identifying the
Frobenius-diagonal map on every coordinate-multiplicity sector and deriving the
explicit prime-uniform resolution (6.3), especially its use as a structural
input to the rigidity carry program. Searches performed on 4 August 2026 found
nearby divided-power and global-Weyl literature but no exact match for this
kernel decomposition or its Betti table. A search miss is not evidence of
priority.

Before using novelty language, seek review from specialists in strict
polynomial functors, modular invariant theory, and global Weyl modules.
