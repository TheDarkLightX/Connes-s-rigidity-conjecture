# A uniform prime-indexed carry program

**Status:** consolidated complete paper-proof candidate modulo the explicitly
listed operator-algebra/formalization interfaces. The carry/common-factor and
finite-orbit architecture is published binary prior art. The possible new
content is the minimal-rank prime-uniform synthesis, especially the binary
rank-three carry family and the odd-prime cyclicity/orbit theorems. No novelty
or correctness priority is claimed without expert review.

## 1. The minimal-rank phase line

For every prime `p`, set

```text
r_p=max(p,3),
k=F_p,
R=k[t],
V=R^(r_p),
Gamma=SL_(r_p)(R)=E_(r_p)(R).
```

This choice simultaneously resolves three otherwise unrelated thresholds.

| prime | rank | cyclicity mechanism | orbit mechanism | detector |
|---:|---:|---|---|---|
| 2 | 3 | fresh coordinate (`r>p`) | fresh coordinate (`r>p`) | affine charts, `1/12` |
| odd `p` | `p` | critical two-source difference | critical symmetric tail | primitive boxes |

Thus the lone zero of the primitive detector, `(p,r)=(2,3)`, is exactly filled
by affine charts, while the lone unsupported critical cyclicity corner,
`(p,r)=(2,2)`, is avoided by property-(T) rank.

## 2. Algebraic input

Put

```text
B=Gamma^p(V)=(V^tensor-p)^(S_p),
d_p:B->V,             d_p(v^tensor-p)=v,
K=ker d_p.
```

The stable/critical cyclicity theorem proves

```text
K=k[Gamma].[e_1,...,e_p],
B=k[Gamma].e_1^tensor-p.                              (2.1)
```

The stable/critical orbit theorem proves

```text
every nonzero element of B, hence of K, has infinite Gamma-orbit. (2.2)
```

Both statements work over multivariate polynomial rings at the cyclicity
level; the one-variable ring is retained here for the shifted finite quotient
`V/t^nV`.

## 3. The universal length-two Witt carry

For `a,c in F_p`, let

```text
C_p(a,c)
 = (a^p+c^p-(a+c)^p)/p mod p
 = -sum_(j=1)^(p-1) (binom(p,j)/p) a^j c^(p-j).       (3.1)
```

The integer coefficients are well-defined because `p` divides
`binom(p,j)`. The operation

```text
(a,b)+(c,d)=(a+c,b+d+C_p(a,c))                       (3.2)
```

is the additive group of `W_2(F_p)`. The Teichmuller coordinate

```text
phi_p(a,b)=a^p+p b mod p^2                            (3.3)
```

identifies it with `Z/p^2`, and

```text
p(a,b)=(0,a).                                         (3.4)
```

The exact oracle `experiments/prime_witt_exhaustive.py` exhausts
normalization, symmetry, the cocycle law, associativity, (3.3), (3.4), and an
element of order `p^2` for `p=2,3,5,7`. Equations (3.1)--(3.4) themselves are
general polynomial identities; the exhaustion is a regression oracle.

## 4. Functional and shifted carries

Let

```text
L=Hom_k(V,k),       Q=Hom_k(B,k)
```

with their product topologies. Because pure powers span `B`, there is a unique
functional carry

```text
c(ell,m)(v^tensor-p)=C_p(ell(v),m(v)).                (4.1)
```

Existence can also be read directly from (3.1): it is the corresponding
linear combination of symmetrized tensors in `ell` and `m`. Equality on all
pure powers proves normalization, symmetry, and the cocycle identity.

For `n>=0`, define

```text
T_n ell(v)=ell(t^n v),
c_n(ell,m)=c(T_n ell,T_n m),
(ell,q)+_n(m,s)=(ell+m,q+s+c_n(ell,m)).                (4.2)
```

This makes the fixed compact carrier `L x Q` into a compact abelian group
`E_n`. Since every `g in Gamma` is `R`-linear, `T_n` commutes with the dual
action and the coordinate formula

```text
g.(ell,q)=(ell composed with g^(-1),q composed with Gamma^p(g^(-1))) (4.3)
```

is an automorphism for every `n`, independent of `n`.

Evaluating the scalar formula (3.4) on every pure power gives

```text
p(ell,q)=(0,h),
h(b)=ell(t^n d_p(b)).                                  (4.4)
```

Thus the compact multiplication-by-`p` map and its discrete Bockstein are
identified without a coordinate guess.

## 5. The discrete groups and their invariant

Let

```text
A_n=dual(E_n),
G_(p,n)=A_n semidirect Gamma.
```

Duality and (4.4) give

```text
0 -> V -> A_n -> B -> 0,
beta_n=t^n d_p.                                       (5.1)
```

For any exponent-`p^2` extension of exponent-`p` groups, the Bockstein gives
the canonical exact sequence

```text
0 -> V/im(beta_n) -> A_n[p]/pA_n -> ker(beta_n) -> 0.
```

Here this is

```text
0 -> V/t^nV -> A_n[p]/pA_n -> K -> 0.                 (5.2)
```

The left term is finite of order

```text
|V/t^nV|=p^(r_p n),                                   (5.3)
```

while every nonzero element in the right term has infinite orbit by (2.2).
Therefore the finite-orbit subgroup of the canonical subquotient in (5.2) is
exactly `V/t^nV`.

The group `Gamma` is a higher-rank lattice with property (T). Its center is
trivial on the minimal-rank line:

- for `p=2`, `F_2^x={1}`;
- for odd `p` and `r_p=p`, a scalar `lambda I` in `SL_p` satisfies
  `lambda^p=1`, while `lambda^p=lambda` in `F_p`, so `lambda=1`.

Margulis's normal-subgroup theorem then gives `Rad_am(Gamma)=1`, hence

```text
Rad_am(G_(p,n))=A_n.                                  (5.4)
```

Thus `A_n`, the subquotient (5.2), orbit finiteness, and the number (5.3) are
intrinsic under abstract group isomorphism. For fixed `p`, the groups
`G_(p,n)` are pairwise nonisomorphic.

## 6. Finite generation and ICC

The group `Gamma` is finitely generated. Equation (2.1) makes `B` cyclic and
`V` cyclic as `Gamma`-modules, so one lift of a generator of `B`, together
with a generator of `V`, generates `A_n` as a module. Hence every `G_(p,n)` is
finitely generated.

If a nonzero `a in A_n` maps nontrivially to `B`, its image has infinite orbit
by (2.2). If it lies in `V`, elementary transvections `u_ij(t^N)` give an
infinite orbit directly. The quotient `Gamma` is ICC because its FC-center is
an amenable normal subgroup and (5.4) is trivial. Therefore `G_(p,n)` is ICC.

## 7. Relative property (T)

On the common pointed dual action `L x Q`, use

```text
D={ (ell,q) : ell(e_1)!=0 or q(e_1^tensor-p)!=0 }.
```

For odd `p` at rank `p`, primitive-box averaging and the degree-`p`
Reed--Muller support bound give

```text
c_p = ((p-1)/p^2-p^(1-p))/(1-p^(1-p))
    = ((p-1)p^(p-3)-1)/(p^(p-1)-1) > 0.              (7.1)
```

In particular `c_3=1/8` and `c_5=33/208`. At `(p,r)=(2,3)`, primitive
averaging is exactly zero, but the affine-chart block-erasure theorem gives

```text
c_2=1/12.                                             (7.2)
```

For every invariant probability `nu`, either bound has the form

```text
nu(D)>=c_p nu((L x Q)\{0}).                            (7.3)
```

The pointed topology and action in (4.3), not the carry group law, enter
(7.3). The Cornulier--Tessera criterion plus property-(T) invariantization
therefore proves `(G_(p,n),A_n)` has relative property (T). Since `Gamma` has
property (T), every `G_(p,n)` has property (T).

## 8. Common operator algebras and commensurability

Product Haar measure on `L x Q` is Haar for every triangular law (4.2), by
Fubini: for fixed first coordinate, left translation is a translation in the
`Q` fiber. The action (4.3) is identical for all `n`. Fourier transform gives

```text
L(G_(p,n))   = L-infinity(L x Q) crossed-product Gamma,
C*(G_(p,n))  = C(L x Q) crossed-product-max Gamma,
C*_r(G_(p,n))= C(L x Q) crossed-product-r Gamma,       (8.1)
```

independent of `n` for fixed `p`.

Also

```text
pi_n:E_n->E_0,       pi_n(ell,q)=(T_n ell,q)           (8.2)
```

is a surjective equivariant homomorphism with kernel
`Hom(V/t^nV,F_p)` of order `p^(r_p n)`. Dualizing gives

```text
G_(p,0) < G_(p,n),       index p^(r_p n),              (8.3)
```

so every fixed-prime family is mutually commensurable.

## 9. Candidate conclusion

Subject to independent audit of the classical lattice interfaces and the
topological/Pontryagin-duality construction, the synthesis yields:

> **Uniform prime-family candidate.** For every prime `p`, there is a
> countable family `{G_(p,n)}` of finitely generated, ICC, property-(T),
> pairwise nonisomorphic, mutually commensurable groups with common group von
> Neumann algebras and common full and reduced group C*-algebras.

The intrinsic cardinal is

```text
p=2:   2^(3n),
p odd: p^(pn).                                         (9.1)
```

For `p=2`, this would lower the published binary carry construction from rank
four to rank three by combining fresh-coordinate cyclicity/orbits with the
chart detector. For odd `p`, it would produce a prime-indexed extension of the
ternary program.

The common-factor mechanism, Witt carry, Bockstein strategy, and binary
existence result are prior art. The new claims requiring review are the
stable/critical cyclicity theorem, its uniform orbit partner, and the fact
that these meet the detector phase diagram exactly on `r_p=max(p,3)`.

## 10. Remaining proof obligations

1. Formalize the general functional carry (4.1)--(4.4), beyond the existing
   ternary Lean modules.
2. Formalize the stable/critical cyclicity and orbit theorems.
3. Check the positive-characteristic Margulis normal-subgroup theorem and
   lattice property-(T) hypotheses uniformly in `p`.
4. Formalize the affine-chart invariant-measure argument at binary rank three.
5. Formalize Pontryagin duality, Haar measure, and all crossed-product bridges.
6. Obtain operator-algebra and modular-representation review before presenting
   (9.1) as an established theorem.
