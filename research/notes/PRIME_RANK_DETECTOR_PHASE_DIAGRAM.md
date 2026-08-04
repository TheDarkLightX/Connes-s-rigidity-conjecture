# A prime--rank phase diagram for primitive and affine-chart detectors

**Status:** complete quantitative proof candidate for two complementary
invariant-measure detectors. Turning the positive detector bounds into a
group-factor construction additionally requires the corresponding Witt-carry
extension, finite generation, and infinite-orbit theorems.

**Novelty status:** unestablished. The calculation generalizes the binary
rank-four detector in Chapter 4 of OpenAI's 2026 *Ten Advances in Mathematics
and Theoretical Computer Science*. The formula below appears not to be stated
there, but it is a short synthesis of that argument with the generalized
Reed--Muller distance formula and should not receive a priority label without
specialist review. Shuoxing Zhou's concurrent binary rank-three construction
uses the complementary affine-chart geometry and is essential prior art:

- <https://arxiv.org/abs/2608.02327>

Affine/projective decompositions of Reed--Muller codes are themselves a
developed coding-theory topic. The chart-ideal lemma here is elementary
monomial-ideal algebra; the possible contribution is its quantitative
prime--rank/degree--rank synthesis with the invariant-measure detector, not a
claim that restricting polynomials to affine charts is new.

## 1. Setup

Let `p` be prime, `r>=3`, and

```text
R = F_p[t],                 V = R^r,
B_p = span_F_p {v tensor-p : v in V},
X = Hom_F_p(V,F_p),         Y = Hom_F_p(B_p,F_p).
```

Let `Gamma=SL_r(R)` act by pullback on `X x Y`. For `N>=1`, let `V_N`
consist of the vectors whose coordinates have degree less than `N`, and let
`Prim_N` be its primitive vectors. Put `e=e_1` and define the clopen detector

```text
D = {(ell,q) : ell(e) != 0 or q(e tensor-p) != 0}.       (1.1)
```

The first theorem candidate is the primitive-box estimate

```text
nu(D) >= c_prim(p,r) nu((X x Y) \ {(0,0)})               (1.2)
```

for every `Gamma`-invariant probability `nu`, where

```text
          (p-1)/p^2 - p^(1-r)
c_prim(p,r) = --------------------- .                    (1.3)
               1 - p^(1-r)
```

The constant is positive exactly when

```text
(p-1) p^(r-3) > 1.                                      (1.4)
```

Consequently:

```text
p=2:   the first positive primitive-box rank is r=4,
       with c_prim(2,4)=1/7;
p>=3:  every property-(T) rank r>=3 is positive;
p=3,r=3: c_prim(3,3)=1/8.
```

This explains the rank threshold of the *primitive-vector implementation* in
the published binary argument and why the ternary construction already works
in rank three. It is not a universal detector obstruction: Section 6 proves
that affine charts recover the binary rank-three case of Zhou.

## 2. Exact primitive-vector count

There are `p^(rN)` vectors in `V_N`. Classifying every nonzero vector by its
monic greatest common divisor gives

```text
p^(rN)-1 = sum_(d=0)^(N-1) p^d |Prim_(N-d)|.
```

Subtracting `p` times the identity for `N-1` yields

```text
|Prim_N| = p^(rN) - p^(rN-r+1) + p - 1,                 (2.1)
|V_N \ Prim_N| = p^(rN-r+1) - p + 1.                    (2.2)
```

Thus the nonprimitive density tends to `p^(1-r)`. Since `R` is Euclidean,
every primitive vector is the first column of an element of `SL_r(R)`, so the
group is transitive on primitive vectors.

## 3. Minimum support of the degree-p detector

For `z=(ell,q)`, the two evaluation functions on the `rN` scalar coordinates
of `V_N` are

```text
L_z(v)=ell(v),                  P_z(v)=q(v tensor-p).
```

The first is reduced linear. The second is a reduced polynomial function of
total degree at most `p`. If `q` is nonzero on the span generated inside
`V_N`, then `P_z` is nonzero because pure `p`th tensors span that module.

The generalized Reed--Muller minimum-distance formula says that a nonzero
reduced degree-at-most-`p` polynomial in `m>=2` variables has support at least

```text
(p-1) p^(m-2).                                           (3.1)
```

For `p>2`, write `p=1*(p-1)+1` in the standard distance formula. For `p=2`,
write `2=2*(p-1)+0`; both cases give (3.1). A nonzero linear function has the
larger support `(p-1)p^(m-1)`. Hence whenever `z` is detected somewhere in
`V_N`, at least the fraction

```text
s_p = (p-1)/p^2                                         (3.2)
```

of all vectors detects it.

## 4. Remove the nonprimitive vectors

Let `T=p^(rN)` and `delta=p^(1-r)`. Equations (2.2) and (3.2) show that the
number of detecting primitive vectors is at least

```text
(s_p-delta)T + (p-1),
```

whereas the number of primitive vectors is

```text
(1-delta)T + (p-1).
```

Their ratio is bounded below by its limit

```text
(s_p-delta)/(1-delta) = c_prim(p,r),                    (4.1)
```

because the common positive correction `p-1` only increases the ratio when
`s_p<1`.

For each primitive `v`, choose `g_v` with `g_v e=v`. Invariance makes the
probability of detection at `v` equal to `nu(D)`. Integrating the finite
pointwise count gives

```text
nu(D) >= c_prim(p,r) nu(U_N),                           (4.2)
```

where `U_N` is the set detected somewhere in `V_N`. The sets `U_N` increase
to `(X x Y)\{(0,0)}`. Monotone convergence proves (1.2).

Finally, the denominator in (1.3) is positive and

```text
c_prim(p,r)>0
  iff (p-1)/p^2 > p^(1-r)
  iff (p-1)p^(r-3)>1,
```

which is the phase boundary (1.4).

## 5. Values near the boundary

| prime `p` | rank `r` | `c_prim(p,r)` | primitive-box verdict |
|---:|---:|---:|:---|
| 2 | 3 | 0 | boundary; this count proves no gap |
| 2 | 4 | `1/7` | positive, published binary case |
| 2 | 5 | `1/5` | positive |
| 3 | 3 | `1/8` | positive, repository ternary case |
| 3 | 4 | `5/26` | positive |
| 5 | 3 | `1/8` | positive |
| 7 | 3 | `5/48` | positive |

The exact Julia oracle `experiments/prime_rank_detector.jl` recomputes this
table and the chart constants below as rational arithmetic, and brute-forces
(2.1) in the boundary cases.

## 6. The complementary affine-chart detector

The primitive loss is avoidable when the rank is larger than the polynomial
degree. Split the `rN` coefficient variables into `r` blocks, one for each
polynomial coordinate, and define the primitive affine charts

```text
U_(s,N) = {e_s + sum_(j != s) f_j e_j : deg(f_j)<N}.
```

Every vector in every chart is in the `SL_r(R)`-orbit of `e_1`. The following
elementary vanishing lemma is the key.

> **Chart lemma.** A reduced polynomial of total degree at most `p` that
> vanishes on every `U_(s,N)` is zero whenever `p<r`.

To prove it, make the single simultaneous affine change
`y_(s,0)=x_(s,0)-1` in the constant variable of every block and leave all
positive-degree variables unchanged. In these coordinates, chart `s` is the
coordinate subspace on which the entire `s`th block is zero. Uniqueness of the
reduced representative says that vanishing on chart `s` is equivalent to
every monomial containing a variable from block `s`. If the polynomial
vanishes on all `r` charts, every monomial contains at least one variable from
every block and therefore has degree at least `r`. Degree at most `p<r`
forces the polynomial to vanish.

More quantitatively, if a nonzero reduced polynomial of degree at most `p`
vanishes on a set `S` of charts, then every one of its monomials uses a
variable from every block indexed by `S`. Hence

```text
|S| <= p.                                                (6.1)
```

Thus when `p<r`, the restriction is nonzero on at least `r-p` charts, not
merely on one chart.

The condition is sharp for this chart family. If `p>=r` and `N>=2`, the
reduced homogeneous degree-`p` monomial

```text
x_(1,1)^(p-r+1) x_(2,1) ... x_(r,1)
```

is nonzero and vanishes on every chart, because the distinguished coordinate
has all positive-degree coefficients equal to zero. It is an evaluation
monomial of the divided `p`th-power module.

Assume now `p<r`. If `z=(ell,q)` is nonzero on the finite module generated in
the degree-`N` box, at least one of its linear and divided-power evaluation
polynomials is nonzero. Regard that polynomial as having degree at most `p`.
By (6.1), it is nonzero on at least `r-p` charts. The Reed--Muller bound
detects at least the fraction `s_p=(p-1)/p^2` on each such chart. Averaging
over all `r` equally sized charts and then increasing `N` gives

```text
nu(D) >= c_chart(p,r) nu((X x Y)\{0}),
c_chart(p,r) = (r-p)(p-1)/(r p^2),         provided p<r. (6.2)
```

For `p=2,r=3`, this is `c_chart=1/12`, exactly the chart constant in Zhou's
independent rank-three binary construction. Thus the two geometries have
complementary domains:

| prime `p` | rank `r` | `c_chart(p,r)` |
|---:|---:|---:|
| 2 | 3 | `1/12` |
| 2 | 4 | `1/8` |
| 2 | 5 | `3/20` |
| 3 | 4 | `1/18` |
| 3 | 5 | `4/45` |

The independent block-restriction oracle
`experiments/chart_detector_rank.py` computes the exact joint restriction
rank on every subset of charts with two coefficient variables per block. It
finds minimum numbers of nonzero charts

```text
p=2, d=2, r=3,4,5:  1,2,3;
p=3, d=3, r=3,4,5:  0,1,2,
```

exactly `max(r-d,0)`. At the sharp ternary boundary `p=d=r=3`, the source has
dimension `78` but restriction to all three charts has rank `70`; when `r=4`,
the all-chart restriction has full rank `157`.

```text
primitive boxes: c_prim>0 iff (p-1)p^(r-3)>1;
affine charts:   c_chart=(r-p)(p-1)/(r p^2)>0 iff p<r.
```

Together they give a positive detector for every prime `p` and every
property-(T) rank `r>=3`: use charts only at the missing binary point
`(p,r)=(2,3)`, and primitive boxes everywhere else. This is a detector theorem,
not yet a uniform all-prime carry construction.

### 6.1 The degree--rank master formula

The same proof is not special to degree `p`. Let a nonzero reduced polynomial
detector have total degree at most `d`, and write

```text
d = a(p-1)+b,                 0 <= b < p-1.
```

Once the finite box has enough coefficient variables for degree `d`, the exact
generalized Reed--Muller relative distance is

```text
s(p,d) = (p-b)/p^(a+1).                              (6.3)
```

The two arguments above therefore give

```text
c_prim(p,r;d)
  = (s(p,d)-p^(1-r))/(1-p^(1-r)),
  positive iff (p-b)p^(r-a-2)>1;                    (6.4)

c_chart(p,r;d)
  = (r-d)s(p,d)/r,                   provided d<r.  (6.5)
```

Indeed, a degree-`d` polynomial can vanish on at most `d` coordinate-block
charts. The threshold is sharp for this chart family once there are enough
coefficient variables: a reduced monomial of degree `d` using at least one
positive-degree variable from every block vanishes on all charts whenever
`d>=r`. Substituting `d=p` in (6.3)--(6.5) recovers all formulas above. This
degree--rank form may be useful for other low-degree module extensions even
when no Witt-carry construction is present.

## 7. Property (T) consequence and an explicit spectral constant

For `r>=3`, `SL_r(F_p[t])` is a lattice in
`SL_r(F_p((1/t)))` and has property (T). First consider the split module

```text
D_p = V direct-sum B_p.
```

Its dual is `X x Y` with coordinatewise group law. Let

```text
a_1=(e,0),                  a_2=(0,e tensor-p),
zeta_p=exp(2 pi i/p),       kappa_p=4 sin(pi/p)^2.
```

For a character `z=(ell,q)`, membership in the detector (1.1) implies

```text
|z(a_1)-1|^2 + |z(a_2)-1|^2 >= kappa_p.                (7.1)
```

Indeed every nontrivial `p`th root of unity is at squared distance at least
`kappa_p` from `1`. Combining (7.1) with either positive detector estimate
gives the explicit invariant
spectral estimate

```text
sum_(j=1)^2 integral |z(a_j)-1|^2 dnu(z)
  >= kappa_p c_*(p,r) (1-nu({0})),                      (7.2)
```

where `c_*` may be `c_prim` or `c_chart` in its domain.

The standard abelian-by-property-(T) spectral lemma therefore proves

```text
D_p semidirect Gamma has property (T).                  (7.3)
```

The constants recover the published binary number exactly:

```text
kappa_2 c_prim(2,4) = 4/7,
kappa_3 c_prim(3,3) = 3/8,
kappa_2 c_chart(2,3) = 1/3.                             (7.4)
```

More generally, estimate (1.2) also rules out the Cornulier--Tessera sequence
after property-(T) invariantization. Therefore, for any countable abelian
`Gamma`-module `A` whose compact dual is the same pointed action `X x Y`,

```text
(A semidirect Gamma, A) has relative property (T),
A semidirect Gamma has property (T).                    (7.5)
```

The relative-property-(T) conclusion uses only the pointed topology and action,
not which carry group law is placed on `X x Y`. There is also an independent
factor-transfer route: (7.3), the common crossed product, ICC, and the
Connes--Jones characterization transfer property (T) from the split group to
every carry group. Thus the detector supports two proof paths with different
formalization dependencies.

## 8. Construction portal and its limits

Length-two `p`-typical Witt addition suggests a carry group on `X x Y` whose
discrete dual has exponent `p^2` and Bockstein

```text
beta_n = t^n d_p,       d_p(v tensor-p)=v.               (8.1)
```

Over the prime field `F_p`, (8.1) is untwisted because scalar Frobenius is the
identity. The same finite-orbit argument would give

```text
|FinOrb(A_n[p]/pA_n)| = p^(rn).                         (8.2)
```

The stable/critical cyclicity and orbit theorems now close the algebraic portal
on the minimal-rank line

```text
r_p=max(p,3).
```

At `p=2,r=3`, both proofs use a fresh coordinate and the detector uses charts.
At odd `p,r=p`, both proofs use their critical branches and the detector uses
primitive boxes. The general Witt polynomial supplies a functional carry;
scalar cocycle, Teichmuller, exponent, and multiplication-by-`p` identities
pass exact exhaustion at `p=2,3,5,7`.

The remaining obligations are now interfaces rather than missing algebra:

1. formalize continuity and naturality of the general functional Witt carry;
2. formalize the stable/critical cyclicity and tensor-orbit proofs;
3. install the Bockstein exact sequence and characteristic-subgroup argument;
4. formalize the crossed-product identifications;
5. obtain independent modular-representation and operator-algebra review.

The candidate conclusion and its exact claim boundary are in
`UNIFORM_PRIME_CARRY_FAMILIES.md`. The published OpenAI construction supplies
a completed route at `p=2,r=4`, while Zhou supplies a different completed route
using binary rank-three charts. The proposed binary rank-three *carry* route
and odd-prime routes remain unreviewed.

## 9. Falsification targets

1. Check (3.1) with the exact generalized Reed--Muller convention for degree
   `p` when `p=2` and when the number of variables is minimal.
2. Verify that `q` nonzero on the finite divided-power span forces the
   evaluation polynomial to be a nonzero function, not merely a nonzero formal
   polynomial.
3. Audit the primitive completion and action convention `g_v e=v`.
4. Search the modular representation literature for the exact detector
   phase formula before making any novelty claim.
5. Audit the new critical identity `(u(x)S-u(-x)S)/2`: its validity depends on
   the source having exactly two mutable factors and on divided-power orbit-sum
   normalization, not on a generic cancellation of a degree-`p` expansion.
6. Formalize the chart-ideal intersection argument and verify that the sharp
   monomial obstruction belongs to the divided-power evaluation space.

## References

- OpenAI, Chapter 4, *A Counterexample to Connes's Rigidity Conjecture*, in
  [Ten Advances in Mathematics and Theoretical Computer
  Science](https://cdn.openai.com/pdf/ten-proofs-oai.pdf#page=95).
- S. Zhou,
  [ICC property (T) groups without W*-superrigidity](https://arxiv.org/abs/2608.02327).
- R. San-Jose,
  [A recursive construction for projective Reed--Muller
  codes](https://arxiv.org/abs/2312.05072).
- Y. de Cornulier and R. Tessera,
  [A characterization of relative Kazhdan property T for semidirect products
  with abelian groups](https://arxiv.org/abs/0911.3371).
- B. Bekka, P. de la Harpe, and A. Valette,
  [Kazhdan's Property (T)](https://perso.univ-rennes1.fr/bachir.bekka/KazhdanTotal.pdf).
