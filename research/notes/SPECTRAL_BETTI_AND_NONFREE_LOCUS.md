# Betti series and the Frobenius nonfree locus

**Status:** corollaries of the spectral Frobenius-kernel decomposition. The
paper argument is complete, but the module decomposition on which it depends is
not yet Lean checked or independently reviewed.

Let

```text
S = F_p[e_1,...,e_p],
I_p = (e_1,...,e_(p-1)),
K_(p,r) = ker d_p.
```

The decomposition in `SPECTRAL_FROBENIUS_KERNEL_RESOLUTION.md` has the form

```text
K_(p,r) ~= F_mixed direct-sum I_p^r,                 (1)
```

where `F_mixed` is graded free over `S`.

This note records two consequences that are not visible from the Hilbert series
alone:

1. a closed two-variable generating function for every graded Betti number;
2. an exact description of the nonfree locus.

## 1. Closed Betti generating function

Write `S(-d)` for a free generator in spectral degree `d`. The truncated Koszul
resolution of `I_p` has, in homological degree `j`, one summand

```text
S(-sum J)
```

for every subset

```text
J subset {1,...,p-1},   |J|=j+1.
```

Define the graded Betti polynomial

```text
beta_j(q)
 = sum_d beta_(j,d) q^d.
```

The complete nonfree contribution is then

```text
sum_(j=0)^(p-2) z^j beta_j^(nonfree)(q)
 = (r/z) [ product_(a=1)^(p-1)(1+z q^a) - 1 ].       (2)
```

Indeed, expanding the product chooses a subset `J`; dividing by `z` changes the
subset cardinality from `|J|` to homological degree `|J|-1`.

If

```text
F_mixed(q)=B_(p,r)(q)-r
```

is the free-basis polynomial of the mixed-label sectors, the full Betti series
is

```text
P_(p,r)(z,q)
 = F_mixed(q)
   + (r/z) [ product_(a=1)^(p-1)(1+z q^a) - 1 ].      (3)
```

Setting `z=-1` gives the Hilbert numerator:

```text
P_(p,r)(-1,q)
 = B_(p,r)(q)
   - r product_(a=1)^(p-1)(1-q^a)
 = K_(p,r)(q).                                        (4)
```

Thus the earlier numerator formula is the Euler characteristic of a much more
rigid Betti object.

### Ungraded Betti numbers

At `q=1`, the nonfree Betti numbers are

```text
beta_j^(nonfree)
 = r binom(p-1,j+1),       0<=j<=p-2.                 (5)
```

Including the mixed free generators gives

```text
beta_0(K_(p,r)) = r^p + r(p-2),
beta_j(K_(p,r)) = r binom(p-1,j+1),   1<=j<=p-2.      (6)
```

Their alternating sum is `r^p`, the generic spectral rank.

For `p=r=3`, (6) gives

```text
beta_0=30,
beta_1=3,
```

matching

```text
0 -> S(-3)^3
  -> S^7 direct-sum S(-1)^11
       direct-sum S(-2)^11 direct-sum S(-3)
  -> K_(3,3) -> 0.
```

## 2. Exact nonfree locus

Assume `p>=3`. Then

```text
NonFree_S(K_(p,r)) = V(I_p) = V(e_1,...,e_(p-1)).    (7)
```

### Outside the Frobenius curve

If a prime ideal `q` does not contain `I_p`, one generator `e_j` is invertible
in `S_q`. Therefore

```text
(I_p)_q = S_q,
```

so every summand in (1) is free after localization.

### On the Frobenius curve

If `q` contains `I_p`, the regular sequence

```text
e_1,...,e_(p-1)
```

remains a minimal generating set of `(I_p)_q`. Hence

```text
mu((I_p)_q)=p-1>1.
```

But `(I_p)_q` has rank one. A free rank-one module over the local ring `S_q`
would need one generator, so `(I_p)_q` is not free. Since it is a direct
summand of `K_(p,r)_q`, the kernel is not free there either.

Equation (7) follows.

## 3. Homological phase change

The nonfree locus is empty at `p=2`, because `I_2=(e_1)` is principal. For every
odd prime, it is exactly the Frobenius small diagonal.

At the generic point `I_p` of that curve,

```text
dim S_(I_p)=p-1,
projective-dimension (I_p)_(I_p)=p-2,
depth (I_p)_(I_p)=1.                                  (8)
```

Thus for `p>=3`, `I_p` and hence `K_(p,r)` are torsion-free but not reflexive.
The obstruction is concentrated on a codimension-`p-1` curve rather than being
distributed throughout spectral space.

At the homogeneous maximal ideal, Auslander--Buchsbaum gives global graded
depth two:

```text
depth_S K_(p,r)=2.                                    (9)
```

The kernel therefore has constant depth two as the prime grows, while its
projective dimension grows linearly as `p-2`.

## 4. Top Ext and its binary exception

For `p>=3`, the short exact sequence

```text
0 -> I_p -> S -> S/I_p -> 0
```

and the complete-intersection calculation give

```text
Ext_S^(p-2)(I_p,S)
 ~= S/I_p                                               (10)
```

up to the grading shift

```text
1+2+...+(p-1)=p(p-1)/2.
```

Consequently

```text
Ext_S^(p-2)(K_(p,r),S)
 ~= (S/I_p)^r                                           (11)
```

with the same shift. Its support is exactly the nonfree locus in (7).

Equation (11) is intended only for `p>=3`. At `p=2`, the ideal is already free,
so homological degree zero is an ordinary dual rather than the quotient
`S/I_2`.

## 5. Geometric meaning

The scheme

```text
Spec(S/I_p) ~= A^1
```

is the Frobenius small diagonal in `Sym^p(A^1)`. The Betti series (3) says that
all higher syzygies of the carry kernel come from the derived neighborhood of
this one curve. Mixed-coordinate sectors contribute only free generators.

This gives a precise form to the slogan:

> The Frobenius quotient is small in rank but leaves a complete homological
> fingerprint in the kernel.

## 6. Formalization targets

A Lean development can split these corollaries into four comparatively small
obligations:

1. formalize the localization criterion for `I_p` outside `V(I_p)`;
2. prove minimality of the localized regular-sequence generators on `V(I_p)`;
3. encode the subset-indexed Koszul Betti polynomial (2);
4. derive the alternating-sum identity (4) and the ungraded formula (6).

The arithmetic subset enumeration is already replayed by
`experiments/spectral_frobenius_resolution.py`. The localization and
homological statements remain mathematical candidates.
