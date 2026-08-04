# Stable- and critical-range divided-power cyclicity

**Status:** complete paper proof candidate with exact finite-quotient certificate
replay. No priority claim is made. The theorem is not yet formalized in Lean or
independently reviewed.

This note supersedes the idea that the cyclicity mechanism is intrinsically
ternary. There are two proofs separated by a sharp geometric distinction:

- in the stable range `r>p`, an unused coordinate lowers every positive-degree
  basis tensor in one step;
- on the critical diagonal `r=p`, no coordinate is unused on an all-distinct
  tensor, but for odd `p` a two-source finite difference isolates it.

The binary rank-three case belongs to the first range. Every odd prime at rank
`p` belongs to the second.

## 1. Statement

Let `p` be prime, let

```text
k = F_p,
R = k[t_1,...,t_d]                    (d finite),
V = R^r,
E = E_r(R).
```

Tensor products are over `k`. Put

```text
B_p(V) = span_k{v^tensor-p : v in V} subseteq (V^tensor-p)^(S_p).
```

For basis vectors `b_1,...,b_p`, write `[b_1,...,b_p]` for the
corresponding orbit sum, with each distinct ordered tensor occurring once.
Let

```text
q = e_1^tensor-p,
w = [e_1,...,e_p].
```

> **Cyclicity theorem candidate.** Assume `r>=p` and either `r>p` or `p` is
> odd. Then
>
> ```text
> B_p(V) = (V^tensor-p)^(S_p),
> 0 -> K_p -> B_p(V) --d_p--> V -> 0,
> K_p = span_k(E.w),
> B_p(V) = span_k(E.q),
> ```
>
> where `d_p(v^tensor-p)=v` and `K_p=ker d_p`.

The unsupported corner is `(p,r)=(2,2)`. The argument below neither proves
nor disproves cyclicity there.

## 2. Why pure powers span the full divided power

First let `U` be a finite-dimensional `k`-subspace of `V` with basis
`b_1,...,b_N`. The orbit sums are a basis of `(U^tensor-p)^(S_p)`. The
coordinate of

```text
(x_1 b_1 + ... + x_N b_N)^tensor-p
```

at the multiset with multiplicities `m=(m_1,...,m_N)` is the function

```text
x |-> x_1^(m_1) ... x_N^(m_N),       sum m_i=p.       (2.1)
```

These functions on `F_p^N` are linearly independent. Indeed, reduce every
coordinate exponent using `x_i^p=x_i`:

- a diagonal monomial `x_i^p` reduces to the degree-one monomial `x_i`;
- every non-diagonal degree-`p` monomial already has all exponents at most
  `p-1` and remains unchanged.

The resulting reduced exponent vectors are pairwise distinct. Reduced
monomials with coordinate exponents in `{0,...,p-1}` form a basis of the
functions on `F_p^N`, so (2.1) is independent. The evaluation matrix therefore
has full row rank, and its columns—the pure powers—span every orbit sum.

Every tensor involves a finite-dimensional `U`, hence

```text
B_p(V)=(V^tensor-p)^(S_p).                         (2.2)
```

This prime-field interpolation lemma is essential. It would be unsafe to
invoke characteristic-zero polarization, since `p!` vanishes in `F_p`.

## 3. The Frobenius diagonal

Define `d_p` on the orbit-sum basis by

```text
d_p([b,...,b])=b,
d_p([b_1,...,b_p])=0 if the multiset is not diagonal.  (3.1)
```

For `v=sum a_b b`, the diagonal coefficient of `v^tensor-p` is
`a_b^p=a_b`, so (3.1) gives `d_p(v^tensor-p)=v`. Since pure powers span,
this also proves `E`-equivariance. The map is onto and

```text
K_p = span_k{all non-diagonal orbit sums}.             (3.2)
```

## 4. Constant tensors

Use the monomial basis

```text
M={t^alpha e_i : alpha in N^d, 1<=i<=r}
```

and let the total degree of a multiset be the sum of its monomial degrees.
At degree zero, every all-distinct `p`-frame is in the `SL_r(F_p)` orbit span
of `w`.

Now take a non-diagonal constant multiset `T` with fewer than `p` coordinate
labels. Some `e_i` occurs with multiplicity `m`, where `2<=m<=p-1`. Choose
an absent label `h`, and replace one `e_i` by `e_h` to obtain `S`. For the
elementary transvection sending `e_h` to `e_h+e_i`,

```text
(u_ih(1)-1)S = m T.                                  (4.1)
```

There is no higher substitution term because `e_h` occurs once in `S`.
The scalar `m` is invertible in `F_p`, and `S` uses one more coordinate
label. Descending induction on the number of missing labels proves that every
constant element of `K_p` lies in `span(E.w)`.

## 5. The fresh-coordinate induction

Let `T` be a positive-degree non-diagonal basis multiset. Select an entry

```text
t^alpha e_i,     alpha_s>0.
```

Suppose there is a coordinate `h!=i` absent from the other `p-1` entries.
Replace the selected entry by

```text
t^(alpha-e_s) e_h
```

to obtain `S`. The label `h` occurs exactly once in `S`, hence

```text
(u_ih(t_s)-1)S = m T,                                (5.1)
```

where `m` is the multiplicity of the exact selected entry in `T`.
Because `T` is non-diagonal, `1<=m<=p-1`; therefore `m` is invertible.
The source has total degree one less than `T`.

When `r>p`, the other `p-1` entries omit at least two of the `r` coordinates,
so an `h!=i` always exists. Equation (5.1), together with the constant case,
proves kernel cyclicity throughout the stable range for every prime—including
`p=2,r=3`.

When `r=p`, the same argument works unless the target uses all `p` coordinate
labels. That is the sole critical case.

## 6. Critical odd-prime identity

Assume `r=p` is odd and `T` uses every coordinate label. Relabel the
coordinates so that a positive-degree monomial `x` occurs in the first slot:

```text
T=A(x,y,z_3,...,z_p)
 =[x e_i, y e_j, z_3 e_3,...,z_p e_p].                (6.1)
```

Put

```text
S_y=[e_j,y e_j,z_3 e_3,...,z_p e_p].                 (6.2)
```

Only the two `j`-labelled factors can change under `u_ij(ax)`. Consequently
the difference between parameters `x` and `-x` cancels the zero- and
two-substitution terms. Since `2` is invertible,

```text
(u_ij(x)S_y-u_ij(-x)S_y)/2
  = A(x,y,z_3,...,z_p)                    if y=1,
  = A(x,y,z_3,...,z_p)+A(xy,1,z_3,...,z_p) if y!=1.  (6.3)
```

Here `1` is the constant monomial. In the equal-source case, the two identical
source factors coalesce in the divided-power orbit basis; the coefficient in
(6.3) is `1`, not an unnormalized binomial coefficient `2`.

The source `S_y` has lower total degree because `deg x>0`. In the second line,
the auxiliary tensor `A(xy,1,z_3,...,z_p)` is obtained from the equal-source
identity applied to

```text
[e_j,e_j,z_3 e_3,...,z_p e_p],
```

which is already generated by the repeated-label induction. Thus a
simultaneous induction on total degree proves (6.1). Notice that multiplication
of monomials, not divisibility comparison, is used; the proof is unchanged for
every finite number of polynomial variables.

This is the actual odd-prime generalization of the ternary cancellation:
antisymmetrization isolates the linear substitution term because the source
has exactly two `j`-factors. It does not try to cancel all degrees in a generic
`p`-term expansion.

## 7. The whole module is cyclic

Inclusion-exclusion in the tensor algebra gives

```text
sum_(S subseteq {1,...,p}) (-1)^(p-|S|)
  (sum_(i in S) e_i)^tensor-p
    = [e_1,...,e_p]=w.                              (7.1)
```

Every nonzero constant vector `sum_(i in S)e_i` is in the
`SL_r(F_p)`-orbit of `e_1`, so `w` lies in `span(E.q)`. Moreover,
`d_p(span(E.q))` is the `E`-span of `e_1`, which is all of `V`: elementary
transvection differences produce every `f e_i`. Since this span contains the
kernel and maps onto the quotient, it equals `B_p(V)`.

## 8. Exact certificate evidence

The checker `experiments/odd_prime_divided_power_certificates.py` expands every
identity into ordered tensors, reduces coefficients modulo `p`, and certifies
every kernel basis vector in the declared total-degree quotient.

| `p` | rank | variables | degree | `dim B_p` | `dim K_p` | certified |
|---:|---:|---:|---:|---:|---:|---:|
| 2 | 3 | 1 | 6 | 132 | 120 | 120 |
| 2 | 3 | 2 | 3 | 162 | 153 | 153 |
| 2 | 4 | 1 | 4 | 126 | 114 | 114 |
| 3 | 4 | 1 | 3 | 264 | 256 | 256 |
| 5 | 5 | 1 | 2 | 1351 | 1346 | 1346 |
| 5 | 6 | 1 | 1 | 1008 | 1002 | 1002 |

For `(p,r)=(5,5)`, the ledger is

```text
120 constant collisions
+ 1 constant frame
+ 1205 degree-lowering certificates
+ 19 equal-source certificates
+ 1 distinct-source two-step certificate
= 1346.
```

The previously recorded univariate, bivariate, and trivariate `p=3,r=3`
oracles give the larger-degree ternary checks.

## 9. Falsification and formalization targets

1. Formalize the prime-field interpolation lemma (2.2), including the
   normalization of orbit sums with repeated entries.
2. Formalize the double induction behind (4.1), (5.1), and (6.3).
3. Verify the constant-frame orbit statement inside `E_r(R)`, rather than only
   `SL_r(F_p)`.
4. Search strict-polynomial, hyperalgebra, and current-group literature for
   this exact stable/critical theorem before using novelty language.
5. Do not infer the `(2,2)` corner from the stable or odd-critical proof.

Finite certificates are exact evidence for the displayed quotients, not a
substitute for the untruncated induction.
