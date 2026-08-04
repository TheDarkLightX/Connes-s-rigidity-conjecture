# A stable/critical polynomial-tensor orbit theorem

**Status:** complete paper proof candidate. The rank-three, tensor-cube
critical case is Lean checked in the repository's full pinned dependency
graph. The general statement below is a written candidate and has not been
formalized or independently reviewed.

## 1. The theorem

Let `F` be any field,

```text
R=F[t],       V=R^r,
2<=m<=r,
E=E_r(R).
```

All tensor products are over `F`, not over `R`.

> **Polynomial-tensor orbit theorem candidate.** Let
> `0!=x in V^tensor-m`.
>
> - If `r>m`, the `E`-orbit of `x` is infinite, with no symmetry assumption.
> - If `r=m` and `x` is fixed by swapping its first two tensor factors, the
>   `E`-orbit of `x` is infinite.

Every divided power `Gamma^m(V)=(V^tensor-m)^(S_m)` satisfies the critical
symmetry hypothesis. Hence every nonzero divided-power tensor has infinite
orbit whenever `r>=m`.

The statement is characteristic-free. In particular it applies to the
binary rank-three tensor square and to the rank-`p` divided `p`th power for
every prime `p`.

## 2. Coordinate blocks

There is an `F`-linear coordinate decomposition

```text
V^tensor-m = direct-sum_(a in {1,...,r}^m) F[t_1,...,t_m].  (2.1)
```

Write `P_a(t_1,...,t_m)` for the finite polynomial block at coordinate tuple
`a=(a_1,...,a_m)`. Choose `a` with `P_a!=0`.

Let `u_ij(t^N)` be the elementary transvection sending

```text
e_j |-> e_j+t^N e_i.
```

In the block formula for the diagonal tensor action, selecting the
transvection term in tensor slot `s` multiplies the source block by `t_s^N`.
The use of independent variables `t_s` is exactly where tensoring over `F`
matters.

## 3. Fresh-coordinate branch

Suppose some coordinate `i` is absent from the labels
`a_1,...,a_m`. Choose a slot `s`, put `j=a_s`, and let `b` be obtained from
`a` by replacing the `s`th label by `i`. The output tuple `b` contains `i` in
exactly one slot. Therefore its block after applying `u_ij(t^N)` is

```text
P_b + t_s^N P_a.                                      (3.1)
```

Because `P_a` is a nonzero finite polynomial, the maximum total degree of the
moving summand is `N+deg(P_a)`. The family (3.1) is injective after at most a
finite initial segment, and its range is infinite.

If `r>m`, every coordinate tuple omits a label, so this proves the first part.
If `r=m` and `a` has a repeated label, it also omits a label and the same proof
applies.

## 4. Critical all-distinct branch

It remains to consider `r=m`, after assuming every repeated-label block is
zero. A nonzero block must then have all labels distinct. Relabel it as

```text
a=(i,j,a_3,...,a_m),       P=P_a!=0.
```

Apply `u_ij(t^N)` and observe the repeated output tuple

```text
b=(i,i,a_3,...,a_m).
```

The zero-substitution block `P_b` vanishes. The two-substitution block with
source labels `(j,j,a_3,...,a_m)` also vanishes. Only the two one-substitution
terms remain. First-two-factor symmetry identifies their source polynomials by
interchanging `t_1` and `t_2`, so the observed output is

```text
Q_N = t_1^N P(t_2,t_1,t_3,...,t_m)
    + t_2^N P(t_1,t_2,t_3,...,t_m).                    (4.1)
```

Let

```text
Delta(alpha)=alpha_1-alpha_2
```

for a monomial exponent in the finite support of `P`. Choose

```text
N_0 > max{|Delta(alpha)| : alpha in supp(P)}.          (4.2)
```

For `N>=N_0`, every monomial in the first summand of (4.1) has positive
`Delta`, while every monomial in the second has negative `Delta`. Their
supports are disjoint in every characteristic. Thus `Q_N!=0`. If `D` is the
maximum total degree in `P`, then `Q_N` has maximum total degree exactly
`N+D`. Consequently

```text
N |-> Q_N,       N>=N_0,
```

is injective, proving the critical case.

## 5. Why the tensor base ring is not cosmetic

The usual determinant tensor can be invariant in an exterior power over
`R`. That does not contradict this theorem: (2.1) is a tensor product over
the ground field `F`. Terms such as

```text
(t^N e_i) tensor_F e_i
and
e_i tensor_F (t^N e_i)
```

live in different monomial blocks and cannot move a polynomial scalar between
tensor factors. The separation in (4.2) makes this distinction explicit.

## 6. Consequences for the carry program

Take tensor degree `m=p`.

- At `(p,r)=(2,3)`, the stable branch says every nonzero tensor-square element
  has infinite orbit.
- For every odd prime at `r=p`, the critical branch says every nonzero divided
  `p`th-power element has infinite orbit.
- More generally, every nonzero divided `p`th-power tensor has infinite orbit
  for all `r>=p`.

Combined with the cyclicity theorem in
`STABLE_RANGE_DIVIDED_POWER_CYCLICITY.md`, this supplies both finite module
generation and the orbit-finiteness separation required by the Bockstein
invariant.

## 7. Formalization handoff

1. Replace the rank-three coordinate type by `Fin r -> ... -> Finsupp` for a
   fixed tensor arity `m`.
2. Prove the general diagonal-transvection block expansion indexed by subsets
   of the output target positions.
3. Formalize the fresh-coordinate observation (3.1).
4. Formalize the two-slot support separation (4.2).
5. Recover the existing theorem
   `fixed_swapFirstTwo_SL3_orbit_infinite` as the case `r=m=3`.

The proof is finite-support algebra; it uses no classification theorem or
analytic input.
