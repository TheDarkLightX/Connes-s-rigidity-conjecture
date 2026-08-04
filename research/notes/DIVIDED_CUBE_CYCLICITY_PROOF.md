# A cyclicity proof for the ternary divided cube

**Mathematical status:** complete proof candidate over `F₃`, reduced to the
explicit tensor-basis calculations written below.

**Machine status:** independently verified in the total-degree quotients through
degree `12` and in the ring quotients `F₃[t]/(t^N)` for `N = 1,2,3,4`.
The infinite cyclicity proof itself is not yet formalized in Lean. The separate
infinite-orbit theorem passes the repository's full pinned Lean build.

**Novelty status:** not established. The proof should be compared with modular
divided-power/current-group literature and reviewed by a specialist before any
novelty claim.

## 1. Statement

Let

```text
k = F₃,        R = k[t],        V = R³
```

and regard `V` as a `k`-vector space. Put

```text
B = span_k {v ⊗ v ⊗ v : v ∈ V} ⊆ V ⊗_k V ⊗_k V.
```

Let `E = E₃(R)` act diagonally on the tensor cube. Write

```text
q = e₁ ⊗ e₁ ⊗ e₁,
w = Σ_{σ∈S₃} e_{σ(1)} ⊗ e_{σ(2)} ⊗ e_{σ(3)}.
```

The proof establishes the following package.

> **Theorem candidate.** There is an `E`-equivariant exact sequence
>
> ```text
> 0 → K → B --d₃→ V → 0,
> d₃(v ⊗ v ⊗ v) = v.
> ```
>
> Moreover:
>
> 1. `K = span_k(E · w)`;
> 2. `B = span_k(E · q)`;
> 3. neither `K` nor `B` has a nonzero `E`-fixed vector;
> 4. every nonzero element of `B` has infinite `E`-orbit.

Item 4 is the existing rank-three orbit theorem. The new part of this note is a
short proof of items 1 and 2. The engine is a finite difference that cancels the
quadratic divided-power term in characteristic three.

## 2. The multiset basis and Frobenius exact sequence

Choose the `k`-basis

```text
x(i,a) = t^a eᵢ,       i ∈ {1,2,3}, a ≥ 0
```

of `V`. For basis vectors `x,y,z`, let `[x,y,z]` be the sum of the distinct
ordered tensors obtained by permuting the multiset `{x,y,z}`. Thus `[x,x,y]`
has three summands and `[x,y,z]` has six when the entries are distinct.

### Lemma 2.1 — multiset basis

The tensors `[x,y,z]`, indexed by multisets of three basis vectors, form a
`k`-basis of `B`.

**Proof.** They are linearly independent because different multisets have
disjoint support in the ordered tensor basis. It remains to put every multiset
sum in the span of pure cubes.

For two different basis vectors, set `P(v)=v^⊗3` and

```text
C₊ = P(x+y) - P(x) - P(y) = [x,x,y] + [x,y,y],
C₋ = P(x-y) - P(x) + P(y) = -[x,x,y] + [x,y,y].
```

Since `2` is invertible in `F₃`, these two equations isolate both two-equal
multisets. For three different vectors, inclusion-exclusion gives

```text
[x,y,z] = P(x+y+z) - P(x+y) - P(x+z) - P(y+z)
            + P(x) + P(y) + P(z).
```

Conversely, expanding a pure cube gives a finite linear combination of these
multiset sums. ∎

Define `d₃` on this basis by

```text
d₃([x,x,x]) = x,
d₃([x,y,z]) = 0  if the multiset is not diagonal.
```

For `v = Σ_x a_x x`, the diagonal part of `P(v)` is
`Σ_x a_x³ [x,x,x]`. Since `a³=a` in `F₃`, this proves

```text
d₃(P(v)) = v.
```

It follows immediately that `d₃` is onto and that `K=ker d₃` has the basis of
all non-diagonal multisets.

Equivariance can be checked on pure cubes:

```text
d₃(g · P(v)) = d₃(P(gv)) = gv = g d₃(P(v)).
```

## 3. Simultaneous degree induction: the repeated-label step

Let

```text
W = span_k(E · w) ⊆ K.
```

Use the convention

```text
uᵢⱼ(f)(r eⱼ) = r eⱼ + fr eᵢ,       i ≠ j,
```

with the other coordinate summands fixed.

We prove that every non-diagonal basis tensor lies in `W` by induction on
total polynomial degree. At each degree we first handle tensors whose
coordinate labels repeat, then all-distinct tensors. The second half is
Section 4.

At total polynomial degree zero, `w ∈ W`. Applying a constant transvection to
the unique occurrence of `eⱼ` gives

```text
uᵢⱼ(1)w - w = 2[eᵢ,eᵢ,eₖ],
```

where `{i,j,k}={1,2,3}`. Varying the ordered pair `(i,j)` produces all six
two-equal basis vectors because `2` is invertible in `F₃`. The coefficient
`2` is important: two ordered tensors collapse onto each term of the
two-equal orbit sum. Hence the entire seven-dimensional constant kernel is in
`W`. The `psl₃` identification in `CONSTANT_KERNEL_PSL3.md` gives a useful
conceptual explanation, but is not needed for this base case.

For the induction step, assume every non-diagonal multiset of degree below
`D` belongs to `W`, and let

```text
T = [t^a eᵢ, t^b eⱼ, t^c eₖ]
```

have degree `D`, with its coordinate labels not all distinct. If `D>0`, choose
a positive-degree entry, say `t^a eᵢ`. Because the other two labels repeat or
use at most two labels in total, there is a label `h ≠ i` absent from the other
two entries. Replace the chosen entry by `t^(a-1)e_h`, obtaining a
non-diagonal multiset `S` of degree `D-1`. The label `h` occurs exactly once in
`S`, so no quadratic term appears and

```text
uᵢh(t)S - S = cT,        c ∈ {1,2}.
```

Here `c=1` if the new entry is distinct from the other two basis vectors and
`c=2` if it coincides with exactly one of them. Coincidence with both would
make `T` diagonal, which is excluded because `T∈K`. Thus `c≠0` in `F₃`.
The outer induction hypothesis puts `S` in `W`; `E`-stability and invertibility
of `c` then put `T` in `W`. This completes the repeated-label half at degree
`D`. Notice why the outer hypothesis includes both label shapes: `S` can have
all three coordinate labels distinct.

## 4. One finite difference generates every all-distinct tensor

For monomials `x,y,z ∈ R`, write

```text
A(x,y,z) = [x eᵢ, y eⱼ, z eₖ]
```

when `i,j,k` are pairwise distinct and fixed in that order.

Take the repeated-label tensor with two genuinely equal entries

```text
S = [x eⱼ, x eⱼ, z eₖ].
```

Its transvection expansion is

```text
uᵢⱼ(f)S
  = S
  + A(fx,x,z)
  + [fx eᵢ, fx eᵢ, z eₖ].                (4.1)
```

This identity has coefficient `1` in the middle term: the three positions of
`z`, together with the two choices of which equal `x eⱼ` entry is changed,
produce the six distinct ordered tensors in `A(fx,x,z)` exactly once.

The middle term is linear in `f`, while the last term is quadratic. Replacing
`f` by `2f` and using `2²=1` in `F₃` therefore yields the exact certificate

```text
uᵢⱼ(2f)S - uᵢⱼ(f)S
  = A(fx,x,z).                              (4.2)
```

Both transvection images in (4.2) lie in `W`, because `S∈W` and `W` is
`E`-stable. Hence `A(fx,x,z)∈W`.

For the second half of the same degree-`D` induction, let
`A(t^a,t^b,t^c)` be an all-distinct basis tensor of degree
`D=a+b+c`. The monomials `t^a` and `t^b` are comparable by divisibility.

- If `a≥b`, use (4.2) with `x=t^b` and `f=t^(a-b)`.
- If `a<b`, interchange the coordinate labels `i,j` in the same calculation,
  and use `x=t^a` and `f=t^(b-a)`.

The repeated-label source has degree `2 min(a,b)+c ≤ D`. If the inequality
is strict, it lies in `W` by the outer induction hypothesis; if equality holds,
then `a=b` and it lies in `W` by the repeated-label half just proved at degree
`D`. Thus (4.2) puts the desired all-distinct tensor in `W`.

At degree zero, the only all-distinct tensor is `w` itself, so this also closes
the base case. The simultaneous induction proves

```text
K = W = span_k(E · w).
```

### Conceptual form

Equation (4.2) is a characteristic-three group-level divided-power operation:
the first finite difference keeps the linear term, while `2²=1` cancels the
quadratic term. The remaining input is the divisibility chain of the monomial
basis of `F₃[t]`. The ordinary current Lie algebra sees only the first
derivative and does not by itself encode this two-point finite-difference
certificate.

## 5. The whole divided cube is cyclic

Let `Q = span_k(E · q)`. Inclusion-exclusion on the seven nonzero subset sums of
`e₁,e₂,e₃` shows `w ∈ Q`; each subset sum is a constant unimodular vector and
is an elementary translate of a coordinate vector.

The image `d₃(Q)` contains `e₁` and is `E`-stable. Differences of elementary
translates give every polynomial basis vector:

```text
uᵢⱼ(t^a)eⱼ - eⱼ = t^a eᵢ.
```

Hence `d₃(Q)=V`. Given `b∈B`, choose `c∈Q` with `d₃(c)=d₃(b)`. Then
`b-c∈K`. Since `K=span_k(E·w)` and `w∈Q`, we have `b-c∈Q`, and therefore
`b∈Q`. Thus

```text
B = span_k(E · q).
```

## 6. Fixed vectors and orbit growth

The repository's rank-three orbit theorem proves more than needed here: every
nonzero tensor fixed by swapping its first two tensor factors has an infinite
orbit under a single tail of elementary `SL₃(F[t])` transvections. Every element
of `B` has that symmetry. Consequently a nonzero `E`-fixed vector in `B` (or in
`K`) would have both a singleton orbit and an infinite orbit, a contradiction.

## 7. Hilbert-series check

Grade the multiset basis by total `t`-degree. If `A(q)=3/(1-q)` counts the
basis letters, the cycle index for multisets of size three gives

```text
H_B(q) = (A(q)^3 + 3 A(q)A(q^2) + 2 A(q^3)) / 6.
```

There are `3/(1-q^3)` diagonal basis elements, so

```text
H_K(q)
  = 9/(2(1-q)^3) + 9/(2(1-q)(1-q^2)) - 2/(1-q^3).
```

The first coefficients of `H_K` are

```text
7, 18, 36, 52, 81, 108, 142, 180, 225, 268, 324, 378, 439, ...
```

The total-degree oracle through degree `12` has

```text
dim B_≤12 = 2273,
dim K_≤12 = 2258,
dim span(E_≤12 · w) = 2258.
```

It uses `78 = 6·13` monomial elementary transvections. This exact finite linear
algebra is consistent with the proof and is sensitive to a missing coefficient
or finite-difference relation. A separate replay of the local proof
certificates checks the generator seed, all `6` constant collision identities,
`1,797` repeated-label induction steps, and `454` nonconstant/all-distinct
equal-source finite differences in this quotient. Thus every one of the
`2,258` kernel basis vectors is covered by the replayable induction ledger.

## 8. Formalization obligations

The Lean proof should be split into replayable obligations:

1. multiset orbit sums form a basis of `B` over `F₃`;
2. diagonal extraction gives the exact sequence in Section 2;
3. the simultaneous degree induction and the unique-source transvection
   identity, including its `1`/`2` collision coefficient;
4. the equal-source expansion (4.1);
5. the finite-difference cancellation (4.2);
6. monomial divisibility generates every all-distinct basis tensor;
7. inclusion-exclusion placing `w` in the orbit span of `q`;
8. surjectivity of `d₃` on that orbit span;
9. cyclicity conclusions for `K` and `B`.

Until those obligations build and the argument receives independent review,
the repository should label this a **complete proof candidate**, not a promoted
new theorem.
