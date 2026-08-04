# Relative property (T) from the joint ternary detector

**Status:** complete paper proof candidate. This is the central unreviewed step
that upgrades the algebraic construction to a candidate family of property-(T)
groups. It is not yet formalized and must receive expert scrutiny before any
counterexample claim.

## 1. Statement

Let

```text
Γ = SL₃(F₃[t]),
E_n = the compact shifted carry group on L×Q,
A_n = dual(E_n),
G_n = A_n ⋊ Γ.
```

Here

```text
L = Hom_F₃(F₃[t]³,F₃),
Q = Hom_F₃(B,F₃),
```

and `B` is the ternary divided-cube module. The claim proved below is

```text
(G_n,A_n) has relative property (T).
```

Since `Γ` has property (T), the standard extension theorem then gives property
(T) for `G_n`.

The proof is independent of `n`: by shifted-carry naturality, the pointed
compact `Γ`-space underlying `dual(A_n)` is always the same coordinate action
on `L×Q`.

The proof architecture is not a priority claim. Chapter 4 of OpenAI's
July/August 2026 *Ten Advances in Mathematics and Theoretical Computer
Science* proves the binary rank-four construction by the same primitive-vector
and low-degree-support mechanism. The contribution tested here is its ternary
rank-three specialization, where the degree-three Reed--Muller density `2/9`
still beats the nonprimitive density `1/9`:

- <https://cdn.openai.com/pdf/ten-proofs-oai.pdf#page=106>

## 2. The measure criterion

Cornulier and Tessera prove the following criterion for a semidirect product
with abelian normal subgroup ([Theorem 1](https://www.normalesup.org/~cornulier/relt.pdf)).
The pair `(A⋊Γ,A)` fails relative property (T) exactly when there are
probability measures `μ_r` on `dual(A)` such that

```text
(P1) μ_r → δ_0 weakly,
(P2) μ_r({0}) = 0,
(P3) ||g_*μ_r-μ_r||_TV → 0 for every g∈Γ.       (2.1)
```

We rule out (2.1) on `E_n=L×Q`.

## 3. Property (T) turns almost-invariant measures into invariant measures

We use this standard consequence of property (T).

> **Measure-stability lemma.** If a countable group `Γ` has property (T), acts
> on a standard Borel space `X`, and probabilities `μ_r` satisfy (P3), then
> there are `Γ`-invariant probabilities `ν_r` with
> `||μ_r-ν_r||_TV→0`.

Here is a proof sketch that records the needed uniformity. For each `r`, form a
probability `λ_r` equivalent to every translate of `μ_r`, for example a
strictly positive weighted sum of `g_*μ_r` over an enumeration of `Γ`. In
the Radon–Nikodym Koopman representation on `L²(X,λ_r)`, the vector

```text
ξ_r = sqrt(dμ_r/dλ_r)
```

is almost invariant; squared Hellinger distance is bounded by total variation.
A fixed Kazhdan pair for `Γ` makes `ξ_r` uniformly close to the invariant
subspace. The absolute value of its invariant projection is still invariant and
nonnegative. After normalization, its square is the density of an invariant
probability `ν_r`. The `L²` estimate implies
`||μ_r-ν_r||_TV→0`.

The required property (T) of `Γ` is classical: `SL₃` over a local field has
property (T), lattices inherit it, and `SL₃(F₃[t])` is a lattice in
`SL₃(F₃((1/t)))`; see
[Bekka–de la Harpe–Valette](https://perso.univ-rennes1.fr/bachir.bekka/KazhdanTotal.pdf).

## 4. Finite boxes and primitive vectors

Let `V_N` be the `3N`-dimensional `F₃`-space of polynomial vectors whose
coordinates have degree `<N`. Its cardinality is `3^(3N)`.

A vector is primitive if its three polynomial coordinates have gcd one. The
exact count is

```text
|Prim_N| = 3^(3N) - 3^(3N-2) + 2,
|V_N\Prim_N| = 3^(3N-2) - 2 < |V_N|/9.   (4.1)
```

One direct derivation classifies a nonzero vector by its monic gcd. There are
`3^d` monic degree-`d` polynomials, giving

```text
3^(3N)-1 = Σ_{d=0}^{N-1} 3^d |Prim_(N-d)|,
```

whose solution is (4.1). The repository also contains a Lean proof candidate
and exhaustive Julia checks.

Every primitive vector is the first column of an elementary matrix: over the
PID `F₃[t]`, a unimodular column can be completed to an `SL₃` matrix, and
`E₃(F₃[t])=SL₃(F₃[t])`. Choose once and for all

```text
g_v∈Γ,  g_v e₁=v,  for every v∈Prim_N.             (4.2)
```

The set in (4.2) is finite for each `N`; no word-length uniformity is needed
after we pass to invariant measures.

## 5. The linear marginal detector on `L`

Fix the clopen set

```text
D_L = { ℓ∈L : ℓ(e₁)≠0 }.
```

Let `ρ` be a `Γ`-invariant probability on `L`. For a nonzero `ℓ`, choose
`N` such that `ℓ|V_N≠0`. The linear function `v↦ℓ(v)` is nonzero on
exactly `2/3` of `V_N`. Discarding all nonprimitive vectors loses less than
`1/9` of the box, so at least a `5/8` fraction of `Prim_N` is detected:

```text
|{v∈Prim_N : ℓ(v)≠0}| / |Prim_N| ≥ 5/8.        (5.1)
```

Average the indicator of `D_L` over the elements `g_v⁻¹` from (4.2).
Invariance of `ρ` makes the integral of every translate equal to
`ρ(D_L)`, while (5.1) bounds the pointwise average on the set where
`ℓ|V_N≠0`. Letting `N→∞` and using countable additivity gives

```text
ρ(D_L) ≥ (5/8) ρ(L\{0}).                         (5.2)
```

## 6. The cubic marginal detector on `Q`

Let `B_N⊆B` be the span of pure cubes `v⊗³`, `v∈V_N`, and set

```text
D_Q = { q∈Q : q(e₁⊗³)≠0 }.
```

If `q|B_N≠0`, then

```text
P_q(v)=q(v⊗³),  v∈V_N,
```

is a nonzero reduced ternary polynomial of total degree at most three in `3N`
scalar variables. The degree-three generalized Reed–Muller bound gives

```text
|{v∈V_N : P_q(v)≠0}| ≥ (2/9)|V_N|.              (6.1)
```

After discarding the nonprimitive vectors from (4.1), at least a `1/8`
fraction of `Prim_N` remains detected:

```text
|{v∈Prim_N : q(v⊗³)≠0}| / |Prim_N| ≥ 1/8.        (6.2)
```

The repository proves (6.1) by a simultaneous slice induction through degrees
zero to three. The constants are exact:

```text
(2/9 - 1/9)/(1 - 1/9) = 1/8.
```

Now let `σ` be a `Γ`-invariant probability on `Q`. Average the indicator
of `D_Q` over `g_v⁻¹`. Since

```text
(g_v⁻¹·q)(e₁⊗³)=q(v⊗³),
```

the same finite-average and monotone-limit argument gives

```text
σ(D_Q) ≥ (1/8) σ(Q\{0}).                         (6.3)
```

## 7. The joint detector improves `5/48` to `1/8`

The two marginal estimates above are useful checks, but combining them only
after integration loses information. A pointwise joint count is stronger.

For `z=(ell,q)∈L×Q` and `v∈V`, say that `v` detects `z` if

```text
ell(v) != 0  or  q(v⊗³) != 0.
```

Let `U_N` be the set of points detected by at least one vector of `V_N`. If
`z∈U_N`, at least one of the reduced polynomials

```text
v |-> ell(v),             v |-> q(v⊗³)
```

is nonzero on `V_N`. The first has support density `2/3`; the second has
support density at least `2/9`. Thus at least `(2/9)|V_N|` vectors detect
`z`. Removing every nonprimitive vector loses fewer than `(1/9)|V_N|`, so
at least a `1/8` fraction of `Prim_N` detects `z`, exactly as in (6.2).

Put

```text
D = {(ell,q) : ell(e₁) != 0 or q(e₁⊗³) != 0}.
```

For every primitive `v`, choose `g_v e₁=v`. The coordinate action gives

```text
(g_v^-1 . z) is in D  iff  v detects z.
```

If `nu` is any `Γ`-invariant probability on `E_n=L×Q`, integrating the
finite average over `Prim_N` therefore gives

```text
nu(D) >= (1/8) nu(U_N).                              (7.1)
```

The sets `U_N` increase to `E_n\{0}`: a nonzero `ell` is nonzero on some
finite box, while a nonzero `q` is nonzero on some pure cube because pure
cubes span `B`. Monotone convergence upgrades (7.1) to the fixed escape bound

```text
nu(D) >= (1/8) nu(E_n\{0}).                          (7.2)
```

The set `D` is clopen and does not contain the identity. The earlier marginal
argument gave `5/48`; (7.2) is both simpler and stronger.

## 8. Contradiction to the Cornulier–Tessera sequence

Assume relative property (T) fails and take `μ_r` satisfying (2.1). By the
measure-stability lemma, choose invariant `ν_r` with
`||μ_r-ν_r||_TV→0`.

Because `μ_r({0})=0`,

```text
ν_r(E_n\{0}) → 1.
```

The escape inequality (7.2) therefore gives

```text
liminf ν_r(D) ≥ 1/8.                               (8.1)
```

On the other hand, `μ_r→δ_0` and `D` is clopen away from zero, so
`μ_r(D)→0`; total-variation closeness gives `ν_r(D)→0`, contradicting
(8.1). Thus `(G_n,A_n)` has relative property (T).

Finally, `G_n/A_n≅Γ` has property (T). The standard extension theorem

```text
(G_n,A_n) relative (T) + G_n/A_n property (T)
    ⇒ G_n property (T)
```

proves the claim.

## 9. Independent factor-transfer proof

There is a second route that avoids the measure-stability lemma and provides a
useful cross-check. Put

```text
H = (V direct-sum B) semidirect Γ.
```

The compact dual of `V direct-sum B` is `L×Q` with the coordinatewise group
law. Let `zeta=exp(2 pi i/3)` and choose the two module elements

```text
a_1=(e₁,0),              a_2=(0,e₁⊗³).
```

For the character indexed by `(ell,q)`, membership in `D` implies

```text
|zeta^(ell(e₁))-1|^2 + |zeta^(q(e₁⊗³))-1|^2 >= 3.
```

Therefore every invariant probability `nu` satisfies the spectral estimate

```text
sum_(j=1)^2 integral |chi(a_j)-1|^2 dnu(chi)
  >= (3/8)(1-nu({0})).                                (9.1)
```

The standard abelian-by-property-(T) spectral lemma proves that `H` has
property (T). The orbit theorem makes `H` ICC. The common measured action then
gives

```text
L(H) isomorphic to L(G_n).
```

The group-factor criterion makes `G_n` ICC, and the Connes--Jones
characterization transfers property (T) from the factor `L(H)` to `G_n`.
This is the route used structurally in the published binary construction; the
ternary constant in (9.1) is `3/8`, corresponding to `4/7` in the binary
rank-four case.

The two proofs have complementary dependencies:

- Sections 2--8 directly prove the stronger relative property (T) statement
  for the nonsplit carry group, but use measure stability and
  Cornulier--Tessera.
- Section 9 uses the common-factor bridge and Connes--Jones, but only needs the
  standard spectral lemma for the split module.

## 10. Consequence and claim boundary

Combined with the other proof candidates, this gives the following coherent
candidate package:

```text
G_n are finitely generated, ICC, property (T), and pairwise nonisomorphic,
while L(G_n), C*(G_n), and C*_r(G_n) are independent of n.
```

If every bridge survives formalization and independent review, any pair
`G_m,G_n` with `m≠n` is an alternative ternary counterexample to Connes's
rigidity conjecture. The conjecture already has a public binary-carry
counterexample, so this would not be the first disproof.

That conclusion is **not promoted as an established theorem here**. The
relative-(T) measure argument, the Bockstein identification, the compact-dual
construction, and their interfaces must be checked by specialists and
machine formalization. Search results and internal consistency are not proof
of novelty or correctness.

## 11. Formalization obligations

1. formalize the Cornulier–Tessera probability criterion in the discrete case;
2. prove the property-(T) measure-stability lemma with explicit TV bounds;
3. formalize primitive-vector completion to elementary matrices;
4. connect the reduced cubic evaluation polynomial to `q|B_N≠0`;
5. install the `2/9`, `1/8`, and `5/8` finite detector bounds;
6. formalize joint detection and invariant-measure averaging over `Prim_N`;
7. pass to the increasing union of finite boxes and obtain the `1/8` escape
   bound;
8. retain the marginal estimates as independent consistency checks;
9. derive relative property (T) and then property (T) for `G_n`;
10. independently formalize the split-module spectral estimate `3/8` and the
    common-factor/Connes--Jones transfer route.
