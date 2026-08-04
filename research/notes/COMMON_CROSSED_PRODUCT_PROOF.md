# Common von Neumann and C*-algebras from the carry coordinates

**Status:** complete topological/operator-algebra proof candidate, conditional
only on installing the algebraic carry construction as the compact Pontryagin
dual of the discrete groups. No property-(T) input is used.

**Priority boundary:** this mechanism is not new. Chapter 4 of OpenAI's 2026
*Ten Advances in Mathematics and Theoretical Computer Science* proves the
binary version, including the same triangular Haar argument and common crossed
product. This note records the ternary specialization and its full/reduced
`C*` consequences:

- <https://cdn.openai.com/pdf/ten-proofs-oai.pdf#page=98>

## 1. The common compact carrier

Let

```text
V = F₃[t]³,
B = the ternary divided-cube module,
L = Hom_F₃(V,F₃),
Q = Hom_F₃(B,F₃).
```

Give `L` and `Q` their product topologies in monomial/multiset coordinates.
Both are countable products of the finite discrete group `F₃`, hence compact,
metrizable, totally disconnected abelian groups. Write their normalized Haar
measures as `μ_L` and `μ_Q`.

For every shift `n`, the carry cocycle

```text
c_n : L×L → Q
```

defines a group `E_n` on the same topological carrier `L×Q`:

```text
(ℓ,q) +_n (m,r) = (ℓ+m, q+r+c_n(ℓ,m)).       (1.1)
```

The Lean algebraic model already proves normalization, symmetry, and the
cocycle identity, so (1.1) is abelian and associative.

## 2. Continuity

The topology on `Q` is initial for the evaluations `q↦q(b)`, `b∈B`. For a
fixed `b`, choose a finite expression of `b` as a linear combination of pure
cubes. The coordinate

```text
(ℓ,m) ↦ c_n(ℓ,m)(b)
```

is then a polynomial over `F₃` in finitely many evaluations of `ℓ` and `m`
on shifted polynomial vectors. It is continuous. Hence `c_n` is continuous in
the product topology, and so are the multiplication and inverse in `E_n`.
Thus every `E_n` is a compact metrizable abelian topological group on the same
underlying compact space.

## 3. Haar measure does not see the cocycle

The product probability measure

```text
μ = μ_L × μ_Q                                  (3.1)
```

is Haar measure for every group law (1.1). Indeed, left translation by
`(a,b)` sends

```text
(ℓ,q) ↦ (a+ℓ, b+q+c_n(a,ℓ)).                   (3.2)
```

For each fixed `ℓ`, the second coordinate is a translation of `Q`, so the
inner `Q` integral is unchanged. The remaining first coordinate is a
translation of `L`, so the outer integral is unchanged. Fubini therefore
proves invariance of (3.1); uniqueness of normalized Haar measure finishes the
claim.

This is the key observation: changing `n` changes the compact group law but
not its Haar probability space.

## 4. The action is independent of the shift

Let `Γ=E₃(F₃[t])=SL₃(F₃[t])`. For `g∈Γ`, define

```text
g·(ℓ,q) = (ℓ∘g⁻¹, q∘(g⁻¹)⊗³).                 (4.1)
```

The shifted-carry naturality theorem says that (4.1) is a continuous group
automorphism of every `E_n`. Crucially, the coordinate formula (4.1) contains
no `n`. The formal shear-action file already exposes this fact: both its base
and fiber projections are the same pullbacks for every shift.

Consequently the identity map on `L×Q` is a measure-preserving conjugacy

```text
(E_n,μ,Γ) ≅ (E_m,μ,Γ)                         (4.2)
```

of probability actions. It is generally not a homomorphism `E_n→E_m`, and
does not need to be one.

## 5. Fourier transform and the common group factor

Let

```text
A_n = dual(E_n),
G_n = A_n ⋊ Γ.
```

Since `E_n` is compact metrizable, `A_n` is countable discrete. Pontryagin
Fourier transform identifies the group von Neumann algebra of `A_n` with the
multiplication algebra on its compact dual and intertwines the `Γ` actions.
The standard semidirect-product formula is therefore

```text
L(G_n) ≅ L∞(E_n,μ) ⋊ Γ.                       (5.1)
```

The formula and the exact "same measured action, different compact group law"
use are now explicit in the published binary counterexample cited above; the
formula itself is standard and is an immediate calculation on the Fourier
basis.

Applying the action conjugacy (4.2) to (5.1) gives canonical trace-preserving
isomorphisms

```text
L(G_n) ≅ L∞(L×Q,μ) ⋊ Γ ≅ L(G_m)              (5.2)
```

for all `m,n`. In coordinates the middle crossed product is literally the
same represented algebra, not merely an abstractly classified copy.

Once the ICC proof in `FINITE_ORBIT_INVARIANT_PROOF.md` is installed, these
are isomorphic `II₁` factors.

## 6. Full and reduced group C*-algebras

The same conjugacy gives more. For a discrete abelian group,

```text
C*(A_n) = C*_r(A_n) ≅ C(E_n).
```

Fourier transform and the semidirect-product universal/regular
representations yield

```text
C*(G_n)   ≅ C(E_n) ⋊_max Γ,
C*_r(G_n) ≅ C(E_n) ⋊_r Γ.                          (6.1)
```

The identity homeomorphism of the carriers conjugates the actions on
`C(E_n)`, so both crossed products in (6.1) are independent of `n`. Thus the
construction candidate gives common full and reduced group C*-algebras as
well as common group von Neumann algebras.

This does **not** automatically identify the algebraic complex group rings:
the trigonometric-polynomial subalgebras depend on the compact group law even
though their C*- and von Neumann completions do not.

## 7. The ternary family is mutually commensurable

The shift also gives a finite-index relation, paralleling the published binary
family. Let

```text
T_n : L -> L,             T_n(ell)(v)=ell(t^n v).
```

The full algebraic dual makes `T_n` surjective: extend a functional on `t^nV`
to `V`. Its kernel is

```text
Z_n = Hom_F3(V/t^nV,F3),        |Z_n|=3^(3n).
```

Because the shifted cocycle is the pullback of the unshifted cocycle,

```text
p_n : E_n -> E_0,       p_n(ell,q)=(T_n ell,q)          (7.1)
```

is a continuous surjective `Γ`-equivariant homomorphism with kernel
`Z_n×{0}`. Pontryagin duality gives an injective equivariant homomorphism

```text
p_n^ : A_0 -> A_n,       [A_n:p_n^(A_0)]=3^(3n).       (7.2)
```

It extends across the common acting group to

```text
G_0 -> G_n,              [G_n:G_0]=3^(3n).             (7.3)
```

Thus the candidate groups are mutually commensurable. Property (T) can also be
transferred from `G_0` to all `G_n` through (7.3), once it is proved for one
member. This is a ternary specialization of the finite-index argument in the
binary counterexample, not a novelty claim.

## 8. Formalization obligations

1. equip the two algebraic duals with their coordinate product topologies;
2. prove compactness, metrizability, and continuity of every carry coordinate;
3. construct `E_n` as a compact abelian topological group;
4. formalize the Fubini proof that product measure is Haar for every `n`;
5. extend the generator-level shear action to `Γ` and prove (4.1);
6. construct the Pontryagin dual `A_n` and the semidirect product `G_n`;
7. install the Fourier equivalences (5.1) and (6.1);
8. verify trace preservation and the ICC-to-factor conclusion.
9. construct `p_n`, compute its finite kernel, and dualize it to the
   finite-index inclusions (7.2)--(7.3).

The ternary relative-property-(T) bridge now also has a paper proof candidate.
What remains is formalization and independent review of the interfaces; common
operator-algebra completions are not a conceptual obstruction and are not a
novel mechanism of this repository.
