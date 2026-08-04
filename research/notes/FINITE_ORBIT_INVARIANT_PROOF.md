# The intrinsic finite-orbit invariant: an exact-sequence proof

**Status:** complete algebraic proof candidate. The module invariant is proved
below, and the characteristic-subgroup step follows from classical higher-rank
lattice theorems with precise references. The Bockstein dualization and the
full construction still require formalization and independent review.

**Priority boundary:** the binary exact analogue
`0 -> V/t^nV -> E_n[2]/2E_n -> ker d_2 -> 0` and its finite-orbit recovery are
already in Chapter 4, Lemma 6.8 of OpenAI's 2026 counterexample manuscript.
This note is a ternary specialization with a different characteristic-subgroup
argument, not a claim to the mechanism:

- <https://cdn.openai.com/pdf/ten-proofs-oai.pdf#page=111>

## 1. Why the raw shifted kernel is not yet intrinsic

The compact carry calculation gives a distinguished linear map whose kernel
has size `3^(3n)`. A group isomorphism, however, is not required to preserve the
chosen base/fiber coordinates or that chosen map. Calling this kernel
“intrinsic” before recovering it from the abstract group would be circular.

There is also a serious absorption warning. The Pontryagin duals are countable
abelian groups of exponent nine with infinite `Z/9` and `Z/3` ranks. Finite
changes in one rank are generally swallowed by those infinite multiplicities.
Thus the underlying abelian groups should not be expected to distinguish `n`.
The action and a canonical subquotient must do the work.

## 2. The discrete extension and its Bockstein

Let `E_n` be the compact shifted carry extension and let

```text
A_n = dual(E_n)
```

be its discrete Pontryagin dual. Dualizing the compact base/fiber sequence gives
an exact sequence of `F₃[Γ]`-modules

```text
0 → V → A_n --π→ B → 0,                 (2.1)
```

where

```text
Γ = E₃(F₃[t]),   V = F₃[t]^3,
B = the divided-cube module.
```

Both `V` and `B` are killed by `3`, while `A_n` is killed by `9`. Every such
extension has a canonical Bockstein

```text
β_n : B → V,
β_n(b) = 3a  for any lift a with π(a)=b.  (2.2)
```

This is well-defined because changing the lift adds an element of `V`, and
`3V=0`.

Dualizing the proved compact multiplication-by-three formula identifies

```text
β_n = t^n d₃.                            (2.3)
```

Since `d₃` is onto and multiplication by `t^n` is injective,

```text
im β_n = t^n V,
ker β_n = K = ker d₃.                    (2.4)
```

The exact identification (2.3) is an important formalization obligation; the
existing compact-side Lean modules contain its dual ingredients but not yet
this discrete exact sequence.

## 3. A canonical 3-torsion subquotient

For an abelian group `A`, write

```text
A[3] = {a ∈ A : 3a=0}.
```

Equations (2.1) and (2.2) give a canonical exact sequence

```text
0 → V / im β_n → A_n[3] / 3A_n → ker β_n → 0.   (3.1)
```

Here is the direct proof.

- Multiplication by three on a lift of `b∈B` is `β_n(b)`, so
  `3A_n=im β_n⊆V`.
- An element `a∈A_n` is killed by three exactly when its image `π(a)` lies in
  `ker β_n`.
- The kernel of `A_n[3]→ker β_n` is `V`; quotienting source and kernel by
  `3A_n=im β_n` gives (3.1).

Using (2.4), this becomes

```text
0 → V/t^nV → A_n[3]/3A_n → K → 0.        (3.2)
```

## 4. Recovering the finite piece from orbit behavior

Define the finite-orbit subgroup of the canonical subquotient by

```text
FinOrb_n = {x ∈ A_n[3]/3A_n : Γ·x is finite}.
```

The left term in (3.2) is finite:

```text
|V/t^nV| = 3^(3n).
```

Therefore all its elements have finite orbit. Conversely, if `x` maps to a
nonzero element of `K`, then the orbit of its image is infinite by the
rank-three divided-cube orbit theorem. An equivariant image of a finite orbit is
finite, so `x` itself must have infinite orbit. Hence

```text
FinOrb_n = V/t^nV,
|FinOrb_n| = 3^(3n).                      (4.1)
```

This is the needed ternary upgrade: the parameter is recovered without
mentioning a chosen carry coordinate, fiber projection, or shifted map. It is
the finite-orbit part of the characteristic subquotient `A[3]/3A`.

Since `n ↦ 3^(3n)` is injective, the `Γ`-modules `A_n` are pairwise
nonisomorphic whenever isomorphisms are required to respect the action up to an
automorphism of `Γ` that preserves orbit finiteness.

## 5. Promotion to the semidirect-product group

Let

```text
G_n = A_n ⋊ Γ.
```

Inside a known semidirect product, conjugation on `A_n` is exactly the
`Γ`-action, because `A_n` is abelian. Thus (4.1) becomes a finite-conjugacy
invariant of `A_n[3]/3A_n`.

To make it intrinsic under an arbitrary group isomorphism `G_m ≅ G_n`, it
suffices to prove that `A_n` is characteristic in `G_n`. In fact

```text
A_n = Rad_am(G_n),
```

the amenable radical. Here are all of the required inputs.

1. Since `F₃[t]` is Euclidean, elementary row reduction gives
   `E₃(F₃[t])=SL₃(F₃[t])`.
2. `SL₃(F₃[t])` is the nonuniform lattice in
   `SL₃(F₃((1/t)))`; see, for example, the explicit statement in
   [Klingler, lines 130–132](https://epiga.episciences.org/5491/pdf) or
   [Douba–Kubrak–Tsouvalas, Corollary 3](https://arxiv.org/abs/2505.13639).
3. Margulis's normal subgroup theorem applies to this irreducible rank-two
   lattice: a normal subgroup is finite central or has finite index
   ([Margulis, Theorem IX.5.6](https://doi.org/10.1007/978-3-642-51445-6)).
4. The center is trivial. A central matrix is `λI` with
   `λ∈F₃[t]^×=F₃^×` and `λ³=1`; only `λ=1` works.
5. The lattice has property (T): `SL₃` over any local field has property
   (T), and lattices inherit it
   ([Bekka–de la Harpe–Valette, Introduction](https://perso.univ-rennes1.fr/bachir.bekka/KazhdanTotal.pdf)).
   It is infinite, so it cannot be amenable, because a discrete amenable
   property-(T) group is finite.

Now let `N ◁ G_n` be amenable. Its image in `Γ` is normal and amenable.
Margulis's dichotomy makes that image either trivial or finite index. The
finite-index case would make `Γ` amenable, which is impossible; the finite
central case is trivial because the center is trivial. Thus `N⊆A_n`.
Conversely `A_n` is normal and abelian, hence amenable, proving
`A_n=Rad_am(G_n)` and therefore characteristicity.

Every group isomorphism consequently preserves

```text
A_n,  A_n[3],  3A_n,
```

and finite conjugacy in their quotient. It therefore preserves `|FinOrb_n|`,
forcing `m=n`. Conditional only on the construction and Bockstein
identification (2.1)–(2.3), the semidirect products `G_n` are therefore
pairwise nonisomorphic.

## 6. Consequences for finite generation and ICC

The cyclicity proof for `B` also closes most of two neighboring algebraic
obligations.

- `V` is cyclic as a `Γ`-module, and the new proof makes `B` cyclic. An
  extension (2.1) is therefore finitely generated as a `Γ`-module after choosing
  one lift of a generator of `B`. With finite generation of `Γ`, this gives
  finite generation of `G_n`.
- If `0≠a∈A_n` maps nontrivially to `B`, its orbit is infinite by the divided
  cube theorem. If its image is zero, it is a nonzero vector `v∈V`: choose
  `j` with `v_j≠0` and `i≠j`; then the vectors
  `u_ij(t^N)v` are pairwise distinct because `F₃[t]` is a domain. Thus every
  nonzero element of `A_n` has an infinite conjugacy class.
- The FC-center of any group is amenable. Since Section 5 proves that `Γ` has
  trivial amenable radical, its FC-center is trivial; hence `Γ` is ICC. Every
  element of `G_n` with nontrivial image in `Γ` has an infinite conjugacy
  class already in the quotient. Therefore `G_n` is ICC.

The compact topology, Haar action, crossed-product equivalence, and ternary
relative-property-(T) detector are closed at paper-proof level in the companion
notes. The remaining work is to formalize and independently review their
interfaces.

## 7. Lean handoff

The proof decomposes into exact formal tasks:

1. define the discrete dual extension or an algebraic model of it;
2. define the Bockstein of an exponent-nine extension;
3. prove `β_n=t^n d₃` by dualizing multiplication by three;
4. prove the general exact sequence (3.1);
5. specialize it to (3.2);
6. define finite-orbit elements and prove they form a subgroup;
7. use the infinite-orbit theorem to prove (4.1);
8. formalize the classical amenable-radical argument in `G_n`;
9. deduce pairwise nonisomorphism, finite generation, and ICC.

No property-(T) or von Neumann algebra conclusion is used in this argument.
