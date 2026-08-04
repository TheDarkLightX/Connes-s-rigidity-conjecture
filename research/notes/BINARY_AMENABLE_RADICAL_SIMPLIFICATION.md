# Removing the torsion-free acting-group detour in the binary construction

**Status:** complete paper proof candidate obtained by recombining the published
binary construction with the amenable-radical argument developed for the
ternary model. It requires expert review, especially of the positive-
characteristic normal-subgroup-theorem invocation.

**Claim boundary:** this does not give a new counterexample—the counterexample
is already public. It is a candidate simplification of its group-theoretic
architecture.

## 1. The published detour

Chapter 4 of OpenAI's 2026 *Ten Advances in Mathematics and Theoretical
Computer Science* constructs a torsion-free ICC property-(T) group

```text
K = ker(SL_4(Z[t]) -> SL_4(F_3))
```

that surjects onto

```text
Q = SL_4(F_2[t]).
```

The action on the binary modules factors through `Q`. Torsion-freeness of `K`
is then used to recover the abelian normal subgroup of each semidirect product
as its torsion subgroup. Remark 3.4 says that `Q` cannot replace `K` in that
argument because `Q` itself contains an element of order four:

- <https://cdn.openai.com/pdf/ten-proofs-oai.pdf#page=100>

The observation here is that the torsion subgroup is not the only intrinsic
way to recover the abelian layer. The amenable radical works with `Q` directly.

## 2. Simplified family

Retain all binary modules and compact carry groups from the published paper:

```text
R = F_2[t],       V=R^4,
B = span_F2 {v tensor v : v in V},
D = V direct-sum B,
C_n = the shifted compact binary carry group,
E_n = dual(C_n).
```

Replace the auxiliary group `K` everywhere by `Q=SL_4(R)` and define

```text
Lambda_bar = D semidirect Q,
Gamma_bar_n = E_n semidirect Q.                         (2.1)
```

The candidate theorem is that the complete conclusion of the binary
construction still holds:

```text
Lambda_bar, Gamma_bar_0, Gamma_bar_1, ...
```

are finitely generated ICC property-(T) groups; the `Gamma_bar_n` are pairwise
nonisomorphic and mutually commensurable; `Lambda_bar` is not isomorphic to
any `Gamma_bar_n`; and all their group von Neumann algebras are isomorphic.

## 3. The acting group has trivial amenable radical

The required classical facts are shorter than the auxiliary-group
construction. Since `F_2[t]` is Euclidean,

```text
Q=SL_4(F_2[t])=E_4(F_2[t]).
```

The Ershov--Jaikin-Zapirain theorem for elementary linear groups over finitely
generated rings gives property (T) directly. In particular, the infinite group
`Q` is nonamenable. Equivalently, one may obtain property (T) from its
higher-rank lattice realization

```text
Q < SL_4(F_2((1/t))).
```

This realization also puts `Q` under the positive-characteristic form of
Margulis's normal subgroup theorem: every normal subgroup is finite or finite
index.

For completeness, the finite case and ICC can be disposed of by the same
elementary calculation. Suppose `x in Q` has a finite conjugacy class. For
fixed `i!=j`, two distinct polynomials `f,h` give the same conjugate under
`u_ij(f)` and `u_ij(h)`. Hence `x` commutes with `u_ij(h-f)`, so

```text
(h-f)(E_ij x-x E_ij)=0.
```

The coefficient ring is a domain, whence `x` commutes with every matrix unit
`E_ij`. Thus `x` is scalar. Since `F_2[t]^x={1}`, it follows that `x=I`.
Consequently `Q` is ICC and every finite normal subgroup is trivial.

If `N` is an amenable normal subgroup of `Q`, the finite-index alternative
would make `Q` amenable, while the finite alternative is trivial. Therefore

```text
Rad_am(Q) = {1}.                                         (3.1)
```

The FC-center of a group is amenable, so (3.1) also implies that `Q` is ICC.

## 4. The abelian layer is characteristic without torsion-freeness

Use the following elementary lemma.

> **Amenable-radical lemma.** If an abelian group `A` is acted on by a group
> `H` with trivial amenable radical, then
> `Rad_am(A semidirect H)=A`.

Indeed `A` is amenable and normal. Conversely, the image in `H` of any
amenable normal subgroup of `A semidirect H` is an amenable normal subgroup of
`H`, hence trivial.

Applying the lemma to (2.1) gives

```text
Rad_am(Lambda_bar)=D,
Rad_am(Gamma_bar_n)=E_n.                                (4.1)
```

Thus `D` and `E_n` are characteristic even though `Q` has torsion.

This immediately replaces the first use of torsion-freeness. The group `D`
has exponent two, while every `E_n` has an element of order four. An
isomorphism `Lambda_bar -> Gamma_bar_n` would identify their amenable radicals,
which is impossible. Hence

```text
Lambda_bar is not isomorphic to Gamma_bar_n.            (4.2)
```

## 5. Pairwise nonisomorphism survives unchanged

Because `E_n` is characteristic, the quotient action of
`Gamma_bar_n/E_n=Q` on

```text
E_n[2]/2E_n
```

is intrinsic. The published Bockstein calculation and infinite-orbit theorem
give

```text
0 -> V/t^nV -> E_n[2]/2E_n -> ker d_2 -> 0,
FinOrb(E_n[2]/2E_n) = V/t^nV,
|FinOrb(E_n[2]/2E_n)| = 2^(4n).                         (5.1)
```

These statements were already proved for the `Q`-action—the auxiliary `K`
acted only through its surjection onto `Q`. An abstract group isomorphism
preserves (4.1), the quotient action, and finite orbit cardinality. Equation
(5.1) therefore forces `m=n`, proving that the `Gamma_bar_n` are pairwise
nonisomorphic.

## 6. ICC and property (T)

The published orbit and spectral estimates use only the `Q`-action.

- Every nonzero element of `D` has an infinite `Q`-orbit. Together with the
  direct finite-conjugacy-class calculation in Section 3, this makes
  `Lambda_bar` ICC.
- `Q` has property (T). The primitive-vector and quadratic Boolean detector
  gives the invariant spectral constant `4/7`, so the standard
  abelian-by-property-(T) lemma makes `Lambda_bar` a property-(T) group.

There is also a direct route for every carry group, so factor transfer is not
needed to establish its group properties. The published equivariant sequence

```text
0 -> V -> E_n -> B -> 0
```

and infinite-orbit lemma imply that every nonzero element of `E_n` has an
infinite `Q`-orbit: project to `B` unless the element lies in `V`. Since `Q` is
ICC, this makes `Gamma_bar_n` ICC directly.

For property (T), the compact dual of `E_n` has the same pointed `Q`-space
`X x Y` as the split module. The published `1/7` invariant-measure detector is
therefore unchanged. Property (T) of `Q` turns an asymptotically invariant
probability into a nearby invariant one; the detector then contradicts the
Cornulier--Tessera failure sequence. Thus

```text
(Gamma_bar_n,E_n) has relative property (T),
Gamma_bar_n has property (T).                            (6.1)
```

This direct route is the binary analogue of the argument in
`RELATIVE_PROPERTY_T_PROOF.md`.

The measured `Q`-space underlying `dual(D)` and every `C_n` is the same, hence

```text
L(Lambda_bar) isomorphic to L(Gamma_bar_n).              (6.2)
```

The group-factor criterion and Connes--Jones characterization still provide an
independent transfer check across (6.2), just as in the published proof.
Countable discrete property-(T) groups are finitely generated.

## 7. Commensurability

The published shift-forgetting quotient `C_n -> C_0` is already
`Q`-equivariant. Dualizing it gives

```text
Gamma_bar_0 -> Gamma_bar_n,
[Gamma_bar_n:Gamma_bar_0] = 2^(4n).                     (7.1)
```

Thus the simplified family remains mutually commensurable.

## 8. What was removed

If the argument survives review, the following ingredients are unnecessary
for the counterexample:

1. the integral polynomial group `SL_4(Z[t])`;
2. the congruence kernel modulo three;
3. the proof that this kernel is torsion-free;
4. the strong-approximation/surjectivity construction onto `SL_4(F_2[t])`;
5. recovery of the abelian layer as the full torsion subgroup.

They are replaced by the higher-rank lattice facts for `Q` and the one-line
amenable-radical lemma.

## 9. Adversarial checks

1. Confirm the exact normal subgroup theorem hypotheses for the nonuniform
   lattice `SL_4(F_2[t])` in positive characteristic.
2. Verify there is no nontrivial finite normal subgroup hidden by the center
   calculation.
3. Check that every published action, orbit, detector, carry, and
   finite-index map is genuinely `Q`-equivariant, not merely `K`-equivariant.
4. Re-run the abstract-isomorphism argument with a quotient automorphism of
   `Q`; only orbit finiteness, not a chosen identification of `Q`, may be used.
5. Obtain author/expert review before advertising the proof as a simplification.

## References

- OpenAI, Chapter 4, [A Counterexample to Connes's Rigidity
  Conjecture](https://cdn.openai.com/pdf/ten-proofs-oai.pdf#page=95).
- G. Margulis, *Discrete Subgroups of Semisimple Lie Groups*, Theorem IX.5.6,
  <https://doi.org/10.1007/978-3-642-51445-6>.
- M. Ershov and A. Jaikin-Zapirain,
  [Property (T) for noncommutative universal
  lattices](https://arxiv.org/abs/0809.4095).
- B. Bekka, P. de la Harpe, and A. Valette,
  [Kazhdan's Property (T)](https://perso.univ-rennes1.fr/bachir.bekka/KazhdanTotal.pdf).
- Y. de Cornulier and R. Tessera,
  [A characterization of relative Kazhdan property T for semidirect products
  with abelian groups](https://arxiv.org/abs/0911.3371).
