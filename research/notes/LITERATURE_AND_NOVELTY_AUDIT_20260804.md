# Literature and novelty audit — 4 August 2026

This note separates current problem status, classical ingredients, plausible
new statements, and failed identifications. Search misses are never treated as
proof of novelty.

## 1. Current status of Connes's rigidity conjecture

The current public record contains two claimed counterexamples. Chapter 4 of
OpenAI's *Ten Advances in Mathematics and Theoretical Computer Science*,
released at the beginning of August 2026, gives a binary-carry construction: a
countably infinite family of pairwise nonisomorphic, finitely generated ICC
property-(T) groups with isomorphic group von Neumann algebras.

- <https://cdn.openai.com/pdf/ten-proofs-oai.pdf#page=95>

Shuoxing Zhou's independent and concurrent paper gives a second construction:
two semidirect products with the same elementary abelian normal group and
quotient but different actions. A quadratic fiber shear conjugates the dual
probability actions, while a semisimple/nonsemisimple module distinction proves
the groups are nonisomorphic.

- <https://arxiv.org/abs/2608.02327>

This is directly relevant prior art, not merely neighboring work. Its proof
already contains the following architecture:

```text
divided-power module -> carry cocycle on one compact carrier
-> shift-independent Haar action -> common crossed product
-> Bockstein/doubling exact sequence
-> finite-orbit subgroup of E_n[2]/2E_n
-> primitive-vector + Reed--Muller detector -> property (T).
```

The April 2026 paper of Chifan, Fernández Quero, Osin and Tan is useful for the
pre-counterexample status and surrounding `W*`-superrigidity landscape, but it
is no longer the latest source for the conjecture itself:

- <https://arxiv.org/abs/2503.12742>

Jesse Peterson's problem page records the historical formulation:

- <https://math.vanderbilt.edu/peters10/problems.html>

Therefore this repository cannot claim novelty for the common measured-action
strategy, the carry/common-factor strategy, the finite-orbit subquotient
strategy, or the fact of a counterexample. Its public boundary is narrower: it
is an unreviewed ternary rank-three analogue and a source of possible new
modular-representation lemmas and proof simplifications.

### 1.1 A current adversarial manuscript

A 1 August 2026 PhilArchive manuscript by Jenny Lorraine Nielsen claims that
the public counterexamples are invalid and proposes a proof of the conjecture:

- <https://philarchive.org/rec/NIEWTC>

Its public abstract describes an extension of `Z^4 semidirect Sp_4(Z)` and
asserts that the OpenAI and Zhou constructions are the same. Those are not the
objects in either cited public construction: the OpenAI chapter uses a binary
carry over `F_2[t]` with quotient `SL_4(F_2[t])`, while Zhou uses an independent
rank-three action-shear. The abstract also attempts to pass from a bare group-
factor isomorphism to arbitrarily chosen Bernoulli crossed products without
displaying the needed bridge. The PDF was unavailable to the automated reader,
so this is a source-identification audit, not a referee report. The claim is
recorded but does not presently invalidate either construction. See
`ADVERSARIAL_STATUS_AUDIT_20260804.md`.

## 2. Classical ingredients

The repository's earlier TheoremSearch campaign correctly classifies these as
classical:

- recovery of a group from group-like elements of its canonical group-algebra
  Hopf structure;
- the scalar length-two Witt identification with `Z/9` and its Teichmüller
  coordinate;
- the generalized Reed–Muller minimum-support input behind the `2/9` detector.

Formalization or a new use of these facts can be valuable, but the facts
themselves should not carry novelty labels.

## 3. Divided-power current algebra, not the ordinary Lie algebra

The seven-dimensional constant Frobenius kernel is the modular adjoint quotient
`psl₃`. This initially suggested that the polynomial kernel might be the
ordinary global Weyl module of highest weight `ω₁+ω₂`.

The Hilbert series disproves that naive identification: the kernel has
quadratic degree growth with the multiset series

```text
H_K(q) = 9/(2(1-q)^3) + 9/(2(1-q)(1-q^2)) - 2/(1-q^3),
```

which is far larger than the straightforward two-parameter global-Weyl model.

The structural reason is visible in the new proof. The operation

```text
u(2f)s-u(f)s
```

on a repeated equal-source tensor isolates a group-level divided-power term;
monomial divisibility then reaches every all-distinct basis vector. In positive characteristic the
appropriate current algebra is the divided-power/hyperalgebra version, not
only the ordinary universal enveloping algebra. Webster's *Current algebras and
categorified quantum groups* explicitly makes this positive-characteristic
replacement in Section 3.2:

- <https://arxiv.org/abs/1412.1417>

For comparison, the characteristic-zero tensor/multiplicity construction of
current-algebra modules is described by Bennett and Jenkins:

- <https://arxiv.org/abs/1508.00941>

**Assessment:** the ordinary global-Weyl portal is rejected; the modular
hyperalgebra/current-group portal remains relevant.

## 4. Frobenius twist correction

The standard strict-polynomial viewpoint treats divided powers
`Γ^d(V)=(V^⊗d)^{S_d}` and the Frobenius twist as distinct polynomial functors.
The `p`th-power map is Frobenius-semilinear until its target is twisted. A useful
entry point is the strict-polynomial literature summarized in Franjou,
Friedlander, Scorichenko and Suslin:

- <https://arxiv.org/abs/math/9909194>

The repository now contains its own one-dimensional Lean obstruction: an
untwisted linear cube retraction forces `λ³=λ` for every scalar. This is a
correction to the earlier general-field wording, not a novelty claim about
Frobenius twists.

## 5. Strongest novelty candidates

### 5.1 Stable/critical polynomial-tensor orbit theorem

The formal proof now states the rank-three instance:

```text
For every field F, every nonzero tensor in
Fix(τ₁₂) ⊆ (F[t]^3)^⊗_F 3
has an infinite orbit under elementary transvections in SL₃(F[t]).
```

In fact a single tail `u_ij(t^(N+n))` has an observation with infinite range.
The coordinate argument generalizes. For `2<=m<=r`, every nonzero tensor in
`(F[t]^r)^tensor-m` has infinite elementary orbit when `r>m`; on the critical
diagonal `r=m`, invariance under the first-factor transposition suffices. The
divided power is contained in this fixed subspace. Neither web search nor the
archived TheoremSearch results found this exact statement. Priority remains
unproved; only the rank-three instance is represented in Lean source.

### 5.2 Ternary divided-cube cyclicity

The finite-difference proof that

```text
ker d₃ = span_F₃(E₃(F₃[t]) · [e₁,e₂,e₃])
```

and that the whole divided cube is cyclic appears to be a new proof in this
project. It may be classical in hyperalgebra or strict-polynomial language. The
exact theorem now needs a targeted specialist search, not only semantic web
search.

### 5.3 Finite-orbit subquotient

The exact sequence

```text
0 → V/t^nV → A_n[3]/3A_n → ker d₃ → 0
```

combined with the infinite-orbit theorem gives an intrinsic module invariant of
order `3^(3n)`. The new binary counterexample contains the exact prime-two
analogue

```text
0 -> V/t^nV -> E_n[2]/2E_n -> ker d_2 -> 0
```

and recovers `2^(4n)` by finite orbits. Consequently the *strategy* is prior
art. The ternary formula and its amenable-radical implementation may still be
useful as an alternative realization, but should not be presented as a new
mechanism.

### 5.4 Multivariate ternary cyclicity

The two-step certificate proving cyclicity over every
`F_3[t_1,...,t_d]` is not present in the binary counterexample paper and is
currently the cleanest plausible new algebraic statement in this packet.
Exact bivariate and trivariate quotients agree with the proof ledger. A
specialist search in modular divided powers and current-group representations
is still required.

### 5.4.1 Stable/critical divided-power cyclicity

The proof extends much further. For a prime `p`, a finite-variable polynomial
ring `R=F_p[t_1,...,t_d]`, and rank `r>=p`, the Frobenius kernel in
`Gamma^p(R^r)` is cyclic whenever `r>p` or `p` is odd. In the stable range an
unused coordinate lowers every positive-degree basis multiset. On the critical
odd diagonal `r=p`, the antisymmetrized difference

```text
(u(x)S-u(-x)S)/2
```

isolates the two one-substitution terms. The theorem includes binary rank
three and every odd prime at rank `p`. Exact certificates pass for
`(p,r)=(2,3),(2,4),(3,4),(5,5),(5,6)`. No exact literature match was found,
but semantic search is weak in modular hyperalgebra language; priority is
wholly unestablished.

### 5.5 Prime--rank detector phase diagram

The OpenAI binary paper proves positivity from rank four using primitive
vectors and remarks that its rank-`j` constant becomes positive exactly for
`j>=4`. Combining its method with the degree-`p` generalized Reed--Muller
distance gives

```text
             (p-1)/p^2 - p^(1-r)
c(p,r) =    --------------------- ,
                  1-p^(1-r)
```

positive exactly when `(p-1)p^(r-3)>1`. Zhou's paper shows that the zero at
`(p,r)=(2,3)` is not an impossibility result: affine charts yield `1/12` in
binary rank three. The repository now proves the complementary chart formula

```text
c_chart(p,r)=(r-p)(p-1)/(r p^2), provided p<r,
```

because a degree-`p` polynomial can vanish on at most `p` of the `r` charts.
The threshold `p<r` is sharp for this chart family. The union of the primitive
and chart regions covers every prime and every rank `r>=3`; it recovers Zhou's
`1/12` and the ternary `1/8`. This two-geometry synthesis is proved in
`PRIME_RANK_DETECTOR_PHASE_DIAGRAM.md`. It is a plausible new organizing
observation, not a claimed new theorem of record.

The coding-theory search found established recursive decompositions of
projective Reed--Muller codes into affine pieces, for example San-Jose
([arXiv:2312.05072](https://arxiv.org/abs/2312.05072)). This is adjacent prior
art and reinforces that the chart-restriction lemma should be treated as
elementary/classical. No exact source was found for the combined block-erasure,
primitive-density, and invariant-measure phase formula; that search miss is not
priority evidence.

### 5.6 Amenable-radical simplification of the binary proof

The binary paper constructs a torsion-free group `K` surjecting onto
`Q=SL_4(F_2[t])` so that the abelian layer of the semidirect product is its
torsion subgroup. It explicitly notes that `Q` has order-four torsion and
therefore cannot replace `K` *in that torsion-subgroup argument*.

The ternary amenable-radical proof suggests a shorter replacement. Margulis's
normal subgroup theorem and the trivial center give `Rad_am(Q)=1`, hence

```text
Rad_am(A semidirect Q)=A
```

for every abelian `Q`-module `A`. All published orbit, detector, carry,
finite-orbit, and common-factor arguments already use only the quotient
`Q`-action. The note `BINARY_AMENABLE_RADICAL_SIMPLIFICATION.md` therefore
reconstructs the full binary family with `Q` acting directly and removes the
integral lift, congruence kernel, torsion-freeness proof, and surjectivity
detour. The published equivariant extension gives ICC directly, and its `1/7`
pointed-space detector gives relative property (T) for each carry group, so
Connes--Jones transfer is optional for the group properties as well. This is a
plausible new proof simplification, subject to expert audit.

### 5.7 Minimal-rank prime-uniform carry synthesis

The cyclicity theorem, the general orbit theorem, and the two-geometry detector
meet on the line

```text
r_p=max(p,3).
```

At `p=2`, fresh coordinates prove binary rank-three cyclicity and orbit growth,
while affine charts give `1/12`. At every odd prime, rank `p` uses the critical
finite difference and symmetric-tail orbit theorem, while primitive boxes give
a positive constant. The length-two Witt polynomial works uniformly, and its
scalar identities pass exhaustive checks at `p=2,3,5,7`. Installing the
published carry/Bockstein/common-factor architecture would give an intrinsic
finite-orbit cardinal `2^(3n)` in the binary rank-three case and `p^(pn)` for
odd `p`. This would be a new realization/synthesis, not a new common-factor
mechanism. See `UNIFORM_PRIME_CARRY_FAMILIES.md`.

## 6. Claims removed by the current-paper comparison

The following should no longer appear under a “new mechanism” heading:

1. changing a compact abelian group law while preserving the measured action;
2. the product-Haar/Fubini proof for triangular carry cocycles;
3. common group factors obtained by Pontryagin Fourier transform;
4. shifted Bocksteins recovered from finite orbits in `E_n[p]/pE_n`;
5. primitive-vector counting plus low-degree polynomial support as the
   property-(T) detector.

The ternary versions can still be mathematically valuable as independent
generalizations, alternate proofs, and formalization targets.

## 7. Required external review

Before a priority claim, seek review from experts in:

1. modular representations and distribution algebras of `SL_r`;
2. global/local Weyl modules and strict polynomial functors;
3. higher-rank lattices over function fields and amenable radicals;
4. deformation/cocycle models of compact abelian groups;
5. deformation-rigidity and group von Neumann algebras.

The correct public label today is **possible new theorem/proof**, not “first” or
“novel theorem.” The overarching status should be phrased as “two public
claimed counterexamples, with a recent unresolved adversarial manuscript,”
rather than as an independently certified final resolution.
