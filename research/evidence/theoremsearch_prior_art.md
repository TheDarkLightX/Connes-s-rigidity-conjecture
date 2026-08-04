# TheoremSearch prior-art assessment

Workflow run: `30897349795`  
Artifact digest: `sha256:1a24da7e481d2ec4bb4cfdd2ea6e9eb7184a0220d12ce90546714b6cc338471e`

TheoremSearch semantic retrieval is evidence for literature triage. A missing close hit is **not** proof of novelty, and a returned hit must be read in context before it is used as prior art.

## Canonical Hopf reconstruction

The search found close classical results. In particular, it returned a lemma from Bartholdi, Siegenthaler and Trimble, *Wreath products of cocommutative Hopf algebras* (2014), stating that group-like elements are linearly independent and that a Hopf algebra is a group algebra exactly when its group-like elements form a basis.

**Assessment:** group-like reconstruction is classical mathematics. The contribution here is its use as an obstruction/interpretation for the Connes-rigidity construction and the associated formalization—not priority over the underlying Hopf result.

## Length-two Witt coordinate

The search returned classical Witt-vector statements, including a theorem phrased as `W_n(F_p) ≅ Z/p^(n+1)` under that source's indexing convention, and results distinguishing the exponent of groups over `W₂(F_q)` from truncated polynomial rings.

**Assessment:** identifying the scalar ternary extension with `Z/9Z` and using Teichmüller representatives is classical. The formula

```text
phi(a,b) = a^3 + 3b mod 9
```

should be presented as a recovered canonical coordinate, not as new Witt-vector mathematics.

## Degree-three ternary support

The top semantic results were not the exact generalized Reed–Muller minimum-distance theorem needed here. This is a retrieval miss, not novelty evidence. The minimum-weight theory of generalized Reed–Muller codes is classical.

**Assessment:** the `2/9` support lower bound is classical as mathematics. A correct Lean proof may still be a new formalization or a useful proof specialization.

## Rank-three polynomial tensor orbit

The top results concerned finite-dimensional tensor-orbit classifications, tensor eigenvalue maps, and secant varieties. None matched the exact statement:

```text
Every nonzero element in the span of pure cubes in (F[t]^3)^(tensor 3)
has an infinite orbit under explicit elementary transvections in SL_3(F[t]).
```

**Assessment:** this remains the strongest novelty candidate in the project, especially the exponent-support replacement for the unavailable fourth coordinate. The search is not exhaustive enough to establish priority. A specialist literature review is still required.

## Public novelty labels

- **Classical ingredient:** Hopf group-like reconstruction.
- **Classical ingredient:** scalar length-two Witt coordinate / `Z/9Z` identification.
- **Classical ingredient:** generalized Reed–Muller support bound.
- **Possible new theorem/proof:** rank-three divided-cube infinite-orbit theorem over a polynomial ring.
- **Possible new synthesis:** combining the rank-three orbit theorem with shifted ternary carries toward the operator-algebra construction.
