# Morph tactic search for Connes-rigidity Lean repair

Source workflow: `TheDarkLightX/Morph`, run `30896588897`
Artifact digest: `sha256:40d89dad98a646ddabc7d68af84bc0c0395455103021179b5f88d30b213569c0`

## Search outcome

The free-text tactic queries did not return direct database matches for:

- phantom structure parameters and field notation;
- recursive representation typeclass instances;
- finite case splits and extensionality;
- support separation and infinite orbits;
- brittle rewrite replacement;
- dependency-ordered compiler repair.

The invariant-tagged search returned two applicable Morph tactics:

### `tao_abstract_to_numerics`

**Move:** Replace complicated objects with coarse numerical invariants—norms, ranks, measures, support degrees or cardinalities—when those invariants control the target.

**Use in this project:**

- replace full tensor comparison by maximal support degree and exponent difference;
- replace the scalar ternary carry pair by a numerical coordinate in `Z/9Z`;
- replace orbit equality by injectivity of a moving degree label.

### `geom_invariant_coordinate_projection`

**Move:** Project to invariant coordinates when objectives and checkers depend on a small number of conserved or monotone quantities.

**Use in this project:**

- project `(a,b)` to the candidate Teichmüller coordinate `a^3 + 3b mod 9`;
- project tensor blocks to signed exponent difference and total degree;
- project the proposed group invariant to the finite low-degree coefficient kernel.

## Research consequence

The tactic search did not itself prove anything. It did identify the representation change that produced the strongest current finite result:

```text
naive coordinate:        a + 3b        mod 9   — refuted
invariant coordinate:    a^3 + 3b      mod 9   — finite-verified
```

Every use of a Morph tactic remains subject to the original-domain verifier and Lean compilation.
