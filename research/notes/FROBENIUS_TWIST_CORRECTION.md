# Correction: the cubic diagonal needs a Frobenius twist

**Status:** proved scalar obstruction; Lean source added in
`FrobeniusTwistObstruction.lean`.

## The problem

An earlier strategy note used the following statement for an arbitrary field
`F` of characteristic three:

```text
d₃ : B → V is F-linear and d₃(v^⊗3)=v.
```

As written, this is false unless the Frobenius cube is the identity on `F`.
Indeed, for `λ∈F` and nonzero `v`, linearity would give

```text
d₃((λv)^⊗3) = d₃(λ³ v^⊗3) = λ³v,
```

whereas the advertised retraction formula gives `λv`. Hence

```text
(λ³-λ)v=0,
```

so `λ³=λ` for every scalar. A field with that identity has at most three
elements; in characteristic three it is the prime field `F₃`.

## Correct formulations

There are two safe options.

1. State the untwisted retraction only over `F₃`. This is the convention used
   by the ternary carry construction and by the cyclicity proof.
2. Over a general characteristic-three field, send the cubic diagonal to the
   appropriate Frobenius-twisted vector space. The pure-cube assignment is
   Frobenius-semilinear before the twist, not ordinary `F`-linear.

The exact twist convention must be fixed before formalization: dualizing the
standard Frobenius embedding into the symmetric cube can reverse the usual
twist notation. Writing only “the appropriate Frobenius twist” is safer than
silently identifying twists over a non-prime field.

## Consequences for the research program

- The `F₃[t]` construction is unaffected.
- General-field statements in the old cyclicity strategy must be restricted or
  twisted.
- Any naturality theorem over an arbitrary characteristic-three field must
  include the twist in its source/target and scalar action.
- Finite fields `F_{3^m}` with `m>1` do not permit the untwisted formula, even
  though their Frobenius is an automorphism.

This correction is a semantic strengthening: it prevents an apparently
innocent generalization from invalidating the exact sequence used later in the
construction.
