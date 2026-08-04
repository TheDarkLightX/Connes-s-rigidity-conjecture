# Multivariate ternary divided-cube cyclicity

**Mathematical status:** complete proof candidate over every finite polynomial
ring `F₃[t₁,…,t_d]`.

**Machine status:** exact orbit closure and proof-ledger replay pass for the
bivariate total-degree quotient through degree `3` (`444/444`) and the
trivariate quotient through degree `2` (`304/304`). The infinite statement is
not yet formalized in Lean.

**Novelty status:** unknown. This should be compared with modular
divided-power and current-group representation theory before any priority
claim.

## 1. Statement

Let

```text
k = F₃,  R_d = k[t₁,…,t_d],  V_d = R_d³,
B_d = span_k {v⊗v⊗v : v∈V_d}.
```

The cubic diagonal gives an `E₃(R_d)`-equivariant exact sequence

```text
0 → K_d → B_d --d₃→ V_d → 0,
d₃(v⊗³)=v.
```

With

```text
w = Σ_{σ∈S₃} e_{σ(1)}⊗e_{σ(2)}⊗e_{σ(3)},
q = e₁⊗e₁⊗e₁,
```

the theorem candidate is

```text
K_d = span_k(E₃(R_d)·w),
B_d = span_k(E₃(R_d)·q).
```

For `d=1` this is the cyclicity theorem used by the Connes construction. The
multivariate statement is stronger algebraically; no multivariate
infinite-orbit theorem is asserted here.

## 2. Basis and exact sequence

Use the monomial basis `t^α e_i`, where `α∈N^d`. As in the one-variable
proof, the distinct-permutation sums

```text
[x,y,z]
```

indexed by multisets of three basis vectors form a basis of `B_d`. Two-equal
terms are isolated from `P(x+y)` and `P(x-y)`, and all-distinct terms by
inclusion-exclusion. The map `d₃` sends `[x,x,x]` to `x` and every
non-diagonal multiset to zero. Since scalar cubes are fixed in `F₃`, this is
exact and equivariant.

Put `W=span_k(E₃(R_d)·w)`. It remains to show that every non-diagonal basis
tensor lies in `W`.

## 3. Simultaneous induction

Induct on total monomial degree. At degree `D`, handle repeated coordinate
labels first and all-distinct labels second.

### 3.1 Repeated-label step

At degree zero, `w∈W` and

```text
u_ij(1)w-w = 2[e_i,e_i,e_k]
```

generates the other six constant kernel basis vectors.

For `D>0`, let `T` have repeated coordinate labels and choose a positive-degree
entry `t^αe_i`. Choose a variable `t_r` dividing `t^α`, and choose a
coordinate label `h≠i` absent from the other two entries. Replace the chosen
entry by `t^(α-ε_r)e_h`, obtaining a non-diagonal tensor `S` of degree
`D-1`. The label `h` occurs once, so

```text
u_ih(t_r)S-S = cT,   c∈{1,2}.
```

The coefficient is `2` precisely when two ordered outputs collapse onto each
term of a two-equal orbit sum. The diagonal collision, which would have
coefficient `3=0`, cannot occur because `T∈K_d`. Thus `c` is invertible and
the outer induction puts `T` in `W`.

### 3.2 Equal-source finite difference

Fix distinct coordinate labels `i,j,k`. For monomials `r,z`, set

```text
S₀ = [e_j,e_j,z e_k].
```

Direct expansion gives

```text
u_ij(f)S₀
 = S₀ + [f e_i,e_j,z e_k] + [f e_i,f e_i,z e_k].
```

Therefore, in characteristic three,

```text
u_ij(2r)S₀-u_ij(r)S₀ = [r e_i,e_j,z e_k].       (E)
```

The linear term survives with coefficient `2-1=1`; the quadratic term cancels
because `2²=1`.

### 3.3 Two-step all-distinct certificate

Write

```text
A(x,y,z)=[x e_i,y e_j,z e_k].
```

If `y=1`, identity `(E)` puts `A(x,1,z)` in `W`.

If `y≠1`, the two repeated entries in

```text
S_y=[e_j,y e_j,z e_k]
```

are distinct monomial basis vectors. Expanding at `x` and `2x` gives

```text
u_ij(2x)S_y-u_ij(x)S_y
  = A(x,y,z)+A(xy,1,z).                    (D)
```

The auxiliary term `A(xy,1,z)` lies in `W` by `(E)`, so `(D)` puts
`A(x,y,z)` in `W`.

The degree bookkeeping makes the induction well-founded. The source `S_y`
has degree `deg(y)+deg(z)≤D`; it is either covered by the outer induction or
by the repeated-label half at degree `D`. The source in `(E)` has degree
`deg(z)≤D`. The degree-zero all-distinct tensor is the generator `w` itself.

This proves `K_d=W`.

## 4. Cyclicity of the whole divided cube

Inclusion-exclusion among the seven nonzero subset sums of `e₁,e₂,e₃`
puts `w` in the orbit span of `q`. The image of that span under `d₃` contains
all monomial coordinate vectors because

```text
u_ij(t^α)e_j-e_j=t^αe_i.
```

It therefore surjects onto `V_d`; subtracting a lift leaves an element of
`K_d`, already in the span. Hence `B_d` is cyclic from `q`.

## 5. Exact finite evidence

The oracle `experiments/divided_cube_multivariate_orbit.py` independently
closes the orbit and replays every local identity.

```text
R = F₃[t₁,t₂], degree ≤ 3:
  dim B = 453, dim K = 444, dim span(E·w) = 444.
  ledger = 1 seed + 6 constant + 354 repeated
           + 34 equal-source + 49 two-step = 444.

R = F₃[t₁,t₂,t₃], degree ≤ 2:
  dim B = 307, dim K = 304, dim span(E·w) = 304.
  ledger = 1 seed + 6 constant + 243 repeated
           + 27 equal-source + 27 two-step = 304.
```

These are exact finite quotient calculations, not a substitute for the
infinite proof or Lean formalization.

## 6. Further portal

The proof only uses a graded cancellative monomial basis in which every
positive-degree monomial can be lowered by an elementary generator, plus the
fact that multiplying by a nonunit monomial does not identify two basis
monomials. This suggests a broader monoid-algebra theorem for suitably graded,
cancellative, conical monoids. That extension has not been checked and should
remain a conjectural portal.
