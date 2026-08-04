# Publication workspace

No research manuscript is promoted from this directory yet.

The repository currently supports a formalization note describing the checked
rank-three tensor-orbit theorem, Hopf reconstruction, Frobenius obstruction,
shifted ternary carry identities, and finite certificate suite. A stronger
research paper requires a result beyond that checked companion package.

## Strongest paper candidate

The most defensible possible paper would center on two proposed theorems:

1. divided-`p` cyclicity in stable rank `r > p` and odd critical rank `r = p`;
2. infinite polynomial-tensor orbits for tensor degree `m < r`, together with
   the first-two-symmetric critical case `m = r`.

The rank-three critical orbit theorem is Lean checked. The general orbit and
cyclicity statements have written arguments and selected exact certificates,
but they are not fully formalized or independently reviewed.

## Paper gate

A manuscript should begin only after all of the following hold:

- the focal general theorem has a complete proof, preferably machine checked;
- a modular-representation specialist has reviewed the proof and definitions;
- a targeted literature review supports a precise novelty statement;
- an independent reviewer has reproduced the argument;
- the paper avoids depending on unfinished property-(T), characteristic
  subgroup, or operator-algebra interfaces unless those interfaces are also
  completed.

If those conditions are not met, the appropriate publication is a tutorial or
formalization note with explicit nonclaims.

## Prior-art boundary

OpenAI's binary rank-four carry construction already contains the
carry/common-action, finite-orbit, and primitive-detector architecture.
Shuoxing Zhou's independent binary rank-three construction uses affine charts
and an action shear. Neither architecture is claimed as new here.

The plausible contribution is the stable and critical algebra itself, if its
correctness and priority survive review. The broader minimal-rank prime-uniform
construction remains a research program.
