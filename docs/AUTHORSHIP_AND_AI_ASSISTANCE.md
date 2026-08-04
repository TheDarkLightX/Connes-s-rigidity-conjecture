# Authorship and AI assistance

## Research direction and repository stewardship

Dana Edwards specified the research goals, selected the Connes-rigidity problem, directed the adversarial and constructive exploration, supplied the repository infrastructure, and is the repository steward.

## AI-assisted work

OpenAI language models were used to:

- analyze the OpenAI/Codex rigidity construction and proposed rebuttals;
- generate candidate generalizations, including the stable/critical
  divided-power theorems and prime-uniform Witt-carry program;
- propose mathematical proof strategies and theorem decompositions;
- draft and revise Lean source files;
- run GitHub-based compilation experiments and interpret compiler feedback;
- prepare research documentation and migration metadata.

Model output is not itself mathematical verification. A Lean file is treated as verified only when its complete dependency chain builds in the pinned environment, and a formal theorem is treated as relevant only after its definitions are reviewed against the intended mathematical statement.

## Current validation warning

The first complete standalone build in this dedicated repository exposed failures in eleven imported modules. Accordingly, this repository currently presents a research formalization program rather than a blanket set of completed machine-checked results. See `CI_STATUS.md` and `THEOREM_STATUS.md`.

## Publication policy

Any paper or public announcement based on this repository should:

1. distinguish human research direction from AI-generated exploration and drafting;
2. identify the exact tagged commit and toolchain used;
3. disclose the modules and assumptions in the promoted theorem dependency chain;
4. report independent expert review and any unresolved objections;
5. distinguish the published binary counterexample architecture from this
   unreviewed prime-uniform synthesis, acknowledge current adversarial claims,
   and avoid a new-counterexample claim until the property-(T), ICC,
   intrinsic-invariant, and operator-algebra interfaces are formalized and
   independently checked.
