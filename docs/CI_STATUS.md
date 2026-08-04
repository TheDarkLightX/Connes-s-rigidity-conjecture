# CI and trust status

## Pinned formal environment

- Lean: `4.30.0-rc2`
- Mathlib: `9977002c3c9492b622fb469b0d18acc7e73aed3e`
- Formal entry point: `LeanMathlib.lean`
- Imported rigidity modules: 51

## Release gate

The release candidate passes a clean GitHub-hosted `lake build` of the full
import graph. The pull-request gate runs on every proposed change, including
documentation-only changes, so the status belongs to the exact head being
reviewed.

Before Lean runs, `scripts/audit_lean_trust.py` rejects project-source uses of:

- `sorry` and `admit`;
- declared `axiom` statements;
- `unsafe` declarations;
- `native_decide`;
- direct `sorryAx` references.

The same audit runs again on pushes to `main`.

## Why the full graph matters

The first standalone import exposed eleven failures that were hidden by
incremental source-workspace checks. Successive repairs reduced that frontier
to zero. The failed runs remain in GitHub Actions as an audit trail, but they no
longer describe the release head.

An isolated file build is useful during repair, but it is not the publication
gate. The accepted unit is the complete pinned dependency graph at the exact
commit being published.

## Independent finite-oracle gate

The Julia and Python workflow runs eleven bounded certificate suites and
uploads their machine-readable results. The suite covers Witt carries, divided
power kernels, multivariate cases, detector constants, chart restrictions, and
selected prime/rank boundary cases.

This gate is logically separate from Lean:

- Lean checks general statements represented in the formal source;
- the finite programs check only their enumerated domains;
- agreement between them is useful cross-validation where their scopes
  overlap, but neither evidence class inherits claims from the other.

## Reproduction

```bash
python3 scripts/audit_lean_trust.py
lake build
```

The finite commands and their bounds are listed in
`.github/workflows/julia-experiments.yml`.
