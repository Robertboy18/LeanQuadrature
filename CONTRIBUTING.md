# Working on LeanQuadrature

Use the pinned toolchain and dependencies. The project follows mathlib's
conventions for mathematical declarations, proof layout, and documentation.
The CLean adaptation preserves upstream names where exported syntax and
semantic statements depend on them.

## Build and audit

Keep Lean builds on dedicated local storage. `scripts/run-local.sh` synchronizes
the repository there and removes obsolete files from that mirror. Do not point
`QUADRATURE_BUILD_ROOT` at an unrelated directory.

During an edit, check the affected module:

```sh
scripts/run-local.sh lake build Quadrature.Examples.TwoPointCosine
```

After completing a change, run the full build and assumption checks:

```sh
python3 scripts/check-lean.py
```

Set `QUADRATURE_BUILD_ROOT` to change the local mirror. The checker records
commands, logs, source hashes, clean dependency revisions, and theorem counts
in `evidence/lean-quality.json`. The checker fails if an audited theorem depends on an
axiom outside `propext`, `Classical.choice`, and `Quot.sound`, or if checked
inputs change during the run. Counts include generated declarations; they
measure the audit's scope, not the completeness of the application.
Selection uses the defining module, so it also covers project declarations
added to an imported namespace and private helper theorems.
The checker compares Lean's imported module inventory with the project sources
and fails if a source module is missing from the audit. Import new modules
through `Quadrature.lean` or one of its dependencies.
The corresponding text logs are retained under `evidence/lean-quality-logs/`
and included in the source archive.

When changing the audit driver, also run its regression checks:

```sh
python3 -m unittest discover -s scripts/tests -v
```

## Mathematical code

- Search the imported mathlib API before adding a helper. Keep reusable
  mathematics separate from stored constants and execution certificates.
- State regularity, interval, finiteness, and callback assumptions explicitly.
  Preserve their mathematical meaning when simplifying a statement.
- Give public definitions and main theorems useful docstrings. Module
  docstrings should explain their central objects and results.
- Prefer direct proofs, named facts, and small stable simplification sets.
  Factor repeated mathematical arguments into helpers.
- Keep resource-limit changes local to the declaration that needs them.
  Do not admit proofs, introduce project axioms, or leave diagnostic tactics
  such as `simp?` in completed code.
- Treat warnings as errors. Do not suppress a linter simply to make a proof
  compile. The one documented duplicate-namespace exception preserves
  CLean's upstream `State.State` constructor.

## Generated syntax and imported semantics

Shared execution arguments live in `Quadrature/Compiler/Execution/`:
`ExternalCalls.lean` defines soundness and agreement at the symbol-environment
level. `Run.lean` defines the common runner and proves soundness, prefix completion,
and exclusion of infinite executions. Numeric annotation facts live together in
`Quadrature/Compiler/Cminor/Annotations.lean`. Each language defines its own transition
rules and one-step executor; `executeSteps` uses the common `run` directly. Reuse these
lemmas when extending an executor.

Files containing compiler exports or large stored certificates have different
layout needs from handwritten proofs. Keep them attributable and reproducible:
edit the responsible generator when changing generated content, and retain
the input hashes and command in the corresponding evidence record. A successful
import is not a proof that the importer preserves semantics.

Do not rename imported constructors for appearance alone. Keep FloatLib
arithmetic choices and external-call contracts visible in the adapted
semantics, and document changes in `vendor/clean/README.md`.

## Claims and documentation

Update the coverage ledger and manuscript claim map when a theorem's scope
changes. Distinguish exact-real inequalities, rounded functional computations,
C executions under contracts, and particular assembly certificates. A proof
in one kernel is not automatically a theorem in the other.

Keep one current record per verification workflow. Rerun the checker to replace
its record and logs; never edit recorded input hashes to imply a check was run.
Remove superseded records, unused audit scripts, and their documentation links.
Keep the source revisions and distinct compiler or execution checks needed to
reproduce the current results.

Rebuild the PDF with `scripts/build-paper.py` after manuscript changes and use
`scripts/package-artifact.py` to prepare an attachable snapshot.
