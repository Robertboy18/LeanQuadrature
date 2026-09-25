# LeanQuadrature

Gaussian quadrature in Lean: finite-interval mathematics, binary64 error bounds,
and program proofs with explicit execution assumptions.

This development studies Andrew W. Appel and David S. Bindel's
*Formalization of Gaussian Quadrature and Application Verification
(Preliminary Draft)* and its accompanying source code. It proves corrected
results, extends the finite-interval mathematics, and investigates how
numerical theorems connect to C and assembly semantics.

**Read the paper, [Gaussian Quadrature in Lean and Rocq](paper/main.pdf),
its [source and claim map](paper/README.md),
or the [interactive explanation](docs/interactive/index.html).**
The [documentation index](docs/README.md) covers the results and reproduction instructions.
The [24-paragraph comparison](docs/stewart-comparison.md) identifies what
the original LeanPDE baseline supplied and what this project developed.
The general Gaussian theory, explicit Legendre rules, and reusable root and
weight certificate proofs now live in LeanPDE's `PDE.Symbolic.Continuum`
namespace. This project imports them, together with LeanPDE's Taylor bounds,
to verify the stored tables and programs.

## What is proved

| Layer | Current result | Scope that matters |
| --- | --- | --- |
| Mathematical specification and method | Weighted Gaussian rules on compact intervals: construction, roots, exactness, positive weights, recurrence, remainder, and convergence. | Positive continuous weights; the general existence theorem covers all positive orders. |
| Floating-point model | FloatLib binary64 computation, range and error theorems, and certificates for all ten stored rules. | Callback accuracy and range hypotheses remain explicit in the general theorem. Concrete callbacks have separate certificates. |
| C library with an internal cosine | The five original functions, a verified C polynomial replacing `cos`, and initialized calls with error bounds for all ten stored orders. Behavioral preservation to the actual Clight frontend output is proved for all six functions. | Every permitted evaluation order terminates with the certified result in the adapted C semantics. General parser/elaborator correctness and Lean/Rocq correspondence remain open. The original external-cosine variant retains its contract. |
| Polynomial application | Initialized Lean Clight applications and direct proofs through imported assembly for orders 1–10. Their result annotations carry exactly the values returned by the C library. | Uses the same degree-14 polynomial and authored entry points. The proved return-to-annotation agreement does not establish that compiling the original C text produces these assembly trees. |
| CompCert | Independent Rocq numerical and compilation certificates for all ten polynomial applications. | Uses a separately checked explicit compiler configuration. A general Lean–Rocq semantic connection is not proved. The endpoint is formal assembly, not a linked native executable. |

The paper asks how far Appel and Bindel's quadrature development can be
reconstructed in Lean, answers level by level, and records four specific
discrepancies in the examined paper and source, with page and source references:
two false example bounds, an inconsistent remainder index, and a three-point
C/model weight mismatch. The original work is explicitly preliminary:
admitted lemmas and unfinished program assembly are acknowledged work in
progress. A missing proof is distinguished from a statement refuted by a
counterexample. Green checkmarks identify proved results, amber marks
partial or conditional applications, blue-gray circles mark open connections,
and red crosses mark refuted claims. The [review record](evidence/upstream-review.json)
identifies the paper version and source revision examined.
The [code review](docs/review.md) adds counterexamples to admitted overflow
and integral-positivity helpers, identifies a wrong function identifier in the Hughes specification,
and separates the missing callback proof from the completed body proofs.
It also records the original VST rebuild with two type annotations,
the remaining admitted dependencies, and regression checks on
the original C implementation. The review explains the public work on
`g_max_deriv` and the missing Verified Software Unit (VSU), which would
connect the function contracts and check global initialization.
The [review evidence](evidence/upstream-review.json)
links the checks and their retained logs.

The full Lean build and assumption audits are recorded in
[`evidence/lean-quality.json`](evidence/lean-quality.json).
Every project module, including the root, is covered by the audit.
The checker compares the source inventory with Lean's imported modules and
rejects omitted files. The shipped [C cosine](Quadrature/CSource/Cosine/cosine.c)
is a build dependency and is checked against the text used by its proof.
The [initialized wrapper theorem](Quadrature/CSource/Library/Total.lean)
returns bits `0x3fead02c771c35ed` with integral error at most `0.00356`,
without a cosine or table-initialization assumption. Its total-correctness
proof covers all permitted operand orders, excludes infinite executions,
and proves that every reachable state either returns the specified value
or can take another step. The [source-to-Clight theorem](Quadrature/CSource/Library/Preservation.lean)
connects both frontend outputs, including initialization and function lookup.
For all six functions it proves the same returned bits and traces, termination,
and agreement of final memory on loads and permissions that existed before the call.
The integrator uses orders 0–10 and the initialized polynomial callback;
the accessors cover all stored cells, and the callback and cosine accept any binary64 input.
This is a proof for these library calls in the Lean semantics.
The audits
include private helpers and project declarations added to imported namespaces,
allowing only `propext`, `Classical.choice`, and `Quot.sound`.
The record retains logs, input hashes, and clean dependency revisions.
Its theorem counts include generated declarations and describe the audit's
scope, not how much of the complete C-to-native-executable chain is verified.

## Build and inspect

**The full build requires access to the private LeanPDE repository.**
Contact Robert to arrange access before fetching dependencies. The public
source archive includes this project and its paper, but does not include
LeanPDE.

Install Lean through Elan and the usual Lake dependencies. The toolchain and
dependency revisions are pinned in `lean-toolchain` and `lake-manifest.json`.
Build on **dedicated local storage**; the helper synchronizes the repository into
that directory with deletion of obsolete files:

```sh
QUADRATURE_BUILD_ROOT=/tmp/leanquadrature-build scripts/run-local.sh lake build
QUADRATURE_BUILD_ROOT=/tmp/leanquadrature-build scripts/run-local.sh \
  lake env lean -DwarningAsError=true scripts/Audit.lean
```

Run all build and assumption checks, including the vendored semantics:

```sh
QUADRATURE_BUILD_ROOT=/tmp/leanquadrature-build python3 scripts/check-lean.py
```

The checker retains logs and hashes, checks dependency revisions, and refuses
to record success if its inputs change during checking or a project source
module is missing from the audit.
[Contributing instructions](CONTRIBUTING.md) document the code conventions.

Build the paper with Python 3, `pdflatex`, and `bibtex`:

```sh
python3 scripts/build-paper.py
```

Prepare an attachable source snapshot, including current uncommitted project
files, the paper, and a SHA-256 manifest:

```sh
python3 scripts/package-artifact.py --output dist/LeanQuadrature-paper.tar.gz
```

The archive excludes Git metadata, dependency/build caches, and previous
archives. It is a source distribution; dependencies must still be fetched.
Detailed Rocq reproduction requirements are in
[`compcert/certification/README.md`](compcert/certification/README.md).
The [upstream VST instructions](scripts/upstream/README.md) describe the separate
environment for rebuilding the authors' original quadrature development.

## Repository map

The Lean library is organized by subject. [`Quadrature/README.md`](Quadrature/README.md)
gives a reading order and the main theorem in each part.

```text
Quadrature/
├── Binary64/     Floating-point operations, roundoff, and functional loops
├── Rules/        Stored tables, root brackets, and accuracy certificates
├── Examples/     Cosine applications and counterexamples
├── CSource/      Frontend, semantics, and proofs grouped by C function
├── Clight/       Library execution and initialized applications
└── Compiler/     Cminor through assembly, with shared execution and correspondence proofs
```

| Path | Contents |
| --- | --- |
| [`Quadrature/`](Quadrature/) | Lean mathematics, floating-point results, and execution proofs |
| [`compcert/`](compcert/) | Independent Rocq proofs, compiler exports, and compilation certificates |
| [`vendor/clean/`](vendor/clean/README.md) | Attributed CLean adaptation and upstream license |
| [`paper/`](paper/README.md) | Manuscript, bibliography, evidence map, and PDF |
| [`docs/`](docs/README.md) | Explanations, coverage, and remaining work |
| [`evidence/`](evidence/README.md) | Build, audit, import, and execution checks |
| [`scripts/`](scripts/) | Generation, reproduction, audit, paper, and packaging tools |

Before making a completeness claim, consult the
[coverage ledger](docs/coverage.md).

Project license: [Apache 2.0](LICENSE). Vendored components retain their own notices
and licenses.
