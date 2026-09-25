# Reading the Lean library

The folders follow the subjects of the proof: real quadrature, rounded
computation, C execution, and compiled programs. Import
[`Quadrature`](../Quadrature.lean) to load the whole development, or import an
individual module such as `Quadrature.Binary64.Program`.

The general Gaussian theory was developed here and moved into LeanPDE. We import
its [Gaussian rules](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Weighted.lean) and
[remainder theorem](https://github.com/lean-dojo/LeanPDE/blob/main/PDE/Symbolic/Continuum/Quadrature/Gaussian/Remainder.lean) directly; the local
`Legendre`, `Rules`, and execution proofs apply that shared theory.

| Folder | What it contains | Start here |
| --- | --- | --- |
| [Analysis](Analysis/) | Taylor estimates for the trigonometric examples | [Taylor bounds](Analysis/Taylor.lean) |
| [Legendre](Legendre/) | The explicit one- through four-point rules and certified root and weight enclosures for the larger orders | [Explicit rules](Legendre/Basic.lean), [root certificates](Legendre/RootCertificates.lean) |
| [Binary64](Binary64/) | FloatLib constants and operations, reduction errors, finite representations, and the functional quadrature loop | [Program](Binary64/Program.lean), [functional accuracy](Binary64/FunctionalAccuracy.lean) |
| [Rules](Rules/) | Stored rules, decoded tables, node and weight certificates, and accuracy for a general integrand | [Stored rules](Rules/Basic.lean), [table certificates](Rules/Certificates.lean), [accuracy](Rules/Accuracy.lean) |
| [Examples](Examples/) | The cosine example, its rounded evaluation, polynomial applications, and counterexamples | [Exact cosine bounds](Examples/TwoPointCosine.lean), [binary64 cosine evaluation](Examples/CosineEvaluation.lean) |
| [CSource](CSource/) | The five original functions, the C polynomial replacing cosine, and their behavior before and after Clight normalization | [Source-to-Clight preservation](CSource/Library/Preservation.lean), [total correctness and accuracy](CSource/Library/Total.lean), [cosine execution](CSource/Cosine/Total.lean) |
| [Clight](Clight/) | Execution of library functions and initialized polynomial applications | [Library calls](Clight/Library.lean), [initialized application](Clight/Main.lean), [general-integrand accuracy](Clight/RuleAccuracy.lean) |
| [Compiler](Compiler/) | Direct execution proofs for the particular compiled programs from Cminor through formal assembly | [Shared execution lemmas](Compiler/Execution/Run.lean), [assembly accuracy](Compiler/Asm/StoredTotalCorrectness.lean) |

## C source

`CSource/Frontend/` contains the source bytes, lexer, parser, translations,
and syntax checks. `Refinement.lean` and `InitializedRefinement.lean` define
behavioral preservation for library calls and derive equality of return observations,
termination, progress, and agreement on pre-call memory.
`CSource/Semantics/` defines typed expressions, statements,
memory effects, and both strategy and unrestricted small-step execution.
`TotalCorrectness.lean` defines the judgment used to prove termination,
progress, and the returned value for every permitted evaluation order.
`CSource/Tables/` checks the
decimal table literals.

The function proofs have their own folders:

- `Accessors/`: parameter entry, table reads, return, and complete calls.
- `Integrator/`: local state, nested calls, loop steps, entry, and return.
- `Callback/`: the original `testfun` function under its cosine contract.
- `Wrapper/`: the original two-point wrapper and its integral-error bound.
- `Cosine/`: the shipped C replacement, its parsed syntax, and its complete execution.
- `Library/`: the selected source library, global initialization, total correctness,
  numerical accuracy, and preservation to the actual Clight frontend output.
  `Preservation.lean` states the covered calls and the theorem starting from both source files.

## Compiler stages

`Compiler/` contains `Cminor/`, `CminorSel/`, `RTL/`, `LTL/`, `Linear/`,
`Mach/`, and `Asm/`. Within each stage, `Semantics.lean` defines execution,
`Execution.lean` implements and justifies the finite executor,
`Imported.lean` holds the generated program syntax, and
`ProgramExecution.lean` connects initialization, finite execution, and the
exit status. `StoredPrograms.lean` checks the ten applications;
`StoredTotalCorrectness.lean` proves termination, unique results, and
integral-error bounds for their executions.

`Compiler/Execution/` supplies common run and external-call lemmas.
`Compiler/Correspondence/` relates the particular programs and their
components across stages.
[CSourcePrograms.lean](Compiler/Correspondence/CSourcePrograms.lean) connects the
initialized C library to the authored Clight applications and imported assembly:
the application reports the same binary64 value that C returns, then exits zero.
It covers all ten stored orders and specializes to the original two-node wrapper.
This is a result correspondence between the verified programs; it does not establish
that compiling the original C source produces the imported assembly syntax. The
[coverage ledger](../docs/coverage.md) states the assumptions and remaining connections.

Generated data stays beside the proofs that use it. Its header names the
responsible script under [`scripts/`](../scripts/). Change that script when
changing generated content. Declaration namespaces are independent of the
folder layout; theorem names remain stable when a module moves.
