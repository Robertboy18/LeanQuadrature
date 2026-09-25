import PDE.Symbolic.Continuum.Quadrature.Gaussian.Characterization
import PDE.Symbolic.Continuum.Quadrature.Gaussian.Recurrence
import PDE.Symbolic.Continuum.Quadrature.Gaussian.Weighted
import PDE.Symbolic.Continuum.Quadrature.PositiveRule
import Quadrature.Binary64.BoundedRoundoff
import Quadrature.Binary64.Constants
import Quadrature.Binary64.ExceptionalValues
import Quadrature.Binary64.FiniteExecution
import Quadrature.Binary64.FiniteInteger
import Quadrature.Binary64.FiniteRepresentation
import Quadrature.Binary64.FunctionalAccuracy
import Quadrature.Binary64.IntegerRounding
import Quadrature.Binary64.Program
import Quadrature.Binary64.Roundoff
import Quadrature.CSource.Accessors.Calls
import Quadrature.CSource.Accessors.Entry
import Quadrature.CSource.Accessors.TableExpressions
import Quadrature.CSource.Frontend.ClightFunctions
import Quadrature.CSource.Frontend.ElaborationChecks
import Quadrature.CSource.Frontend.ParserChecks
import Quadrature.CSource.Integrator.Function
import Quadrature.CSource.Library.Accuracy
import Quadrature.CSource.Library.Preservation
import Quadrature.CSource.Library.Total
import Quadrature.CSource.Tables.Accuracy
import Quadrature.CSource.Wrapper.Accuracy
import Quadrature.Clight.Applications
import Quadrature.Clight.Arithmetic
import Quadrature.Clight.Callbacks
import Quadrature.Clight.Library
import Quadrature.Clight.Main
import Quadrature.Clight.RuleAccuracy
import Quadrature.Clight.StoredAccuracy
import Quadrature.Clight.StoredRules
import Quadrature.Compiler.Asm.CallSites
import Quadrature.Compiler.Cminor.StoredTotalCorrectness
import Quadrature.Compiler.Cminor.Validation
import Quadrature.Compiler.Correspondence.AsmPrograms
import Quadrature.Compiler.Correspondence.CSourcePrograms
import Quadrature.Compiler.Correspondence.CallbackFunction
import Quadrature.Compiler.Correspondence.CallerFunctions
import Quadrature.Compiler.Correspondence.GlobalFunctions
import Quadrature.Compiler.Correspondence.GlobalMemory
import Quadrature.Compiler.Correspondence.IntegratorFunction
import Quadrature.Compiler.Correspondence.LTLPrograms
import Quadrature.Compiler.Correspondence.LinearPrograms
import Quadrature.Compiler.Correspondence.MachPrograms
import Quadrature.Compiler.Correspondence.PolynomialFunction
import Quadrature.Compiler.Correspondence.PreallocationPrograms
import Quadrature.Compiler.Correspondence.RTLPrograms
import Quadrature.Compiler.Correspondence.SelectedExpressions
import Quadrature.Compiler.Correspondence.SelectedPrograms
import Quadrature.Compiler.Correspondence.TableAccessors
import Quadrature.Compiler.Execution.ExternalCalls
import Quadrature.Compiler.Execution.IntegerArithmetic
import Quadrature.Compiler.Execution.Run
import Quadrature.Compiler.Mach.Imported
import Quadrature.Compiler.Mach.ProgramExecution
import Quadrature.Compiler.Mach.StoredPrograms
import Quadrature.Examples.CosineAccuracy
import Quadrature.Examples.CosineCallback
import Quadrature.Examples.CosineEvaluation
import Quadrature.Examples.IntegralPositivity
import Quadrature.Examples.LoopApplications
import Quadrature.Examples.Overflow
import Quadrature.Examples.PolynomialRules
import Quadrature.Examples.TwoPointCosine
import Quadrature.Legendre.Basic
import Quadrature.Legendre.Identification
import Quadrature.Rules.Accuracy
import Quadrature.Rules.Basic
import Quadrature.Rules.Constants

/-!
# LeanQuadrature: Gaussian quadrature from the real line to compiled code

This project redoes in Lean 4 and mathlib the verification that Appel and Bindel carried out
in Rocq for a small C library of Gaussian quadrature rules. The original C program is
`quadrules.c` from their `simple_cfem` repository, their paper is the Appel–Bindel
manuscript (Formalization of Gaussian Quadrature and Application Verification, Preliminary
Draft), and their proofs are the Rocq development. The Lean development covers exactness and
error theory on compact intervals, the original C functions with an internal polynomial cosine,
and ten polynomial applications through formal assembly. It also records where the manuscript's
numbers or lemmas needed repair.

## Main results

Shared exact quadrature on compact intervals. We developed the general Gaussian theory here
and moved it into LeanPDE so other applications can reuse it. This project imports those
proofs directly. For a continuous positive weight `w` on `[a, b]` the
monic orthogonal polynomials exist by projection, their roots are simple and interior, and
the Christoffel numbers are positive. `GaussianRule.remainder` gives the error formula
`∫ f w - Q f = f^(2n)(ξ) / (2n)! * ∫ p_n ^ 2 w` for `f ∈ C^{2n}[a, b]`, and
`gaussian_rules_converge` shows the rules converge for every continuous integrand.

Explicit Legendre rules and the ten stored tables. Orders one to four are written in
radicals, and orders five to ten are certified from rational root brackets checked by kernel
evaluation. `Binary64.StoredRule.table_certificate` (in `Rules/Certificates`) shows that
each of the ten node and weight tables of the C program lies within `6e-16` and `5e-16` of
the ideal rule. `Example.corrected_two_point_bound` proves the error bound `0.00356` for the
manuscript's cosine example, whose stated bound `0.00223` is refuted alongside it.

Binary64 error bounds. FloatLib models the rounding of each product and sum in the
integrator. `StoredRule.Certificate.accuracy` (in `Rules/Accuracy`) shows the floating-point
result is finite and bounds its distance from the exact integral by roundoff terms, the node
and weight tolerances, and the Gaussian remainder.

C programs and application results. `CSource.Typed.integrate_testfun_external_accuracy`
proves the `0.00356` bound for the parsed C source of the wrapper calling an external
cosine under its contract. `CSource.Library.parsed_wrapper_total_accuracy` discharges that contract
by a verified C polynomial and includes parsing, global initialization and the complete
wrapper call in every permitted C evaluation order. `CSource.Library.integral_total_accuracy`
covers all ten stored orders, including termination, absence of stuck executions, and caller
memory preservation. `CSource.Library.parsed_refinement` connects the actual C and Clight
frontend outputs for all six functions. Their calls have the same returned bits and traces;
both terminate, and their final memories agree on pre-call loads and permissions.
Authored Clight applications use the same tables and degree-14 polynomial.
`Clight.StoredPolynomial.integral_accuracy` proves their bounds for all ten orders, and
`Asm.StoredPrograms.final_accuracy` proves that every execution of the corresponding
CompCert assembly returns zero and emits a binary64 value with the same bound. Each
intermediate stage has the same result.
`Compiler.csource_integrate_asm_observations_iff` connects the initialized C library to
these assembly applications: C returns the value silently; the application reports that
same value in an annotation and exits zero. `Compiler.parsed_wrapper_asm_accuracy` starts
from the source text of the original two-node wrapper and includes its `0.00356` bound.
These result correspondences do not assert that compiling the original source produces
the imported application syntax.

## Directory layout

The files are grouped by subject under `Quadrature/`:

* `Analysis/`: Taylor estimates for the trigonometric examples. The general Gaussian theory
  lives in LeanPDE under `PDE/Symbolic/Continuum/Quadrature/Gaussian/`.
* `Legendre/`: explicit rules and rational root and weight certificates.
* `Binary64/`: FloatLib operations, rounding, finite representations, and loop models.
* `Rules/`: stored tables, their certificates, and general accuracy bounds.
* `Examples/`: the cosine applications and counterexamples to claims in the original work.
* `CSource/`: the frontend, C semantics, original functions, and internal cosine library.
* `Clight/`: library calls and initialized polynomial applications.
* `Compiler/`: the seven intermediate languages, shared execution lemmas, and proofs
  relating the particular programs at adjacent stages.

`Quadrature/README.md` gives entry points for each subject. Every source module is imported
here, directly or through a dependency, so the assumption audit checks the entire library.

## Scope

The C parser is a restricted one, checked against `clightgen`'s output for the five
original functions. The internal C polynomial is checked by parsing its shipped source.
C calls are proved in the adaptation of CompCert's full C small-step rules using FloatLib.
Behavioral preservation is proved between the typed C and normalized Clight outputs for the
selected calls. General correctness of the parser and elaborator, including preprocessing and
static-array hoisting from an independent source semantics, remains open. The Clight semantics
is adapted from CLean and is not related by proof to CompCert's Rocq semantics.
No compiler correctness theorem is proved in Lean: the
ten compiled programs are proved directly at each stage. The platform `cos` is not verified;
the polynomial library supplies its own C routine. FloatLib and
Flocq arithmetic are not related by proof.
-/
