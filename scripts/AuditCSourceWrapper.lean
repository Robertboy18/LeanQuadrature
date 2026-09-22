import Quadrature.CSource.Wrapper.Accuracy
import Quadrature.CSource.Frontend.ElaborationChecks
import Quadrature.CSource.Library.Accuracy
import Quadrature.CSource.Library.Preservation
import Quadrature.CSource.Library.Total
import Lean.Util.CollectAxioms

/-!
# Assumption audit of the original C functions and the internal cosine

Audit the generic wrapper and the initialized polynomial library. Every `required` name must exist,
and every declaration under `Quadrature.CSource.`, private ones included, must depend only on
`propext`, `Classical.choice`, and `Quot.sound`, with no axiom declarations. A missing required
name, an unapproved axiom, or an axiom declaration fails the run.

`check-lean.py` drives this file together with `Audit.lean` and `AuditClight.lean`.
-/

-- Read the shipped C again, independently of the cached module containing include_str.
example : Quadrature.CSource.Cosine.source =
    (include_str "../Quadrature/CSource/Cosine/cosine.c").toList := by
  decide +kernel

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let required := #[
    ``Quadrature.CSource.C.testfun_entry,
    ``Quadrature.CSource.C.testfun_free,
    ``Quadrature.CSource.C.testfun_subtraction,
    ``Quadrature.CSource.C.testfun_expression,
    ``Quadrature.CSource.C.SourceCallbackContract.of_external,
    ``Quadrature.CSource.C.testfun_call,
    ``Quadrature.CSource.C.testfun_callback_contract,
    ``Quadrature.CSource.C.wrapper_expression,
    ``Quadrature.CSource.C.wrapper_call,
    ``Quadrature.CSource.Typed.testfun_call,
    ``Quadrature.CSource.Typed.integrate_testfun_call,
    ``Quadrature.CSource.Typed.integrate_testfun_accuracy,
    ``Quadrature.CSource.Typed.integrate_testfun_external_accuracy,
    ``Quadrature.CSource.Cosine.elaboration,
    ``Quadrature.CSource.Cosine.function_call,
    ``Quadrature.CSource.Cosine.source_call,
    ``Quadrature.CSource.Cosine.callback_contract,
    ``Quadrature.CSource.Library.from_sources,
    ``Quadrature.CSource.Library.initialized,
    ``Quadrature.CSource.Library.source_integrate_call,
    ``Quadrature.CSource.Library.source_wrapper_call,
    ``Quadrature.CSource.Library.initialized_integrate_call,
    ``Quadrature.CSource.Library.initialized_wrapper_call,
    ``Quadrature.CSource.Library.integral_accuracy,
    ``Quadrature.CSource.Library.parsed_wrapper_accuracy,
    ``Quadrature.CSource.C.SmallStep.Total.reaches,
    ``Quadrature.CSource.C.SmallStep.CallCorrect.accessible,
    ``Quadrature.CSource.C.SmallStep.CallCorrect.progress,
    ``Quadrature.CSource.Cosine.call_correct,
    ``Quadrature.CSource.C.accessor_call_correct,
    ``Quadrature.CSource.C.testfun_call_correct,
    ``Quadrature.CSource.C.integrator_call_correct,
    ``Quadrature.CSource.C.wrapper_call_correct,
    ``Quadrature.CSource.Library.initialized_integrate_correct,
    ``Quadrature.CSource.Library.initialized_wrapper_correct,
    ``Quadrature.CSource.Library.integral_total_accuracy,
    ``Quadrature.CSource.Library.parsed_wrapper_total_accuracy,
    ``Quadrature.CSource.Cosine.translation,
    ``Quadrature.CSource.Cosine.normalized_execution,
    ``Quadrature.CSource.CallRefinement.outcomes_iff,
    ``Quadrature.CSource.CallRefinement.source_accessible,
    ``Quadrature.CSource.CallRefinement.target_accessible,
    ``Quadrature.CSource.CallRefinement.source_progress,
    ``Quadrature.CSource.CallRefinement.target_progress,
    ``Quadrature.CSource.CallRefinement.memory_agrees,
    ``Quadrature.CSource.Library.Normalized.from_sources,
    ``Quadrature.CSource.Library.Normalized.initialized,
    ``Quadrature.CSource.Library.Normalized.internal,
    ``Quadrature.CSource.Library.point_refinement,
    ``Quadrature.CSource.Library.weight_refinement,
    ``Quadrature.CSource.Library.integrate_refinement,
    ``Quadrature.CSource.Library.callback_refinement,
    ``Quadrature.CSource.Library.cosine_refinement,
    ``Quadrature.CSource.Library.wrapper_refinement,
    ``Quadrature.CSource.Library.parsed_refinement,
    ``Quadrature.CSource.Library.initialized_outcomes_iff,
    ``Quadrature.CSource.Library.wrapper_outcomes]
  for name in required do
    unless (env.find? name).isSome do
      throwError m!"Missing source wrapper declaration: {name}"
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants do
    let text := name.toString
    if text.startsWith "Quadrature.CSource." ||
        text.startsWith "_private.Quadrature.CSource." then
      if info.isAxiom then
        throwError m!"Source wrapper axiom declaration is not allowed: {name}"
      for axiomName in ← collectAxioms name do
        unless allowed.contains axiomName do
          throwError m!"{name} depends on unapproved axiom {axiomName}"
      checked := checked + 1
      if info.isTheorem then
        theorems := theorems + 1
  logInfo m!"Audited {checked} source-wrapper declarations, including {theorems} theorems."
  logInfo "The original callback and two-point wrapper have complete terminating strategy calls."
  logInfo "Callback entry, integer promotion, arithmetic, return, and freeing are derived."
  logInfo "The wrapper composes the integrator with a proved callback contract."
  logInfo "The internal C cosine executes the rounded polynomial and preserves caller memory."
  logInfo "Parsing and initialization discharge the polynomial library's table/function contracts."
  logInfo "Every C evaluation order terminates correctly for the initialized polynomial library."
  logInfo "No reachable state gets stuck, and no infinite execution is possible."
  logInfo "All ten stored orders have integral-error bounds in the C small-step semantics."
  logInfo "The parsed two-point wrapper returns 0x3fead02c771c35ed, with integral error <= 0.00356."
  logInfo "Both frontend outputs have equivalent behavior for all six selected functions."
  logInfo "The comparison includes initialization, lookup, all returns, termination, and memory."
  logInfo "The Clight proof requires no external-call determinism assumption."
  logInfo "The original external-cosine variant retains its library contract."
  logInfo "General frontend correctness, Lean/Rocq correspondence, and native execution remain open."
