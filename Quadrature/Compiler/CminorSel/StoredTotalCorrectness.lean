import Quadrature.Compiler.CminorSel.Determinism
import Quadrature.Compiler.CminorSel.StoredPrograms

/-!
# All executions of the ten CminorSel programs

For n = 1..10, every execution of `Imported.program n` terminates, and every terminating
execution emits exactly `resultTrace (result n)` and exits 0. `progress` says every
reachable state is final or can step, `maximal_execution` fixes the trace and exit
status of every maximal run, `not_infinite` excludes infinite runs, and
`final_accuracy` adds the integral-error bound of the emitted value.

The statements hold for any external-call relation, because the checked runs call only
the annotation builtin, whose events are determined by its arguments.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.CminorSel.StoredPrograms

open CC Quadrature.Binary64
open FloatLib.Floats.Formats.BinaryInterchange

/-- `execution_checked` restated with the emitted bits replaced by the binary64 value
`Clight.StoredPolynomial.result n`. -/
theorem execution_checked_result (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    executeProgram annotatedExternalCall (Imported.program n) (stepCount n) =
      some (resultTrace (Clight.StoredPolynomial.result n), Integers.Int.zero) := by
  rw [Clight.StoredPolynomial.result_value n hlo hhi]
  exact execution_checked n hlo hhi

variable [ExternalCalls]

/-- Every `Steps` run from an initial state of the n-node program extends to a final state,
completing `resultTrace (result n)` and exiting 0. -/
theorem reachable_can_finish (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10)
    {start state : State} {trace : Trace}
    (hinit : InitialState (Imported.program n) start)
    (hrun : Steps (Imported.program n).globalenv start trace state) :
    ∃ remaining finish, trace ++ remaining = resultTrace (Clight.StoredPolynomial.result n) ∧
      Steps (Imported.program n).globalenv state remaining finish ∧
      FinalState finish Integers.Int.zero :=
  execute_program_prefix annotated_external_executor_sound annotated_external_executor_agrees
    (execution_checked_result n hlo hhi) hinit hrun

/-- Every reachable state of the n-node program is the final state with exit status 0 or admits a
further `Step`. -/
theorem progress (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10)
    {start state : State} {trace : Trace}
    (hinit : InitialState (Imported.program n) start)
    (hrun : Steps (Imported.program n).globalenv start trace state) :
    FinalState state Integers.Int.zero ∨
      ∃ emitted next, Step (Imported.program n).globalenv state emitted next :=
  execute_program_progress annotated_external_executor_sound annotated_external_executor_agrees
    (execution_checked_result n hlo hhi) hinit hrun

/-- Every maximal `Steps` run from an initial state of the n-node program emits
`resultTrace (result n)` and ends in the final state with exit status 0. -/
theorem maximal_execution (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10)
    {start state : State} {trace : Trace}
    (hinit : InitialState (Imported.program n) start)
    (hrun : Steps (Imported.program n).globalenv start trace state)
    (hstop : ∀ emitted next, ¬ Step (Imported.program n).globalenv state emitted next) :
    trace = resultTrace (Clight.StoredPolynomial.result n) ∧
      FinalState state Integers.Int.zero :=
  execute_program_unique annotated_external_executor_sound annotated_external_executor_agrees
    (execution_checked_result n hlo hhi) hinit hrun hstop

/-- No infinite sequence of `Step` transitions starts at an initial state of the n-node program. -/
theorem not_infinite (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) {start : State}
    (hinit : InitialState (Imported.program n) start)
    (states : Nat → State) (traces : Nat → Trace) (hstart : states 0 = start)
    (hsteps : ∀ k, Step (Imported.program n).globalenv
      (states k) (traces k) (states (k + 1))) : False :=
  execute_program_not_infinite annotated_external_executor_agrees
    (execution_checked_result n hlo hhi) hinit states traces hstart hsteps

/-- Every terminating execution of the n-node program exits 0 and emits one finite binary64 value
within `errorBound n` of the integral. -/
theorem final_accuracy (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10)
    {start state : State} {trace : Trace} {status : Integers.Int}
    (hinit : InitialState (Imported.program n) start)
    (hrun : Steps (Imported.program n).globalenv start trace state)
    (hfinal : FinalState state status) :
    status = Integers.Int.zero ∧ ∃ value : Value,
      trace = resultTrace value ∧ Model.isFinite value = true ∧
      |Model.toReal value - ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤
        Clight.StoredPolynomial.errorBound n := by
  obtain ⟨htrace, hstatus⟩ :=
    maximal_execution n hlo hhi hinit hrun (fun _ _ => final_state_stuck hfinal)
  exact ⟨final_state_unique hfinal hstatus, Clight.StoredPolynomial.result n, htrace,
    Clight.StoredPolynomial.integral_accuracy n hlo hhi⟩

end Quadrature.CminorSel.StoredPrograms
