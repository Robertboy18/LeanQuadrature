import Quadrature.Compiler.RTL.Preallocation
import Quadrature.Compiler.RTL.StoredTotalCorrectness

/-!
# Total correctness immediately before register allocation

`RTL.Preallocation.program n` is the RTL after CompCert's RTL-level passes with
optimizations off, the input to register allocation. This file proves for it the same
results that `StoredPrograms` and `StoredTotalCorrectness` prove for `Imported.program n`:
the checked run (`execution_checked`), the `Steps` derivation (`execution`), the
integral-error bound (`execution_accuracy`), and total correctness (`progress`,
`maximal_execution`, `not_infinite`, `final_accuracy`). The step count is the same
`stepCount n` as for the initial RTL programs.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.RTL.Preallocation

open CC Quadrature.Binary64
open FloatLib.Floats.Formats.BinaryInterchange
open StoredPrograms (resultTrace stepCount)

-- Kernel evaluation of the checker on all ten pre-allocation programs, `stepCount n` steps each.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- For n = 1..10, the checker runs the n-node program for `stepCount n` steps and returns its
result annotation and exit status 0, by kernel evaluation. -/
theorem execution_checked (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    executeProgram annotatedExternalCall (program n) (stepCount n) =
      some (resultTrace (Model.ofNatBits (Clight.StoredPolynomial.resultBits n)),
        Integers.Int.zero) := by
  interval_cases n <;> decide +kernel

/-- For n = 1..10, some initial state of the n-node program runs by `Steps` to a final state,
emitting `resultTrace (result n)` and exiting 0. -/
theorem execution [ExternalCalls] (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    ∃ start finish, InitialState (program n) start ∧
      Steps (program n).globalenv start
        (resultTrace (Clight.StoredPolynomial.result n)) finish ∧
      FinalState finish Integers.Int.zero := by
  rw [Clight.StoredPolynomial.result_value n hlo hhi]
  exact execute_program_sound annotated_external_executor_sound (execution_checked n hlo hhi)

/-- The value emitted by `execution` is finite and within `errorBound n` of the integral of the
fixed integrand over `[-1, 1]`. -/
theorem execution_accuracy [ExternalCalls] (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    ∃ value : Value, ∃ start finish,
      InitialState (program n) start ∧
      Steps (program n).globalenv start (resultTrace value) finish ∧
      FinalState finish Integers.Int.zero ∧
      Model.isFinite value = true ∧
      |Model.toReal value - ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤
        Clight.StoredPolynomial.errorBound n := by
  obtain ⟨start, finish, hinit, hrun, hfinal⟩ := execution n hlo hhi
  exact ⟨Clight.StoredPolynomial.result n, start, finish, hinit, hrun, hfinal,
    Clight.StoredPolynomial.integral_accuracy n hlo hhi⟩

/-- `execution_checked` restated with the emitted bits replaced by the binary64 value
`Clight.StoredPolynomial.result n`. -/
theorem execution_checked_result (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    executeProgram annotatedExternalCall (program n) (stepCount n) =
      some (resultTrace (Clight.StoredPolynomial.result n), Integers.Int.zero) := by
  rw [Clight.StoredPolynomial.result_value n hlo hhi]
  exact execution_checked n hlo hhi

variable [ExternalCalls]

/-- Every `Steps` run from an initial state of the n-node program extends to a final state,
completing `resultTrace (result n)` and exiting 0. -/
theorem reachable_can_finish (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10)
    {start state : State} {trace : Trace}
    (hinit : InitialState (program n) start)
    (hrun : Steps (program n).globalenv start trace state) :
    ∃ remaining finish, trace ++ remaining = resultTrace (Clight.StoredPolynomial.result n) ∧
      Steps (program n).globalenv state remaining finish ∧
      FinalState finish Integers.Int.zero :=
  execute_program_prefix annotated_external_executor_sound annotated_external_executor_agrees
    (execution_checked_result n hlo hhi) hinit hrun

/-- Every reachable state of the n-node program is the final state with exit status 0 or admits a
further `Step`. -/
theorem progress (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10)
    {start state : State} {trace : Trace}
    (hinit : InitialState (program n) start)
    (hrun : Steps (program n).globalenv start trace state) :
    FinalState state Integers.Int.zero ∨
      ∃ emitted next, Step (program n).globalenv state emitted next :=
  execute_program_progress annotated_external_executor_sound annotated_external_executor_agrees
    (execution_checked_result n hlo hhi) hinit hrun

/-- Every maximal `Steps` run from an initial state of the n-node program emits
`resultTrace (result n)` and ends in the final state with exit status 0. -/
theorem maximal_execution (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10)
    {start state : State} {trace : Trace}
    (hinit : InitialState (program n) start)
    (hrun : Steps (program n).globalenv start trace state)
    (hstop : ∀ emitted next, ¬ Step (program n).globalenv state emitted next) :
    trace = resultTrace (Clight.StoredPolynomial.result n) ∧
      FinalState state Integers.Int.zero :=
  execute_program_unique annotated_external_executor_sound annotated_external_executor_agrees
    (execution_checked_result n hlo hhi) hinit hrun hstop

/-- No infinite sequence of `Step` transitions starts at an initial state of the n-node program. -/
theorem not_infinite (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) {start : State}
    (hinit : InitialState (program n) start)
    (states : Nat → State) (traces : Nat → Trace) (hstart : states 0 = start)
    (hsteps : ∀ k, Step (program n).globalenv
      (states k) (traces k) (states (k + 1))) : False :=
  execute_program_not_infinite annotated_external_executor_agrees
    (execution_checked_result n hlo hhi) hinit states traces hstart hsteps

/-- Every terminating execution of the n-node program exits 0 and emits one finite binary64 value
within `errorBound n` of the integral. -/
theorem final_accuracy (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10)
    {start state : State} {trace : Trace} {status : Integers.Int}
    (hinit : InitialState (program n) start)
    (hrun : Steps (program n).globalenv start trace state)
    (hfinal : FinalState state status) :
    status = Integers.Int.zero ∧ ∃ value : Value,
      trace = resultTrace value ∧ Model.isFinite value = true ∧
      |Model.toReal value - ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤
        Clight.StoredPolynomial.errorBound n := by
  obtain ⟨htrace, hstatus⟩ :=
    maximal_execution n hlo hhi hinit hrun (fun _ _ => final_state_stuck hfinal)
  exact ⟨final_state_unique hfinal hstatus, Clight.StoredPolynomial.result n, htrace,
    Clight.StoredPolynomial.integral_accuracy n hlo hhi⟩

end Quadrature.RTL.Preallocation
