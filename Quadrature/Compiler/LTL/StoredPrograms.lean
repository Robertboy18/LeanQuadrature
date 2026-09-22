import Quadrature.Clight.StoredAccuracy
import Quadrature.Compiler.LTL.Imported
import Quadrature.Compiler.LTL.ProgramExecution

/-!
# Executions of the ten LTL programs

`execution_checked` runs the checker on `Imported.program n` for `stepCount n` steps,
n = 1..10, by kernel evaluation. Each run initializes all 73 globals, executes the LTL
accessors, integrator, internal polynomial, and caller, emits its binary64 result, and
exits 0. The emitted value is `Clight.StoredPolynomial.result n` and inherits its
integral-error bound (`execution_accuracy`). `execution` turns the checked run into a
`Steps` derivation.

`StoredTotalCorrectness` proves that every execution agrees with these runs.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.LTL.StoredPrograms

open CC Quadrature.Binary64
open FloatLib.Floats.Formats.BinaryInterchange

/-- `resultTrace v` is the one-event trace of the annotation `quadrature-result` carrying the
binary64 value `v`. -/
def resultTrace (value : Value) : Trace :=
  [.Event_annot "quadrature-result" [.EVfloat value]]

/-- `stepCount n` is the number of checker steps of the n-node LTL program: 42 plus 210 per node. -/
def stepCount (n : Nat) : Nat := 210 * n + 42

-- Kernel evaluation of the checker on all ten imported programs (`stepCount n` steps each).
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- For n = 1..10, the checker runs the n-node program for `stepCount n` steps and returns its
result annotation and exit status 0, by kernel evaluation. -/
theorem execution_checked (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    executeProgram annotatedExternalCall (Imported.program n) (stepCount n) =
      some (resultTrace (Model.ofNatBits (Clight.StoredPolynomial.resultBits n)),
        Integers.Int.zero) := by
  interval_cases n <;> decide +kernel

/-- For n = 1..10, some initial state of the n-node program runs by `Steps` to a final state,
emitting `resultTrace (result n)` and exiting 0. -/
theorem execution [ExternalCalls] (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    ∃ start finish, InitialState (Imported.program n) start ∧
      Steps (Imported.program n).globalenv start
        (resultTrace (Clight.StoredPolynomial.result n)) finish ∧
      FinalState finish Integers.Int.zero := by
  rw [Clight.StoredPolynomial.result_value n hlo hhi]
  exact execute_program_sound annotated_external_executor_sound (execution_checked n hlo hhi)

/-- The value emitted by `execution` is finite and within `errorBound n` of the integral of the
fixed integrand over `[-1, 1]`. -/
theorem execution_accuracy [ExternalCalls] (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    ∃ value : Value, ∃ start finish,
      InitialState (Imported.program n) start ∧
      Steps (Imported.program n).globalenv start (resultTrace value) finish ∧
      FinalState finish Integers.Int.zero ∧
      Model.isFinite value = true ∧
      |Model.toReal value - ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤
        Clight.StoredPolynomial.errorBound n := by
  obtain ⟨start, finish, hinit, hrun, hfinal⟩ := execution n hlo hhi
  exact ⟨Clight.StoredPolynomial.result n, start, finish, hinit, hrun, hfinal,
    Clight.StoredPolynomial.integral_accuracy n hlo hhi⟩

end Quadrature.LTL.StoredPrograms
