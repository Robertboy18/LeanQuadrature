import Quadrature.Compiler.Mach.Determinism
import Quadrature.Compiler.Mach.StoredPrograms

/-!
# All executions of the ten imported Mach programs

Total correctness of the ten programs in the Mach semantics with the table oracle
`ImportedAddresses.relation n`: for n = 1..10, every execution of `Imported.program n`
terminates, and every terminating execution emits exactly `resultTrace (result n)` and
exits 0. Read `maximal_execution` first, then `not_infinite`. The predictor contract is
discharged by `ImportedAddresses.predict_agrees`, from the table's consistency, and the
theorems hold for any external-call relation because the executions call only numeric
annotations. `GeneratedReturnPrograms` restates them for the Lean Asmgen translation's
oracle `Asm.Generation.returnAddress`.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Mach

/-- For n = 1..10, every offset predicted for the n-node program is the only one its table
permits. -/
theorem ImportedAddresses.predict_agrees (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    ReturnAddressExecutorAgrees (predict n) (relation n) := by
  intro function code offset other hchecked hother
  exact Option.some.inj (hchecked.symm.trans ((predict_iff n hlo hhi).mpr hother))

namespace StoredPrograms

open CC Quadrature.Binary64
open FloatLib.Floats.Formats.BinaryInterchange

/-- The checked execution of the n-node program, stated with the binary64 `result n` in place
of its bit pattern. -/
theorem execution_checked_result (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    executeProgram (ImportedAddresses.predict n) annotatedExternalCall
      (Imported.program n) (stepCount n) =
      some (resultTrace (Clight.StoredPolynomial.result n), Integers.Int.zero) := by
  rw [Clight.StoredPolynomial.result_value n hlo hhi]
  exact execution_checked n hlo hhi

variable [ExternalCalls]

/-- Every finite prefix can finish with the remaining part of the certified trace. -/
theorem reachable_can_finish (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10)
    {start state : State} {trace : Trace}
    (hinit : InitialState (Imported.program n) start)
    (hrun : Steps (ImportedAddresses.relation n) (Imported.program n).globalenv
      start trace state) :
    ∃ remaining finish, trace ++ remaining = resultTrace (Clight.StoredPolynomial.result n) ∧
      Steps (ImportedAddresses.relation n) (Imported.program n).globalenv
        state remaining finish ∧ FinalState finish Integers.Int.zero :=
  execute_program_prefix (ImportedAddresses.predict_sound n)
    (ImportedAddresses.predict_agrees n hlo hhi)
    annotated_external_executor_sound annotated_external_executor_agrees
    (execution_checked_result n hlo hhi) hinit hrun

/-- No reachable state is stuck unless it is a successful final state. -/
theorem progress (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10)
    {start state : State} {trace : Trace}
    (hinit : InitialState (Imported.program n) start)
    (hrun : Steps (ImportedAddresses.relation n) (Imported.program n).globalenv
      start trace state) :
    FinalState state Integers.Int.zero ∨
      ∃ emitted next, Step (ImportedAddresses.relation n) (Imported.program n).globalenv
        state emitted next :=
  execute_program_progress (ImportedAddresses.predict_sound n)
    (ImportedAddresses.predict_agrees n hlo hhi)
    annotated_external_executor_sound annotated_external_executor_agrees
    (execution_checked_result n hlo hhi) hinit hrun

/-- Every maximal finite execution emits exactly the certified result and exits zero. -/
theorem maximal_execution (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10)
    {start state : State} {trace : Trace}
    (hinit : InitialState (Imported.program n) start)
    (hrun : Steps (ImportedAddresses.relation n) (Imported.program n).globalenv
      start trace state)
    (hstop : ∀ emitted next, ¬ Step (ImportedAddresses.relation n) (Imported.program n).globalenv
      state emitted next) :
    trace = resultTrace (Clight.StoredPolynomial.result n) ∧
      FinalState state Integers.Int.zero :=
  execute_program_unique (ImportedAddresses.predict_sound n)
    (ImportedAddresses.predict_agrees n hlo hhi)
    annotated_external_executor_sound annotated_external_executor_agrees
    (execution_checked_result n hlo hhi) hinit hrun hstop

/-- The certified finite run excludes every infinite sequence of semantic transitions. -/
theorem not_infinite (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) {start : State}
    (hinit : InitialState (Imported.program n) start)
    (states : Nat → State) (traces : Nat → Trace) (hstart : states 0 = start)
    (hsteps : ∀ k, Step (ImportedAddresses.relation n) (Imported.program n).globalenv
      (states k) (traces k) (states (k + 1))) : False :=
  execute_program_not_infinite (ImportedAddresses.predict_agrees n hlo hhi)
    annotated_external_executor_agrees
    (execution_checked_result n hlo hhi) hinit states traces hstart hsteps

/-- Every completed execution carries the same finite, accurate binary64 observation. -/
theorem final_accuracy (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10)
    {start state : State} {trace : Trace} {status : Integers.Int}
    (hinit : InitialState (Imported.program n) start)
    (hrun : Steps (ImportedAddresses.relation n) (Imported.program n).globalenv
      start trace state)
    (hfinal : FinalState state status) :
    status = Integers.Int.zero ∧ ∃ value : Value,
      trace = resultTrace value ∧ Model.isFinite value = true ∧
      |Model.toReal value - ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤
        Clight.StoredPolynomial.errorBound n := by
  obtain ⟨htrace, hstatus⟩ :=
    maximal_execution n hlo hhi hinit hrun (fun _ _ => final_state_stuck hfinal)
  exact ⟨final_state_unique hfinal hstatus, Clight.StoredPolynomial.result n, htrace,
    Clight.StoredPolynomial.integral_accuracy n hlo hhi⟩

end StoredPrograms
end Quadrature.Mach
