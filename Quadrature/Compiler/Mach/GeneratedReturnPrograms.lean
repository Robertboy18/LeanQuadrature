import Quadrature.Compiler.Asm.GeneratedReturnAddresses
import Quadrature.Compiler.Mach.StoredTotalCorrectness

/-!
# Mach executions with addresses justified by assembly generation

Total correctness of the ten programs in the Mach semantics with the Lean Asmgen
translation's oracle `Asm.Generation.returnAddress`. Read `predictor_sound` first: by
`Asm.Generation.Imported.table_valid`, every offset the imported table predicts is a
return address of the translation, and `return_address_unique` makes the predictor agree
with it. The theorems of `StoredTotalCorrectness` then transfer without taking table
membership as the definition of a return address.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Mach.GeneratedPrograms

open CC Quadrature.Binary64 StoredPrograms
open FloatLib.Floats.Formats.BinaryInterchange

/-- For n = 1..10, every offset predicted from the imported table is a return address of the
Lean Asmgen translation. -/
theorem predictor_sound (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    ReturnAddressExecutorSound (ImportedAddresses.predict n) Asm.Generation.returnAddress := by
  intro function continuation offset h
  exact Asm.Generation.Imported.table_address_sound n hlo hhi
    ((ImportedAddresses.predict_iff n hlo hhi).mp h)

/-- For n = 1..10, every predicted offset is the only return address the translation permits. -/
theorem predictor_agrees (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    ReturnAddressExecutorAgrees (ImportedAddresses.predict n) Asm.Generation.returnAddress := by
  intro function continuation offset other hchecked hother
  exact Asm.Generation.return_address_unique
    (predictor_sound n hlo hhi function continuation offset hchecked) hother

variable [ExternalCalls]

/-- A complete semantic execution exists under the translation's oracle, from the program's
own initialized memory. -/
theorem execution (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    ∃ start finish, InitialState (Imported.program n) start ∧
      Steps Asm.Generation.returnAddress (Imported.program n).globalenv start
        (resultTrace (Clight.StoredPolynomial.result n)) finish ∧
      FinalState finish Integers.Int.zero :=
  execute_program_sound (predictor_sound n hlo hhi) annotated_external_executor_sound
    (execution_checked_result n hlo hhi)

/-- Every finite prefix can finish with the remaining part of the certified trace. -/
theorem reachable_can_finish (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10)
    {start state : State} {trace : Trace}
    (hinit : InitialState (Imported.program n) start)
    (hrun : Steps Asm.Generation.returnAddress (Imported.program n).globalenv start trace state) :
    ∃ remaining finish, trace ++ remaining = resultTrace (Clight.StoredPolynomial.result n) ∧
      Steps Asm.Generation.returnAddress (Imported.program n).globalenv state remaining finish ∧
      FinalState finish Integers.Int.zero :=
  execute_program_prefix (predictor_sound n hlo hhi) (predictor_agrees n hlo hhi)
    annotated_external_executor_sound annotated_external_executor_agrees
    (execution_checked_result n hlo hhi) hinit hrun

/-- No reachable state is stuck unless it is a successful final state. -/
theorem progress (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10)
    {start state : State} {trace : Trace}
    (hinit : InitialState (Imported.program n) start)
    (hrun : Steps Asm.Generation.returnAddress (Imported.program n).globalenv start trace state) :
    FinalState state Integers.Int.zero ∨
      ∃ emitted next, Step Asm.Generation.returnAddress (Imported.program n).globalenv
        state emitted next :=
  execute_program_progress (predictor_sound n hlo hhi) (predictor_agrees n hlo hhi)
    annotated_external_executor_sound annotated_external_executor_agrees
    (execution_checked_result n hlo hhi) hinit hrun

/-- Every maximal finite execution emits exactly the certified result and exits zero. -/
theorem maximal_execution (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10)
    {start state : State} {trace : Trace}
    (hinit : InitialState (Imported.program n) start)
    (hrun : Steps Asm.Generation.returnAddress (Imported.program n).globalenv start trace state)
    (hstop : ∀ emitted next, ¬ Step Asm.Generation.returnAddress (Imported.program n).globalenv
      state emitted next) :
    trace = resultTrace (Clight.StoredPolynomial.result n) ∧
      FinalState state Integers.Int.zero :=
  execute_program_unique (predictor_sound n hlo hhi) (predictor_agrees n hlo hhi)
    annotated_external_executor_sound annotated_external_executor_agrees
    (execution_checked_result n hlo hhi) hinit hrun hstop

/-- The certified finite run excludes every infinite sequence of semantic transitions. -/
theorem not_infinite (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) {start : State}
    (hinit : InitialState (Imported.program n) start)
    (states : Nat → State) (traces : Nat → Trace) (hstart : states 0 = start)
    (hsteps : ∀ k, Step Asm.Generation.returnAddress (Imported.program n).globalenv
      (states k) (traces k) (states (k + 1))) : False :=
  execute_program_not_infinite (predictor_agrees n hlo hhi) annotated_external_executor_agrees
    (execution_checked_result n hlo hhi) hinit states traces hstart hsteps

/-- Every completed execution carries the same finite, accurate binary64 observation. -/
theorem final_accuracy (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10)
    {start state : State} {trace : Trace} {status : Integers.Int}
    (hinit : InitialState (Imported.program n) start)
    (hrun : Steps Asm.Generation.returnAddress (Imported.program n).globalenv start trace state)
    (hfinal : FinalState state status) :
    status = Integers.Int.zero ∧ ∃ value : Value,
      trace = resultTrace value ∧ Model.isFinite value = true ∧
      |Model.toReal value - ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤
        Clight.StoredPolynomial.errorBound n := by
  obtain ⟨htrace, hstatus⟩ :=
    maximal_execution n hlo hhi hinit hrun (fun _ _ => final_state_stuck hfinal)
  exact ⟨final_state_unique hfinal hstatus, Clight.StoredPolynomial.result n, htrace,
    Clight.StoredPolynomial.integral_accuracy n hlo hhi⟩

end Quadrature.Mach.GeneratedPrograms
