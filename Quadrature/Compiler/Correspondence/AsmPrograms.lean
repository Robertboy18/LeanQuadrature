import Quadrature.Compiler.Asm.StoredTotalCorrectness
import Quadrature.Compiler.Correspondence.MachPrograms
import Quadrature.Compiler.Mach.GeneratedReturnPrograms

/-!
# Application observations after assembly generation

Relates the Mach and assembly programs for n = 1..10 by their observations (event trace,
exit status). Read `mach_asm_final_observations_iff` first: both programs have exactly the
observation `resultTrace (result n)` with exit status 0, because each side's total
correctness theorems exclude every other outcome. `generated_mach_asm_final_observations_iff`
states the same with Mach under the Lean Asmgen translation's oracle
`Asm.Generation.returnAddress` instead of the table. The remaining theorems compose the
chain from the initial RTL programs and from Clight under `ExternalCallsDeterministic`.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Compiler

open CC

/-- Assembly generation preserves the possible final observations of all ten applications. -/
theorem mach_asm_final_observations_iff [ExternalCalls]
    (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) (trace : Trace) (status : Integers.Int) :
    (∃ start finish, Mach.InitialState (Mach.Imported.program n) start ∧
      Mach.Steps (Mach.ImportedAddresses.relation n) (Mach.Imported.program n).globalenv
        start trace finish ∧
      Mach.FinalState finish status) ↔
    (∃ start finish, Asm.InitialState (Asm.Imported.program n) start ∧
      Asm.Steps (Asm.Imported.program n).globalenv
        start trace finish ∧ Asm.FinalState finish status) := by
  constructor
  · rintro ⟨start, finish, hinit, hrun, hfinal⟩
    obtain ⟨htrace, hstatus⟩ := Mach.StoredPrograms.maximal_execution n hlo hhi hinit hrun
      (fun _ _ => Mach.final_state_stuck hfinal)
    have hzero := Mach.final_state_unique hfinal hstatus
    simpa only [htrace, hzero, Mach.StoredPrograms.resultTrace, Asm.StoredPrograms.resultTrace]
      using Asm.StoredPrograms.execution n hlo hhi
  · rintro ⟨start, finish, hinit, hrun, hfinal⟩
    obtain ⟨htrace, hstatus⟩ := Asm.StoredPrograms.maximal_execution n hlo hhi hinit hrun
      (fun _ _ => Asm.final_state_stuck hfinal)
    have hzero := Asm.final_state_unique hfinal hstatus
    simpa only [htrace, hzero, Mach.StoredPrograms.resultTrace, Asm.StoredPrograms.resultTrace]
      using Mach.StoredPrograms.execution n hlo hhi

/-- The same application agreement with return addresses justified by generated continuations. -/
theorem generated_mach_asm_final_observations_iff [ExternalCalls]
    (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) (trace : Trace) (status : Integers.Int) :
    (∃ start finish, Mach.InitialState (Mach.Imported.program n) start ∧
      Mach.Steps Asm.Generation.returnAddress (Mach.Imported.program n).globalenv
        start trace finish ∧ Mach.FinalState finish status) ↔
    (∃ start finish, Asm.InitialState (Asm.Imported.program n) start ∧
      Asm.Steps (Asm.Imported.program n).globalenv
        start trace finish ∧ Asm.FinalState finish status) := by
  constructor
  · rintro ⟨start, finish, hinit, hrun, hfinal⟩
    obtain ⟨htrace, hstatus⟩ := Mach.GeneratedPrograms.maximal_execution n hlo hhi hinit hrun
      (fun _ _ => Mach.final_state_stuck hfinal)
    have hzero := Mach.final_state_unique hfinal hstatus
    simpa only [htrace, hzero, Mach.StoredPrograms.resultTrace, Asm.StoredPrograms.resultTrace]
      using Asm.StoredPrograms.execution n hlo hhi
  · rintro ⟨start, finish, hinit, hrun, hfinal⟩
    obtain ⟨htrace, hstatus⟩ := Asm.StoredPrograms.maximal_execution n hlo hhi hinit hrun
      (fun _ _ => Asm.final_state_stuck hfinal)
    have hzero := Asm.final_state_unique hfinal hstatus
    simpa only [htrace, hzero, Mach.StoredPrograms.resultTrace, Asm.StoredPrograms.resultTrace]
      using Mach.GeneratedPrograms.execution n hlo hhi

/-- The initial RTL and Asm applications have the same final observations. -/
theorem rtl_asm_final_observations_iff [ExternalCalls]
    (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) (trace : Trace) (status : Integers.Int) :
    (∃ start finish, RTL.InitialState (RTL.Imported.program n) start ∧
      RTL.Steps (RTL.Imported.program n).globalenv start trace finish ∧
      RTL.FinalState finish status) ↔
    (∃ start finish, Asm.InitialState (Asm.Imported.program n) start ∧
      Asm.Steps (Asm.Imported.program n).globalenv
        start trace finish ∧ Asm.FinalState finish status) :=
  (rtl_mach_final_observations_iff n hlo hhi trace status).trans
    (mach_asm_final_observations_iff n hlo hhi trace status)

/-- Clight and Asm agree on final observations under the source determinism condition. -/
theorem clight_asm_final_observations_iff [calls : ExternalCalls]
    [ExternalCallsDeterministic calls]
    (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) (trace : Trace) (status : Integers.Int) :
    (∃ start memory, InitialState (Binary64.Clight.Application.program n) start ∧
      Star (Step2 (Binary64.Clight.Application.program n).globalenv) start trace
        (.Returnstate (.Vint status) .Kstop memory)) ↔
    (∃ start finish, Asm.InitialState (Asm.Imported.program n) start ∧
      Asm.Steps (Asm.Imported.program n).globalenv
        start trace finish ∧ Asm.FinalState finish status) :=
  (clight_mach_final_observations_iff n hlo hhi trace status).trans
    (mach_asm_final_observations_iff n hlo hhi trace status)

end Quadrature.Compiler
