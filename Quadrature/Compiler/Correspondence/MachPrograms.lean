import Quadrature.Compiler.Correspondence.LinearPrograms
import Quadrature.Compiler.Mach.StoredTotalCorrectness

/-!
# Application observations after stack layout

Relates the Linear and Mach programs for n = 1..10 by their observations (event trace, exit
status), with Mach under the table oracle `ImportedAddresses.relation n`. Read
`linear_mach_final_observations_iff` first: both programs have exactly the observation
`resultTrace (result n)` with exit status 0, because each side's total correctness theorems
exclude every other outcome. The remaining theorems compose the chain from the initial RTL
programs and from Clight under `ExternalCallsDeterministic`.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Compiler

open CC

/-- Stack layout preserves the possible final observations of all ten applications. -/
theorem linear_mach_final_observations_iff [ExternalCalls]
    (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) (trace : Trace) (status : Integers.Int) :
    (∃ start finish, Linear.InitialState (Linear.Imported.program n) start ∧
      Linear.Steps (Linear.Imported.program n).globalenv start trace finish ∧
      Linear.FinalState finish status) ↔
    (∃ start finish, Mach.InitialState (Mach.Imported.program n) start ∧
      Mach.Steps (Mach.ImportedAddresses.relation n) (Mach.Imported.program n).globalenv
        start trace finish ∧ Mach.FinalState finish status) := by
  constructor
  · rintro ⟨start, finish, hinit, hrun, hfinal⟩
    obtain ⟨htrace, hstatus⟩ := Linear.StoredPrograms.maximal_execution n hlo hhi hinit hrun
      (fun _ _ => Linear.final_state_stuck hfinal)
    have hzero := Linear.final_state_unique hfinal hstatus
    simpa only [htrace, hzero, Linear.StoredPrograms.resultTrace, Mach.StoredPrograms.resultTrace]
      using Mach.StoredPrograms.execution n hlo hhi
  · rintro ⟨start, finish, hinit, hrun, hfinal⟩
    obtain ⟨htrace, hstatus⟩ := Mach.StoredPrograms.maximal_execution n hlo hhi hinit hrun
      (fun _ _ => Mach.final_state_stuck hfinal)
    have hzero := Mach.final_state_unique hfinal hstatus
    simpa only [htrace, hzero, Linear.StoredPrograms.resultTrace, Mach.StoredPrograms.resultTrace]
      using Linear.StoredPrograms.execution n hlo hhi

/-- The initial RTL and Mach applications have the same final observations. -/
theorem rtl_mach_final_observations_iff [ExternalCalls]
    (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) (trace : Trace) (status : Integers.Int) :
    (∃ start finish, RTL.InitialState (RTL.Imported.program n) start ∧
      RTL.Steps (RTL.Imported.program n).globalenv start trace finish ∧
      RTL.FinalState finish status) ↔
    (∃ start finish, Mach.InitialState (Mach.Imported.program n) start ∧
      Mach.Steps (Mach.ImportedAddresses.relation n) (Mach.Imported.program n).globalenv
        start trace finish ∧ Mach.FinalState finish status) :=
  (rtl_linear_final_observations_iff n hlo hhi trace status).trans
    (linear_mach_final_observations_iff n hlo hhi trace status)

/-- Clight and Mach agree on final observations under the source determinism condition. -/
theorem clight_mach_final_observations_iff [calls : ExternalCalls]
    [ExternalCallsDeterministic calls]
    (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) (trace : Trace) (status : Integers.Int) :
    (∃ start memory, InitialState (Binary64.Clight.Application.program n) start ∧
      Star (Step2 (Binary64.Clight.Application.program n).globalenv) start trace
        (.Returnstate (.Vint status) .Kstop memory)) ↔
    (∃ start finish, Mach.InitialState (Mach.Imported.program n) start ∧
      Mach.Steps (Mach.ImportedAddresses.relation n) (Mach.Imported.program n).globalenv
        start trace finish ∧ Mach.FinalState finish status) :=
  (clight_linear_final_observations_iff n hlo hhi trace status).trans
    (linear_mach_final_observations_iff n hlo hhi trace status)

end Quadrature.Compiler
