import Quadrature.Compiler.Correspondence.SelectedPrograms
import Quadrature.Compiler.RTL.StoredTotalCorrectness

/-!
# Observable behavior of the ten RTL applications

Relates the CminorSel and RTL programs for n = 1..10 by their observations (event trace,
exit status). Read `selected_rtl_final_observations_iff` first: both programs have exactly
the observation `resultTrace (result n)` with exit status 0, because each side's total
correctness theorems exclude every other outcome. `clight_rtl_final_observations_iff`
composes with the selection theorem to reach Clight under `ExternalCallsDeterministic`.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Compiler

open CC

/-- Every final CminorSel observation is possible in RTL, and conversely. -/
theorem selected_rtl_final_observations_iff [ExternalCalls]
    (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) (trace : Trace) (status : Integers.Int) :
    (∃ start finish, CminorSel.InitialState (CminorSel.Imported.program n) start ∧
      CminorSel.Steps (CminorSel.Imported.program n).globalenv start trace finish ∧
      CminorSel.FinalState finish status) ↔
    (∃ start finish, RTL.InitialState (RTL.Imported.program n) start ∧
      RTL.Steps (RTL.Imported.program n).globalenv start trace finish ∧
      RTL.FinalState finish status) := by
  constructor
  · rintro ⟨start, finish, hinit, hrun, hfinal⟩
    obtain ⟨htrace, hstatus⟩ := CminorSel.StoredPrograms.maximal_execution n hlo hhi hinit hrun
      (fun _ _ => CminorSel.final_state_stuck hfinal)
    have hzero := CminorSel.final_state_unique hfinal hstatus
    simpa only [htrace, hzero, CminorSel.StoredPrograms.resultTrace,
      RTL.StoredPrograms.resultTrace] using RTL.StoredPrograms.execution n hlo hhi
  · rintro ⟨start, finish, hinit, hrun, hfinal⟩
    obtain ⟨htrace, hstatus⟩ := RTL.StoredPrograms.maximal_execution n hlo hhi hinit hrun
      (fun _ _ => RTL.final_state_stuck hfinal)
    have hzero := RTL.final_state_unique hfinal hstatus
    simpa only [htrace, hzero, CminorSel.StoredPrograms.resultTrace,
      RTL.StoredPrograms.resultTrace] using CminorSel.StoredPrograms.execution n hlo hhi

/-- The source application's possible final observations agree with its RTL program. -/
theorem clight_rtl_final_observations_iff [calls : ExternalCalls]
    [ExternalCallsDeterministic calls]
    (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) (trace : Trace) (status : Integers.Int) :
    (∃ start memory, InitialState (Binary64.Clight.Application.program n) start ∧
      Star (Step2 (Binary64.Clight.Application.program n).globalenv) start trace
        (.Returnstate (.Vint status) .Kstop memory)) ↔
    (∃ start finish, RTL.InitialState (RTL.Imported.program n) start ∧
      RTL.Steps (RTL.Imported.program n).globalenv start trace finish ∧
      RTL.FinalState finish status) :=
  (clight_selected_final_observations_iff n hlo hhi trace status).trans
    (selected_rtl_final_observations_iff n hlo hhi trace status)

end Quadrature.Compiler
