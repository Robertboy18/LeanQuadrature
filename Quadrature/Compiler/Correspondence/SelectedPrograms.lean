import Quadrature.Compiler.CminorSel.StoredTotalCorrectness
import Quadrature.Compiler.Correspondence.CallerFunctions

/-!
# Observable behavior of the ten instruction-selected applications

Relates the Cminor and CminorSel programs for n = 1..10 by their observations (event trace,
exit status). Read `cminor_selected_final_observations_iff` first: both programs have exactly
the observation `resultTrace (result n)` with exit status 0, because each side's total
correctness theorems exclude every other outcome. `clight_selected_final_observations_iff`
composes with the caller theorem to reach Clight under `ExternalCallsDeterministic`.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Compiler

open CC

/-- Every final Cminor observation is possible in CminorSel, and conversely. -/
theorem cminor_selected_final_observations_iff [ExternalCalls]
    (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) (trace : Trace) (status : Integers.Int) :
    (∃ start finish, Cminor.InitialState (Cminor.Imported.program n) start ∧
      Cminor.Steps (Cminor.Imported.program n).globalenv start trace finish ∧
      Cminor.FinalState finish status) ↔
    (∃ start finish, CminorSel.InitialState (CminorSel.Imported.program n) start ∧
      CminorSel.Steps (CminorSel.Imported.program n).globalenv start trace finish ∧
      CminorSel.FinalState finish status) := by
  constructor
  · rintro ⟨start, finish, hinit, hrun, hfinal⟩
    obtain ⟨htrace, hstatus⟩ := Cminor.StoredPrograms.maximal_execution n hlo hhi hinit hrun
      (fun _ _ => Cminor.final_state_stuck hfinal)
    have hzero := Cminor.final_state_unique hfinal hstatus
    simpa only [htrace, hzero, Cminor.StoredPrograms.resultTrace,
      CminorSel.StoredPrograms.resultTrace] using CminorSel.StoredPrograms.execution n hlo hhi
  · rintro ⟨start, finish, hinit, hrun, hfinal⟩
    obtain ⟨htrace, hstatus⟩ := CminorSel.StoredPrograms.maximal_execution n hlo hhi hinit hrun
      (fun _ _ => CminorSel.final_state_stuck hfinal)
    have hzero := CminorSel.final_state_unique hfinal hstatus
    simpa only [htrace, hzero, Cminor.StoredPrograms.resultTrace,
      CminorSel.StoredPrograms.resultTrace] using Cminor.StoredPrograms.execution n hlo hhi

/-- The source application's possible final observations agree with its selected program. -/
theorem clight_selected_final_observations_iff [calls : ExternalCalls]
    [ExternalCallsDeterministic calls]
    (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) (trace : Trace) (status : Integers.Int) :
    (∃ start memory, InitialState (Binary64.Clight.Application.program n) start ∧
      Star (Step2 (Binary64.Clight.Application.program n).globalenv) start trace
        (.Returnstate (.Vint status) .Kstop memory)) ↔
    (∃ start finish, CminorSel.InitialState (CminorSel.Imported.program n) start ∧
      CminorSel.Steps (CminorSel.Imported.program n).globalenv start trace finish ∧
      CminorSel.FinalState finish status) :=
  (main_final_observations_iff n hlo hhi trace status).trans
    (cminor_selected_final_observations_iff n hlo hhi trace status)

end Quadrature.Compiler
