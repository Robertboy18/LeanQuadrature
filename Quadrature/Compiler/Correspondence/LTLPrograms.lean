import Quadrature.Compiler.Correspondence.PreallocationPrograms
import Quadrature.Compiler.LTL.StoredTotalCorrectness

/-!
# Application observations across register allocation

Relates the pre-allocation RTL programs and the LTL programs for n = 1..10 by their
observations (event trace, exit status). Read `preallocation_ltl_final_observations_iff`
first: both programs have exactly the observation `resultTrace (result n)` with exit status
0, because each side's total correctness theorems exclude every other outcome. The
remaining theorems compose the chain from the initial RTL programs and from Clight under
`ExternalCallsDeterministic`.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Compiler

open CC

/-- Allocation preserves final observations for the ten certified applications. -/
theorem preallocation_ltl_final_observations_iff [ExternalCalls]
    (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) (trace : Trace) (status : Integers.Int) :
    (∃ start finish, RTL.InitialState (RTL.Preallocation.program n) start ∧
      RTL.Steps (RTL.Preallocation.program n).globalenv start trace finish ∧
      RTL.FinalState finish status) ↔
    (∃ start finish, LTL.InitialState (LTL.Imported.program n) start ∧
      LTL.Steps (LTL.Imported.program n).globalenv start trace finish ∧
      LTL.FinalState finish status) := by
  constructor
  · rintro ⟨start, finish, hinit, hrun, hfinal⟩
    obtain ⟨htrace, hstatus⟩ := RTL.Preallocation.maximal_execution n hlo hhi hinit hrun
      (fun _ _ => RTL.final_state_stuck hfinal)
    have hzero := RTL.final_state_unique hfinal hstatus
    simpa only [htrace, hzero, RTL.StoredPrograms.resultTrace, LTL.StoredPrograms.resultTrace]
      using LTL.StoredPrograms.execution n hlo hhi
  · rintro ⟨start, finish, hinit, hrun, hfinal⟩
    obtain ⟨htrace, hstatus⟩ := LTL.StoredPrograms.maximal_execution n hlo hhi hinit hrun
      (fun _ _ => LTL.final_state_stuck hfinal)
    have hzero := LTL.final_state_unique hfinal hstatus
    simpa only [htrace, hzero, RTL.StoredPrograms.resultTrace, LTL.StoredPrograms.resultTrace]
      using RTL.Preallocation.execution n hlo hhi

/-- The initial RTL and allocated programs have the same possible final observations. -/
theorem rtl_ltl_final_observations_iff [ExternalCalls]
    (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) (trace : Trace) (status : Integers.Int) :
    (∃ start finish, RTL.InitialState (RTL.Imported.program n) start ∧
      RTL.Steps (RTL.Imported.program n).globalenv start trace finish ∧
      RTL.FinalState finish status) ↔
    (∃ start finish, LTL.InitialState (LTL.Imported.program n) start ∧
      LTL.Steps (LTL.Imported.program n).globalenv start trace finish ∧
      LTL.FinalState finish status) :=
  (rtl_preallocation_final_observations_iff n hlo hhi trace status).trans
    (preallocation_ltl_final_observations_iff n hlo hhi trace status)

/-- The Clight source observations agree with the allocated LTL program. -/
theorem clight_ltl_final_observations_iff [calls : ExternalCalls]
    [ExternalCallsDeterministic calls]
    (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) (trace : Trace) (status : Integers.Int) :
    (∃ start memory, InitialState (Binary64.Clight.Application.program n) start ∧
      Star (Step2 (Binary64.Clight.Application.program n).globalenv) start trace
        (.Returnstate (.Vint status) .Kstop memory)) ↔
    (∃ start finish, LTL.InitialState (LTL.Imported.program n) start ∧
      LTL.Steps (LTL.Imported.program n).globalenv start trace finish ∧
      LTL.FinalState finish status) :=
  (clight_preallocation_final_observations_iff n hlo hhi trace status).trans
    (preallocation_ltl_final_observations_iff n hlo hhi trace status)

end Quadrature.Compiler
