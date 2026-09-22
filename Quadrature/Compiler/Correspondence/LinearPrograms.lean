import Quadrature.Compiler.Correspondence.LTLPrograms
import Quadrature.Compiler.Linear.StoredTotalCorrectness

/-!
# Application observations through linearization

Relates the LTL and Linear programs for n = 1..10 by their observations (event trace, exit
status). Read `ltl_linear_final_observations_iff` first: both programs have exactly the
observation `resultTrace (result n)` with exit status 0, because each side's total
correctness theorems exclude every other outcome. The remaining theorems compose the chain
from the initial RTL programs and from Clight under `ExternalCallsDeterministic`.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Compiler

open CC

/-- The allocated and linearized applications have the same final observations. -/
theorem ltl_linear_final_observations_iff [ExternalCalls]
    (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) (trace : Trace) (status : Integers.Int) :
    (∃ start finish, LTL.InitialState (LTL.Imported.program n) start ∧
      LTL.Steps (LTL.Imported.program n).globalenv start trace finish ∧
      LTL.FinalState finish status) ↔
    (∃ start finish, Linear.InitialState (Linear.Imported.program n) start ∧
      Linear.Steps (Linear.Imported.program n).globalenv start trace finish ∧
      Linear.FinalState finish status) := by
  constructor
  · rintro ⟨start, finish, hinit, hrun, hfinal⟩
    obtain ⟨htrace, hstatus⟩ := LTL.StoredPrograms.maximal_execution n hlo hhi hinit hrun
      (fun _ _ => LTL.final_state_stuck hfinal)
    have hzero := LTL.final_state_unique hfinal hstatus
    simpa only [htrace, hzero, LTL.StoredPrograms.resultTrace, Linear.StoredPrograms.resultTrace]
      using Linear.StoredPrograms.execution n hlo hhi
  · rintro ⟨start, finish, hinit, hrun, hfinal⟩
    obtain ⟨htrace, hstatus⟩ := Linear.StoredPrograms.maximal_execution n hlo hhi hinit hrun
      (fun _ _ => Linear.final_state_stuck hfinal)
    have hzero := Linear.final_state_unique hfinal hstatus
    simpa only [htrace, hzero, LTL.StoredPrograms.resultTrace, Linear.StoredPrograms.resultTrace]
      using LTL.StoredPrograms.execution n hlo hhi

/-- The initial RTL and Linear applications have the same final observations. -/
theorem rtl_linear_final_observations_iff [ExternalCalls]
    (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) (trace : Trace) (status : Integers.Int) :
    (∃ start finish, RTL.InitialState (RTL.Imported.program n) start ∧
      RTL.Steps (RTL.Imported.program n).globalenv start trace finish ∧
      RTL.FinalState finish status) ↔
    (∃ start finish, Linear.InitialState (Linear.Imported.program n) start ∧
      Linear.Steps (Linear.Imported.program n).globalenv start trace finish ∧
      Linear.FinalState finish status) :=
  (rtl_ltl_final_observations_iff n hlo hhi trace status).trans
    (ltl_linear_final_observations_iff n hlo hhi trace status)

/-- The Clight observations agree with the Linear program before stack layout. -/
theorem clight_linear_final_observations_iff [calls : ExternalCalls]
    [ExternalCallsDeterministic calls]
    (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) (trace : Trace) (status : Integers.Int) :
    (∃ start memory, InitialState (Binary64.Clight.Application.program n) start ∧
      Star (Step2 (Binary64.Clight.Application.program n).globalenv) start trace
        (.Returnstate (.Vint status) .Kstop memory)) ↔
    (∃ start finish, Linear.InitialState (Linear.Imported.program n) start ∧
      Linear.Steps (Linear.Imported.program n).globalenv start trace finish ∧
      Linear.FinalState finish status) :=
  (clight_ltl_final_observations_iff n hlo hhi trace status).trans
    (ltl_linear_final_observations_iff n hlo hhi trace status)

end Quadrature.Compiler
