import Quadrature.Compiler.Correspondence.RTLPrograms
import Quadrature.Compiler.RTL.PreallocationPrograms

/-!
# Application observations across the configured RTL passes

Relates the initial RTL programs and the RTL programs just before register allocation, for
n = 1..10, by their observations (event trace, exit status). Read
`rtl_preallocation_final_observations_iff` first: both programs have exactly the observation
`resultTrace (result n)` with exit status 0, because each side's total correctness theorems
exclude every other outcome. `clight_preallocation_final_observations_iff` composes the
chain from Clight under `ExternalCallsDeterministic`.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Compiler

open CC

/-- The RTL passes preserve the possible final observations of all ten applications. -/
theorem rtl_preallocation_final_observations_iff [ExternalCalls]
    (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) (trace : Trace) (status : Integers.Int) :
    (∃ start finish, RTL.InitialState (RTL.Imported.program n) start ∧
      RTL.Steps (RTL.Imported.program n).globalenv start trace finish ∧
      RTL.FinalState finish status) ↔
    (∃ start finish, RTL.InitialState (RTL.Preallocation.program n) start ∧
      RTL.Steps (RTL.Preallocation.program n).globalenv start trace finish ∧
      RTL.FinalState finish status) := by
  constructor
  · rintro ⟨start, finish, hinit, hrun, hfinal⟩
    obtain ⟨htrace, hstatus⟩ := RTL.StoredPrograms.maximal_execution n hlo hhi hinit hrun
      (fun _ _ => RTL.final_state_stuck hfinal)
    have hzero := RTL.final_state_unique hfinal hstatus
    simpa only [htrace, hzero, RTL.StoredPrograms.resultTrace] using
      RTL.Preallocation.execution n hlo hhi
  · rintro ⟨start, finish, hinit, hrun, hfinal⟩
    obtain ⟨htrace, hstatus⟩ := RTL.Preallocation.maximal_execution n hlo hhi hinit hrun
      (fun _ _ => RTL.final_state_stuck hfinal)
    have hzero := RTL.final_state_unique hfinal hstatus
    simpa only [htrace, hzero, RTL.StoredPrograms.resultTrace] using
      RTL.StoredPrograms.execution n hlo hhi

/-- The source observations agree with the program immediately before allocation. -/
theorem clight_preallocation_final_observations_iff [calls : ExternalCalls]
    [ExternalCallsDeterministic calls]
    (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) (trace : Trace) (status : Integers.Int) :
    (∃ start memory, InitialState (Binary64.Clight.Application.program n) start ∧
      Star (Step2 (Binary64.Clight.Application.program n).globalenv) start trace
        (.Returnstate (.Vint status) .Kstop memory)) ↔
    (∃ start finish, RTL.InitialState (RTL.Preallocation.program n) start ∧
      RTL.Steps (RTL.Preallocation.program n).globalenv start trace finish ∧
      RTL.FinalState finish status) :=
  (clight_rtl_final_observations_iff n hlo hhi trace status).trans
    (rtl_preallocation_final_observations_iff n hlo hhi trace status)

end Quadrature.Compiler
