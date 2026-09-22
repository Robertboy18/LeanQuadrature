import Quadrature.CSource.Semantics.Behavior
import Quadrature.Clight.Internal

/-!
# Behavioral preservation for a C library call

`CallRefinement.outcomes_iff` equates all returned values and traces of a
C call and its Clight translation. The proof goes through their common
functional result. Its premises require total C correctness, a terminating
Clight execution and an internal Clight program; they cannot be satisfied
merely by comparing syntax or by assuming a call has already returned.

`source_accessible`, `target_accessible` and the progress theorems exclude
divergence and stuck intermediate states on both sides. `memory_agrees`
relates the returned memories on every block allocated before the call.
C allocates and frees local blocks; Clight uses temporaries, so equality
of their complete final memories would be the wrong specification.
-/

namespace Quadrature.CSource

open CC Binary64.Clight

variable [ExternalCalls]

/-- A C call and a closed Clight call are totally correct for the same result. This certificate
is sufficient for behavioral equivalence, including termination and preservation of old memory. -/
structure CallRefinement (source : C.GlobalEnv) (target : CC.Program) (memory : Mem)
    (sourceFunction : C.FunDef) (targetFunction : CC.FunDef) (args : List Val)
    (result : Val) : Prop where
  source_correct : C.SmallStep.CallCorrect source memory sourceFunction args result
  target_program : InternalProgram target
  target_internal : InternalState (.Callstate targetFunction args .Kstop memory)
  target_execution : StarE0 (Step2 target.globalenv) (.Callstate targetFunction args .Kstop memory)
    (.Returnstate result .Kstop memory)

namespace CallRefinement

variable {source : C.GlobalEnv} {target : CC.Program} {memory : Mem}
  {sourceFunction : C.FunDef} {targetFunction : CC.FunDef} {args : List Val} {result : Val}
  (h : CallRefinement source target memory sourceFunction targetFunction args result)

include h

/-- Every finite Clight execution is silent and can finish with the specified value and memory. -/
theorem target_prefix {trace : Trace} {state : CC.State}
    (hpath : Star (Step2 target.globalenv) (.Callstate targetFunction args .Kstop memory)
      trace state) :
    trace = E0 ∧ StarE0 (Step2 target.globalenv) state (.Returnstate result .Kstop memory) :=
  internal_execution_prefix target h.target_program h.target_internal h.target_execution
    (return_stop_no_step _ _ _) hpath

/-- Every maximal finite Clight execution reaches the specified return state. -/
theorem target_maximal {trace : Trace} {state : CC.State}
    (hpath : Star (Step2 target.globalenv) (.Callstate targetFunction args .Kstop memory)
      trace state)
    (hstop : ∀ emitted next, ¬ Step2 target.globalenv state emitted next) :
    trace = E0 ∧ state = .Returnstate result .Kstop memory := by
  obtain ⟨htrace, hremaining⟩ := h.target_prefix hpath
  exact ⟨htrace, starE0_of_stuck hremaining hstop⟩

/-- Any Clight return has the specified trace, value and unchanged memory. -/
theorem target_outcome {trace : Trace} {value : Val} {final : Mem}
    (hpath : Star (Step2 target.globalenv) (.Callstate targetFunction args .Kstop memory)
      trace (.Returnstate value .Kstop final)) :
    trace = E0 ∧ value = result ∧ final = memory := by
  obtain ⟨htrace, hstate⟩ := h.target_maximal hpath (return_stop_no_step _ _ _)
  cases hstate
  exact ⟨htrace, rfl, rfl⟩

/-- The normalized call has exactly one returned value and trace, and it does return. -/
theorem target_outcome_iff (trace : Trace) (value : Val) :
    (∃ final, Star (Step2 target.globalenv) (.Callstate targetFunction args .Kstop memory)
      trace (.Returnstate value .Kstop final)) ↔ trace = E0 ∧ value = result := by
  constructor
  · rintro ⟨final, hpath⟩
    exact ⟨(h.target_outcome hpath).1, (h.target_outcome hpath).2.1⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨memory, star_of_starE0 h.target_execution⟩

/-- C normalization preserves and reflects every returned value and event trace.
Both sets of outcomes are inhabited by the total-correctness certificates. -/
theorem outcomes_iff (trace : Trace) (value : Val) :
    (∃ final, C.SmallStep.CallOutcome source memory sourceFunction args trace value final) ↔
      ∃ final, Star (Step2 target.globalenv) (.Callstate targetFunction args .Kstop memory)
        trace (.Returnstate value .Kstop final) :=
  (h.source_correct.outcome_iff trace value).trans (h.target_outcome_iff trace value).symm

/-- Every C execution terminates, including all permitted operand evaluation orders. -/
theorem source_accessible :
    Acc (fun next state => ∃ trace, C.SmallStep.Step source state trace next)
      (.call sourceFunction args .stop memory) :=
  h.source_correct.accessible

/-- Every Clight execution terminates, for any external-call interpretation. -/
theorem target_accessible :
    Acc (fun next state => ∃ trace, Step2 target.globalenv state trace next)
      (.Callstate targetFunction args .Kstop memory) :=
  internal_execution_accessible target h.target_program h.target_internal h.target_execution
    (return_stop_no_step _ _ _)

/-- A reached C state has returned the specified value or can take another transition. -/
theorem source_progress {trace : Trace} {state : C.SmallStep.State}
    (hpath : C.SmallStep.Steps source (.call sourceFunction args .stop memory) trace state) :
    (∃ final, C.SmallStep.Final state result final ∧ C.CallMemory memory final) ∨
      ∃ emitted next, C.SmallStep.Step source state emitted next :=
  h.source_correct.progress hpath.reachable

/-- A reached Clight state has returned the specified value or can take another transition. -/
theorem target_progress {trace : Trace} {state : CC.State}
    (hpath : Star (Step2 target.globalenv) (.Callstate targetFunction args .Kstop memory)
      trace state) :
    state = .Returnstate result .Kstop memory ∨
      ∃ next, Step2 target.globalenv state E0 next := by
  cases (h.target_prefix hpath).2 with
  | refl => exact .inl rfl
  | step _ next _ hstep _ => exact .inr ⟨next, hstep⟩

/-- Any two returned memories agree on all pre-call loads and permissions. Only the C side
can have additional, freed local blocks. -/
theorem memory_agrees {sourceTrace targetTrace : Trace} {sourceValue targetValue : Val}
    {sourceMemory targetMemory : Mem}
    (hsource : C.SmallStep.CallOutcome source memory sourceFunction args
      sourceTrace sourceValue sourceMemory)
    (htarget : Star (Step2 target.globalenv) (.Callstate targetFunction args .Kstop memory)
      targetTrace (.Returnstate targetValue .Kstop targetMemory)) :
    C.CallMemory targetMemory sourceMemory := by
  rw [(h.target_outcome htarget).2.2]
  exact (h.source_correct.outcome hsource).2.2

end CallRefinement

end Quadrature.CSource
