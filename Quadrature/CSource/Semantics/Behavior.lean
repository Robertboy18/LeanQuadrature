import Quadrature.CSource.Semantics.TotalCorrectness

/-!
# Traces and results of complete C calls

`Steps` records the trace of a finite execution in the C small-step semantics.
`CallCorrect.outcome_iff` characterizes every possible return value and trace
of a totally correct call. `CallCorrect.maximal` also covers finite executions
that stop without initially being assumed to reach a return state.

Memory is related by `CallMemory`: every load and permission on a block that
existed before the call is preserved. C parameter and local blocks are fresh
allocations, so the final memory need not equal the initial memory.
-/

namespace Quadrature.CSource.C.SmallStep

open CC

variable [ExternalCalls]

/-- Finitely many C transitions, with the concatenation of their observable events. -/
inductive Steps (ge : GlobalEnv) : State → Trace → State → Prop where
  | refl (state) : Steps ge state E0 state
  | cons {start middle finish : State} {first rest : Trace} :
      Step ge start first middle → Steps ge middle rest finish →
      Steps ge start (Eapp first rest) finish

/-- Forgetting a finite execution's trace gives reachability. -/
theorem Steps.reachable {ge : GlobalEnv} {start finish : State} {trace : Trace}
    (h : Steps ge start trace finish) : Reachable ge start finish := by
  induction h with
  | refl => exact .refl
  | cons hstep _ ih => exact .head ⟨_, hstep⟩ ih

/-- A trace-free reachability proof has some corresponding trace. -/
theorem Reachable.steps {ge : GlobalEnv} {start finish : State}
    (h : Reachable ge start finish) : ∃ trace, Steps ge start trace finish := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨E0, .refl _⟩
  | head hstep _ ih =>
      obtain ⟨first, hfirst⟩ := hstep
      obtain ⟨rest, hrest⟩ := ih
      exact ⟨Eapp first rest, .cons hfirst hrest⟩

/-- Every finite prefix of a total computation is silent and retains total correctness. -/
theorem Total.of_steps {ge : GlobalEnv} {post : State → Prop} {start finish : State}
    {trace : Trace} (h : Total ge post start)
    (hterminal : ∀ state, post state → ∀ trace next, ¬ Step ge state trace next)
    (hpath : Steps ge start trace finish) :
    trace = E0 ∧ Total ge post finish := by
  induction hpath with
  | refl => exact ⟨rfl, h⟩
  | @cons start middle finish first rest hstep _ ih =>
      obtain ⟨hfirst, hnext⟩ :=
        h.next (fun hpost => hterminal start hpost first middle hstep) hstep
      obtain ⟨hrest, hlast⟩ := ih hnext
      exact ⟨by simp [hfirst, hrest, Eapp, E0], hlast⟩

/-- A completely returned call, with its trace, value and final memory. -/
def CallOutcome (ge : GlobalEnv) (initial : Mem) (function : FunDef)
    (args : List Val) (trace : Trace) (value : Val) (final : Mem) : Prop :=
  Steps ge (.call function args .stop initial) trace (.returned value .stop final)

/-- A totally correct call has a silent terminating execution. -/
theorem CallCorrect.terminates {ge : GlobalEnv} {initial : Mem} {function : FunDef}
    {args : List Val} {value : Val} (h : CallCorrect ge initial function args value) :
    ∃ final, CallOutcome ge initial function args E0 value final ∧ CallMemory initial final := by
  obtain ⟨finish, hpath, final, hfinal, hmemory⟩ := h.library.reaches
  change finish = .returned value .stop final at hfinal
  subst finish
  obtain ⟨trace, hsteps⟩ := hpath.steps
  have htrace := (h.library.of_steps
    (fun _ ⟨_, hfinal, _⟩ => hfinal.terminal) hsteps).1
  exact ⟨final, htrace ▸ hsteps, hmemory⟩

/-- Every finite maximal execution of a correct call returns its specified value silently. -/
theorem CallCorrect.maximal {ge : GlobalEnv} {initial : Mem} {function : FunDef}
    {args : List Val} {value : Val} (h : CallCorrect ge initial function args value)
    {state : State} {trace : Trace}
    (hpath : Steps ge (.call function args .stop initial) trace state)
    (hstop : ∀ emitted next, ¬ Step ge state emitted next) :
    trace = E0 ∧ ∃ final, state = .returned value .stop final ∧ CallMemory initial final := by
  obtain ⟨htrace, htotal⟩ :=
    h.library.of_steps (fun _ ⟨_, hfinal, _⟩ => hfinal.terminal) hpath
  refine ⟨htrace, ?_⟩
  cases htotal with
  | done hpost => exact hpost
  | step hprogress _ _ =>
      obtain ⟨emitted, next, hstep⟩ := hprogress
      exact (hstop emitted next hstep).elim

/-- Every returned value and trace agree with a correct call's specification. -/
theorem CallCorrect.outcome {ge : GlobalEnv} {initial : Mem} {function : FunDef}
    {args : List Val} {expected : Val} (h : CallCorrect ge initial function args expected)
    {trace : Trace} {value : Val} {final : Mem}
    (hpath : CallOutcome ge initial function args trace value final) :
    trace = E0 ∧ value = expected ∧ CallMemory initial final := by
  obtain ⟨htrace, memory, hstate, hmemory⟩ :=
    h.maximal hpath (returned_stop_terminal ge value final)
  cases hstate
  exact ⟨htrace, rfl, hmemory⟩

/-- The set of possible return observations is exactly the singleton specified by total
correctness. Existence is included, so the equivalence cannot hold vacuously for a stuck call. -/
theorem CallCorrect.outcome_iff {ge : GlobalEnv} {initial : Mem} {function : FunDef}
    {args : List Val} {expected : Val} (h : CallCorrect ge initial function args expected)
    (trace : Trace) (value : Val) :
    (∃ final, CallOutcome ge initial function args trace value final) ↔
      trace = E0 ∧ value = expected := by
  constructor
  · rintro ⟨final, hpath⟩
    exact ⟨(h.outcome hpath).1, (h.outcome hpath).2.1⟩
  · rintro ⟨rfl, rfl⟩
    obtain ⟨final, hpath, _⟩ := h.terminates
    exact ⟨final, hpath⟩

end Quadrature.CSource.C.SmallStep
