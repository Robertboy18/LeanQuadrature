import Quadrature.CSource.Semantics.SmallStep
import Quadrature.CSource.Semantics.CallMemory

/-!
# Total correctness for the C machine

`Total ge post initial` requires every permitted transition to make progress
toward `post`, with no observable event. Its inductive definition excludes
infinite executions; its progress premise excludes stuck executions.

The postcondition may describe an intermediate state, which allows sequential
composition. `Total.accessible` gives termination of the complete transition
relation when the postcondition consists of terminal states.
-/

namespace Quadrature.CSource.C.SmallStep

open CC

variable [ExternalCalls]

/-- Every evaluation order reaches `post` after finitely many silent steps. -/
inductive Total (ge : GlobalEnv) (post : State → Prop) : State → Prop where
  | done {state} : post state → Total ge post state
  | step {state} :
      (∃ trace next, Step ge state trace next) →
      (∀ trace next, Step ge state trace next → trace = E0) →
      (∀ trace next, Step ge state trace next → Total ge post next) →
      Total ge post state

/-- Compose two total-correctness arguments at their shared intermediate postcondition. -/
theorem Total.bind {ge : GlobalEnv} {first last : State → Prop} {state : State}
    (hfirst : Total ge first state)
    (hlast : ∀ middle, first middle → Total ge last middle) :
    Total ge last state := by
  induction hfirst with
  | done h => exact hlast _ h
  | step hprogress hsilent _ ih =>
      exact .step hprogress hsilent ih

/-- Weaken the postcondition of a total computation. -/
theorem Total.mono {ge : GlobalEnv} {first last : State → Prop} {state : State}
    (hfirst : Total ge first state) (hpost : ∀ result, first result → last result) :
    Total ge last state :=
  hfirst.bind fun result h => .done (hpost result h)

/-- Prepend a uniquely determined silent step to a total computation. -/
theorem Total.single {ge : GlobalEnv} {post : State → Prop} {state next : State}
    (hstep : Step ge state E0 next)
    (hunique : ∀ trace result, Step ge state trace result → trace = E0 ∧ result = next)
    (hnext : Total ge post next) :
    Total ge post state :=
  .step ⟨E0, next, hstep⟩ (fun trace result h => (hunique trace result h).1)
    (fun trace result h => (hunique trace result h).2.symm ▸ hnext)

/-- Resume a suspended expression after a function returns. -/
theorem Total.resume {ge : GlobalEnv} {post : State → Prop} {value : Val}
    {function : Function} {locals : Env} {context : Expr → Expr} {type : Ty}
    {cont : Cont} {memory : Mem}
    (hnext : Total ge post
      (.expression function (context (.Eval value type)) cont locals memory)) :
    Total ge post (.returned value (.call function locals context type cont) memory) := by
  apply Total.single (.inr (.resume _ _ _ _ _ _ _)) ?_ hnext
  intro trace result hstep
  rcases hstep with hstep | hstep <;> cases hstep
  exact ⟨rfl, rfl⟩

/-- Away from the postcondition, a total computation has a successor. -/
theorem Total.progress {ge : GlobalEnv} {post : State → Prop} {state : State}
    (h : Total ge post state) (hpost : ¬ post state) :
    ∃ trace next, Step ge state trace next := by
  cases h with
  | done h => exact False.elim (hpost h)
  | step hprogress _ _ => exact hprogress

/-- Each transition before the postcondition is silent and retains total correctness. -/
theorem Total.next {ge : GlobalEnv} {post : State → Prop} {state next : State} {trace : Trace}
    (h : Total ge post state) (hpost : ¬ post state) (hstep : Step ge state trace next) :
    trace = E0 ∧ Total ge post next := by
  cases h with
  | done h => exact False.elim (hpost h)
  | step _ hsilent hsteps => exact ⟨hsilent trace next hstep, hsteps trace next hstep⟩

/-- If every postcondition state is terminal, no execution from a total state is infinite. -/
theorem Total.accessible {ge : GlobalEnv} {post : State → Prop} {state : State}
    (h : Total ge post state)
    (hterminal : ∀ state, post state → ∀ trace next, ¬ Step ge state trace next) :
    Acc (fun next state => ∃ trace, Step ge state trace next) state := by
  induction h with
  | done h =>
      exact .intro _ (fun next ⟨trace, hstep⟩ =>
        False.elim (hterminal _ h trace next hstep))
  | step _ _ _ ih =>
      exact .intro _ (fun next ⟨trace, hstep⟩ => ih trace next hstep)

/-- A state reachable by finitely many C transitions, without fixing their operand order. -/
def Reachable (ge : GlobalEnv) (initial final : State) : Prop :=
  Relation.ReflTransGen (fun state next => ∃ trace, Step ge state trace next) initial final

/-- Total correctness persists at every reachable state when the postcondition is terminal. -/
theorem Total.of_reachable {ge : GlobalEnv} {post : State → Prop} {initial final : State}
    (h : Total ge post initial)
    (hterminal : ∀ state, post state → ∀ trace next, ¬ Step ge state trace next)
    (hpath : Reachable ge initial final) :
    Total ge post final := by
  induction hpath with
  | refl => exact h
  | @tail middle last _ hstep ih =>
      obtain ⟨trace, hstep⟩ := hstep
      exact (ih.next (fun hpost => hterminal middle hpost trace last hstep) hstep).2

/-- A total computation has a finite execution reaching its postcondition. -/
theorem Total.reaches {ge : GlobalEnv} {post : State → Prop} {initial : State}
    (h : Total ge post initial) :
    ∃ final, Reachable ge initial final ∧ post final := by
  induction h with
  | done h => exact ⟨_, .refl, h⟩
  | step hprogress _ _ ih =>
      obtain ⟨trace, next, hstep⟩ := hprogress
      obtain ⟨final, hpath, hpost⟩ := ih trace next hstep
      exact ⟨final, .head ⟨trace, hstep⟩ hpath, hpost⟩

/-- A fully returned library call has no successor. -/
theorem returned_stop_terminal (ge : GlobalEnv) (value : Val) (memory : Mem)
    (trace : Trace) (next : State) :
    ¬ Step ge (.returned value .stop memory) trace next := by
  rintro (h | h) <;> cases h

/-- A final library state cannot take another transition. -/
theorem Final.terminal {ge : GlobalEnv} {state : State} {value : Val} {memory : Mem}
    (h : Final state value memory) (trace : Trace) (next : State) :
    ¬ Step ge state trace next := by
  change state = .returned value .stop memory at h
  subst state
  exact returned_stop_terminal ge value memory trace next

/-- A function returns `value` in every evaluation order and preserves its caller's memory.
The statement is uniform in the caller continuation. -/
def CallCorrect (ge : GlobalEnv) (initial : Mem) (function : FunDef)
    (args : List Val) (value : Val) : Prop :=
  ∀ next : Cont, next.IsCall →
    Total ge (fun state => ∃ final, state = .returned value next final ∧
      CallMemory initial final) (.call function args next initial)

/-- A library call starts with the empty continuation. -/
theorem CallCorrect.library {ge : GlobalEnv} {initial : Mem} {function : FunDef}
    {args : List Val} {value : Val} (h : CallCorrect ge initial function args value) :
    Total ge (fun state => ∃ final, Final state value final ∧ CallMemory initial final)
      (.call function args .stop initial) :=
  h .stop trivial

/-- No infinite C execution starts from a correctly specified library call. -/
theorem CallCorrect.accessible {ge : GlobalEnv} {initial : Mem} {function : FunDef}
    {args : List Val} {value : Val} (h : CallCorrect ge initial function args value) :
    Acc (fun next state => ∃ trace, Step ge state trace next)
      (.call function args .stop initial) :=
  h.library.accessible fun _ ⟨_, hfinal, _⟩ => hfinal.terminal

/-- Every reachable state of a correct library call either has the specified final result
and preserved memory or can take another C transition. -/
theorem CallCorrect.progress {ge : GlobalEnv} {initial : Mem} {function : FunDef}
    {args : List Val} {value : Val} (h : CallCorrect ge initial function args value)
    {state : State} (hpath : Reachable ge (.call function args .stop initial) state) :
    (∃ final, Final state value final ∧ CallMemory initial final) ∨
      ∃ trace next, Step ge state trace next := by
  classical
  have hstate := h.library.of_reachable
    (fun _ ⟨_, hfinal, _⟩ => hfinal.terminal) hpath
  by_cases hfinal : ∃ final, Final state value final ∧ CallMemory initial final
  · exact .inl hfinal
  · exact .inr (hstate.progress hfinal)

end Quadrature.CSource.C.SmallStep
