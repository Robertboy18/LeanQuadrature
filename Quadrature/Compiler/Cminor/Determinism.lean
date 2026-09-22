import Quadrature.Compiler.Cminor.ProgramExecution

/-!
# Uniqueness and termination of checked Cminor executions

For any executor `external` satisfying `ExternalExecutorAgrees`, a successful
`executeStep` fixes the trace and successor of every `Step` from that state
(`execute_step_agrees`). A checked run ending in a stuck state is therefore the only
maximal execution (`execute_steps_unique`) and excludes every infinite execution
(`execute_steps_not_infinite`). The annotation executor is one instance,
`annotated_external_executor_agrees`.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Cminor

open CC

variable [ExternalCalls]

/-- Specialization of `Execution.ExternalExecutorAgrees` to this stage's `Genv`. -/
def ExternalExecutorAgrees (external : ExternalExecutor) (ge : Genv) : Prop :=
  Execution.ExternalExecutorAgrees external ge.toSenv

/-- CLean's `CC.doExternalCall` agrees with `externalCall` for this stage's `Genv`. -/
theorem default_external_executor_agrees {ge : Genv} :
    ExternalExecutorAgrees CC.doExternalCall ge :=
  Execution.default_external_executor_agrees

/-- The annotation executor `annotatedExternalCall` agrees with `externalCall` for this stage's
`Genv`. -/
theorem annotated_external_executor_agrees {ge : Genv} :
    ExternalExecutorAgrees annotatedExternalCall ge :=
  Cminor.annotated_external_call_agrees

variable {external : ExternalExecutor} {ge : Genv}

/-- If `executeStep external ge s` returns `some (t, s')` and `external` agrees, every `Step` from
`s` has trace `t` and successor `s'`. -/
theorem execute_step_agrees (hexternal : ExternalExecutorAgrees external ge)
    {start finish other : State} {trace otherTrace : Trace}
    (h : executeStep external ge start = some (trace, finish))
    (hother : Step ge start otherTrace other) : trace = otherTrace ∧ finish = other := by
  cases hother with
  | skip_seq | skip_block | seq | loop | block | exit_seq | exit_block_zero
  | exit_block_succ | label | return_to_caller =>
      simpa only [executeStep, Option.some.injEq, Prod.mk.injEq] using h.symm
  | skip_call f k sp env memory memory' hcall hfree =>
      cases k <;> simp only [IsCallCont] at hcall
      · simpa [executeStep, freeStack, hfree] using h.symm
      · simpa [executeStep, freeStack, hfree] using h.symm
  | assign f name a k sp env memory value hvalue =>
      simpa [executeStep, eval_expr_complete hvalue] using h.symm
  | store f chunk address a k sp env memory pointer value memory' hp hv hm =>
      simpa [executeStep, eval_expr_complete hp, eval_expr_complete hv, hm] using h.symm
  | call f result signature a args k sp env memory vf values fd hf hv hfd hsig =>
      simpa [executeStep, eval_expr_complete hf, eval_expr_list_complete hv, hfd, hsig]
        using h.symm
  | tailcall f signature a args k sp env memory vf values fd memory' hf hv hfd hsig hm =>
      simpa [executeStep, eval_expr_complete hf, eval_expr_list_complete hv,
        hfd, hsig, freeStack, hm] using h.symm
  | builtin f result ef args k sp env memory values emitted value memory' hv hext =>
      simp only [executeStep, eval_expr_list_complete hv, bind, Option.bind_some,
        Option.bind_eq_some_iff] at h
      obtain ⟨⟨checkedTrace, checkedValue, checkedMemory⟩, hchecked, h⟩ := h
      cases h
      obtain ⟨rfl, rfl, rfl⟩ := hexternal _ _ _ _ _ _ _ _ _ hchecked hext
      exact ⟨rfl, rfl⟩
  | branch f condition yes no k sp env memory value result hv hb =>
      simpa [executeStep, eval_expr_complete hv, bool_of_val_iff.mpr hb] using h.symm
  | switch f isLong a cases fallback k sp env memory value key hv hk =>
      simpa [executeStep, eval_expr_complete hv, switch_argument_iff.mpr hk] using h.symm
  | return_none f k sp env memory memory' hm =>
      simpa [executeStep, freeStack, hm] using h.symm
  | return_some f a k sp env memory value memory' hv hm =>
      simpa [executeStep, eval_expr_complete hv, freeStack, hm] using h.symm
  | goto f name k sp env memory body rest hlabel =>
      simpa [executeStep, hlabel] using h.symm
  | internal_function f values k memory memory' sp env htypes halloc henv =>
      simpa [executeStep, htypes, halloc, henv] using h.symm
  | external_function ef values k memory emitted value memory' hext =>
      simp only [executeStep, bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨checkedTrace, checkedValue, checkedMemory⟩, hchecked, h⟩ := h
      cases h
      obtain ⟨rfl, rfl, rfl⟩ := hexternal _ _ _ _ _ _ _ _ _ hchecked hext
      exact ⟨rfl, rfl⟩

/-- If a checked run from `s` ends in a stuck state, every `Steps` run from `s` is a prefix of it
and the checker completes the remainder with the remaining fuel. -/
theorem execute_steps_prefix (hexternal : ExternalExecutorAgrees external ge)
    {fuel : Nat} {start finish state : State} {total trace : Trace}
    (hcheck : executeSteps external ge fuel start = some (total, finish))
    (hstop : ∀ emitted next, ¬ Step ge finish emitted next)
    (hprefix : Steps ge start trace state) :
    ∃ remainingFuel remaining, remainingFuel ≤ fuel ∧ trace ++ remaining = total ∧
      executeSteps external ge remainingFuel state = some (remaining, finish) := by
  apply Execution.run_prefix (execute_step_agrees hexternal) ?_ hcheck hstop hprefix
  intro first last emitted h
  cases h with
  | refl => exact Or.inl ⟨rfl, rfl⟩
  | cons hstep hsuffix => exact Or.inr ⟨_, _, _, hstep, hsuffix, rfl⟩

/-- If a checked run from `s` ends in a stuck state, every maximal `Steps` run from `s` has the
checked trace and final state. -/
theorem execute_steps_unique (hsound : ExternalExecutorSound external ge)
    (hagrees : ExternalExecutorAgrees external ge)
    {fuel : Nat} {start finish state : State} {total trace : Trace}
    (hcheck : executeSteps external ge fuel start = some (total, finish))
    (hstop : ∀ emitted next, ¬ Step ge finish emitted next)
    (hprefix : Steps ge start trace state)
    (hotherStop : ∀ emitted next, ¬ Step ge state emitted next) :
    trace = total ∧ state = finish := by
  obtain ⟨_, _, _, htrace, hremaining⟩ := execute_steps_prefix hagrees hcheck hstop hprefix
  have hsuffix := execute_steps_sound hsound hremaining
  cases hsuffix with
  | refl => exact ⟨by simpa using htrace, rfl⟩
  | cons h _ => exact False.elim (hotherStop _ _ h)

/-- If a checked run from `s` ends in a stuck state, no infinite sequence of `Step` transitions
starts at `s`. -/
theorem execute_steps_not_infinite (hexternal : ExternalExecutorAgrees external ge)
    {fuel : Nat} {start finish : State} {total : Trace}
    (hcheck : executeSteps external ge fuel start = some (total, finish))
    (hstop : ∀ emitted next, ¬ Step ge finish emitted next)
    (states : Nat → State) (traces : Nat → Trace) (hstart : states 0 = start)
    (hsteps : ∀ n, Step ge (states n) (traces n) (states (n + 1))) : False := by
  rw [execute_steps_eq_run] at hcheck
  exact Execution.run_not_infinite (Step := Step ge)
    (fun hstep hother => (execute_step_agrees hexternal hstep hother).2)
    hcheck hstop states traces hstart hsteps

omit [ExternalCalls] in
/-- If `InitialState program s` holds, then `initialState program` returns `some s`. -/
theorem initial_state_complete {program : Program} {state : State}
    (h : InitialState program state) : initialState program = some state := by
  cases h with
  | intro block function memory hmemory hblock hfunction hsignature =>
      simp [initialState, hmemory, hblock, hfunction, hsignature]

omit [ExternalCalls] in
/-- A program has at most one initial state. -/
theorem initial_state_unique {program : Program} {state other : State}
    (h : InitialState program state) (hother : InitialState program other) : state = other :=
  Option.some.inj ((initial_state_complete h).symm.trans (initial_state_complete hother))

omit [ExternalCalls] in
/-- A final state has exactly one exit status. -/
theorem final_state_unique {state : State} {status other : Integers.Int}
    (h : FinalState state status) (hother : FinalState state other) : status = other := by
  cases h
  cases hother
  rfl

omit [ExternalCalls] in
/-- If `executeProgram` succeeds, its initial state, its checked `executeSteps` run, and its final
state are recoverable. -/
theorem execute_program_checked_run {program : Program} {fuel : Nat}
    {trace : Trace} {status : Integers.Int}
    (h : executeProgram external program fuel = some (trace, status)) :
    ∃ start finish, InitialState program start ∧
      executeSteps external program.globalenv fuel start = some (trace, finish) ∧
      FinalState finish status := by
  simp only [executeProgram, bind, Option.bind_eq_some_iff] at h
  obtain ⟨start, hstart, ⟨events, finish⟩, hrun, result, hfinish, h⟩ := h
  cases h
  exact ⟨start, finish, initial_state_sound hstart, hrun, exit_status_sound hfinish⟩

/-- If `executeProgram` certifies the observation `(total, status)`, every `Steps` run from an
initial state extends to a final state with that observation. -/
theorem execute_program_prefix {program : Program} {fuel : Nat}
    {total trace : Trace} {status : Integers.Int} {start state : State}
    (hsound : ExternalExecutorSound external program.globalenv)
    (hagrees : ExternalExecutorAgrees external program.globalenv)
    (hcheck : executeProgram external program fuel = some (total, status))
    (hinit : InitialState program start) (hrun : Steps program.globalenv start trace state) :
    ∃ remaining finish, trace ++ remaining = total ∧
      Steps program.globalenv state remaining finish ∧ FinalState finish status := by
  obtain ⟨checkedStart, finish, hcheckedInit, hcheckedRun, hfinal⟩ :=
    execute_program_checked_run hcheck
  obtain rfl := initial_state_unique hcheckedInit hinit
  obtain ⟨_, remaining, _, htrace, hremaining⟩ :=
    execute_steps_prefix hagrees hcheckedRun (fun _ _ => final_state_stuck hfinal) hrun
  exact ⟨remaining, finish, htrace, execute_steps_sound hsound hremaining, hfinal⟩

/-- If `executeProgram` certifies `status`, every reachable state is final with `status` or admits
a further `Step`. -/
theorem execute_program_progress {program : Program} {fuel : Nat}
    {total trace : Trace} {status : Integers.Int} {start state : State}
    (hsound : ExternalExecutorSound external program.globalenv)
    (hagrees : ExternalExecutorAgrees external program.globalenv)
    (hcheck : executeProgram external program fuel = some (total, status))
    (hinit : InitialState program start) (hrun : Steps program.globalenv start trace state) :
    FinalState state status ∨ ∃ emitted next, Step program.globalenv state emitted next := by
  obtain ⟨_, _, _, hsuffix, hfinal⟩ := execute_program_prefix hsound hagrees hcheck hinit hrun
  cases hsuffix with
  | refl => exact Or.inl hfinal
  | cons h _ => exact Or.inr ⟨_, _, h⟩

/-- If `executeProgram` certifies `(total, status)`, every maximal `Steps` run from an initial
state has trace `total` and ends in a final state with `status`. -/
theorem execute_program_unique {program : Program} {fuel : Nat}
    {total trace : Trace} {status : Integers.Int} {start state : State}
    (hsound : ExternalExecutorSound external program.globalenv)
    (hagrees : ExternalExecutorAgrees external program.globalenv)
    (hcheck : executeProgram external program fuel = some (total, status))
    (hinit : InitialState program start) (hrun : Steps program.globalenv start trace state)
    (hstop : ∀ emitted next, ¬ Step program.globalenv state emitted next) :
    trace = total ∧ FinalState state status := by
  obtain ⟨_, _, htrace, hsuffix, hfinal⟩ :=
    execute_program_prefix hsound hagrees hcheck hinit hrun
  cases hsuffix with
  | refl => exact ⟨by simpa using htrace, hfinal⟩
  | cons h _ => exact False.elim (hstop _ _ h)

/-- If `executeProgram` succeeds, no infinite sequence of `Step` transitions starts at an initial
state. -/
theorem execute_program_not_infinite {program : Program} {fuel : Nat}
    {total : Trace} {status : Integers.Int} {start : State}
    (hagrees : ExternalExecutorAgrees external program.globalenv)
    (hcheck : executeProgram external program fuel = some (total, status))
    (hinit : InitialState program start)
    (states : Nat → State) (traces : Nat → Trace) (hstart : states 0 = start)
    (hsteps : ∀ n, Step program.globalenv (states n) (traces n) (states (n + 1))) : False := by
  obtain ⟨checkedStart, finish, hcheckedInit, hcheckedRun, hfinal⟩ :=
    execute_program_checked_run hcheck
  obtain rfl := initial_state_unique hcheckedInit hinit
  exact execute_steps_not_infinite hagrees hcheckedRun
    (fun _ _ => final_state_stuck hfinal) states traces hstart hsteps

end Quadrature.Cminor
