import Quadrature.Compiler.Asm.ProgramExecution

/-!
# Uniqueness of checked assembly executions

Agreement results for the assembly checker. Read `execute_step_agrees` first: when the
external executor agrees with the external-call relation, a successful `executeStep`
fixes every semantic successor and its trace, because `execInstr` is a function. A
checked terminating run therefore excludes both a different maximal finite result and
an infinite execution.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Asm

open CC

variable [ExternalCalls]

/-- Successful external checks determine every permitted result for those arguments. -/
def ExternalExecutorAgrees (external : ExternalExecutor) (ge : Genv) : Prop :=
  Execution.ExternalExecutorAgrees external ge.toSenv

/-- CLean's builtin executor agrees with the external-call relation. -/
theorem default_external_executor_agrees {ge : Genv} :
    ExternalExecutorAgrees CC.doExternalCall ge :=
  Execution.default_external_executor_agrees

/-- Numeric annotations require no contract on unknown functions or symbol aliases. -/
theorem annotated_external_executor_agrees {ge : Genv} :
    ExternalExecutorAgrees annotatedExternalCall ge :=
  Cminor.annotated_external_call_agrees

variable {external : ExternalExecutor} {ge : Genv}

omit [ExternalCalls] in
/-- A non-builtin instruction executed by `execInstr` (`h`) is executed by `executeInstruction`
with the empty trace. -/
theorem execute_instruction_of_internal {function : Function} {instruction : Instruction}
    {registers : Regset} {memory : Mem} {next : State}
    (h : execInstr ge function instruction registers memory = some next) :
    executeInstruction external ge function instruction registers memory = some (E0, next) := by
  unfold executeInstruction
  split
  · simp [execInstr] at h
  · simp [h]

/-- A successful check fixes every relational successor and its exact trace. -/
theorem execute_step_agrees (hexternal : ExternalExecutorAgrees external ge)
    {start finish other : State} {trace otherTrace : Trace}
    (h : executeStep external ge start = some (trace, finish))
    (hother : Step ge start otherTrace other) :
    trace = otherTrace ∧ finish = other := by
  cases hother with
  | internal block offset function instruction registers memory next hpc hf hi hexec =>
      simpa [executeStep, hpc, hf, hi, execute_instruction_of_internal hexec] using h.symm
  | builtin block offset function ef args result registers memory values events value memory'
      hpc hf hi hargs hext =>
      simp only [executeStep, hpc, hf, hi, executeInstruction, eval_builtin_args_complete hargs,
        bind, Option.bind_some, Option.bind_eq_some_iff] at h
      obtain ⟨⟨checkedTrace, checkedValue, checkedMemory⟩, hchecked, h⟩ := h
      cases h
      obtain ⟨rfl, rfl, rfl⟩ := hexternal _ _ _ _ _ _ _ _ _ hchecked hext
      exact ⟨rfl, rfl⟩
  | external block ef registers memory args events value memory' hpc hf hargs hext =>
      simp only [executeStep, hpc, hf, external_args_iff.mp hargs, bind,
        Option.bind_some, ↓reduceIte, Option.bind_eq_some_iff] at h
      obtain ⟨⟨checkedTrace, checkedValue, checkedMemory⟩, hchecked, h⟩ := h
      cases h
      obtain ⟨rfl, rfl, rfl⟩ := hexternal _ _ _ _ _ _ _ _ _ hchecked hext
      exact ⟨rfl, rfl⟩

/-- Every semantic prefix of a checked terminating run has a checked suffix. -/
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

/-- A maximal finite execution has exactly the checked trace and final state. -/
theorem execute_steps_unique (hsound : ExternalExecutorSound external ge)
    (hagrees : ExternalExecutorAgrees external ge)
    {fuel : Nat} {start finish state : State} {total trace : Trace}
    (hcheck : executeSteps external ge fuel start = some (total, finish))
    (hstop : ∀ emitted next, ¬ Step ge finish emitted next)
    (hprefix : Steps ge start trace state)
    (hotherStop : ∀ emitted next, ¬ Step ge state emitted next) :
    trace = total ∧ state = finish := by
  obtain ⟨_, _, _, htrace, hremaining⟩ :=
    execute_steps_prefix hagrees hcheck hstop hprefix
  have hsuffix := execute_steps_sound hsound hremaining
  cases hsuffix with
  | refl => exact ⟨by simpa using htrace, rfl⟩
  | cons h _ => exact False.elim (hotherStop _ _ h)

/-- No infinite semantic execution can share the start of a checked terminating run. -/
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
/-- A program has at most one initial state. -/
theorem initial_state_unique {program : Program} {state other : State}
    (h : InitialState program state) (hother : InitialState program other) : state = other :=
  Option.some.inj ((initial_state_complete h).symm.trans (initial_state_complete hother))

omit [ExternalCalls] in
/-- A final state has exactly one exit status. -/
theorem final_state_unique {state : State} {status other : Integers.Int}
    (h : FinalState state status) (hother : FinalState state other) : status = other :=
  Option.some.inj ((exit_status_complete h).symm.trans (exit_status_complete hother))

omit [ExternalCalls] in
/-- Unpacks a whole-program certificate into an initial state, the checked `executeSteps` run
itself, and a final state. -/
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

/-- Any execution from any initial state can finish with the certified observation. -/
theorem execute_program_prefix {program : Program} {fuel : Nat}
    {total trace : Trace} {status : Integers.Int} {start state : State}
    (hsound : ExternalExecutorSound external program.globalenv)
    (hagrees : ExternalExecutorAgrees external program.globalenv)
    (hcheck : executeProgram external program fuel = some (total, status))
    (hinit : InitialState program start)
    (hrun : Steps program.globalenv start trace state) :
    ∃ remaining finish, trace ++ remaining = total ∧
      Steps program.globalenv state remaining finish ∧
      FinalState finish status := by
  obtain ⟨checkedStart, finish, hcheckedInit, hcheckedRun, hfinal⟩ :=
    execute_program_checked_run hcheck
  obtain rfl := initial_state_unique hcheckedInit hinit
  obtain ⟨_, remaining, _, htrace, hremaining⟩ :=
    execute_steps_prefix hagrees hcheckedRun
      (fun _ _ => final_state_stuck hfinal) hrun
  exact ⟨remaining, finish, htrace, execute_steps_sound hsound hremaining, hfinal⟩

/-- Every reachable state is final with the certified status or admits another step. -/
theorem execute_program_progress {program : Program} {fuel : Nat}
    {total trace : Trace} {status : Integers.Int} {start state : State}
    (hsound : ExternalExecutorSound external program.globalenv)
    (hagrees : ExternalExecutorAgrees external program.globalenv)
    (hcheck : executeProgram external program fuel = some (total, status))
    (hinit : InitialState program start)
    (hrun : Steps program.globalenv start trace state) :
    FinalState state status ∨
      ∃ emitted next, Step program.globalenv state emitted next := by
  obtain ⟨_, _, _, hsuffix, hfinal⟩ :=
    execute_program_prefix hsound hagrees hcheck hinit hrun
  cases hsuffix with
  | refl => exact Or.inl hfinal
  | cons h _ => exact Or.inr ⟨_, _, h⟩

/-- Every maximal finite execution has the certified trace and exit status. -/
theorem execute_program_unique {program : Program} {fuel : Nat}
    {total trace : Trace} {status : Integers.Int} {start state : State}
    (hsound : ExternalExecutorSound external program.globalenv)
    (hagrees : ExternalExecutorAgrees external program.globalenv)
    (hcheck : executeProgram external program fuel = some (total, status))
    (hinit : InitialState program start)
    (hrun : Steps program.globalenv start trace state)
    (hstop : ∀ emitted next, ¬ Step program.globalenv state emitted next) :
    trace = total ∧ FinalState state status := by
  obtain ⟨_, _, htrace, hsuffix, hfinal⟩ :=
    execute_program_prefix hsound hagrees hcheck hinit hrun
  cases hsuffix with
  | refl => exact ⟨by simpa using htrace, hfinal⟩
  | cons h _ => exact False.elim (hstop _ _ h)

/-- A checked terminating program has no infinite execution from an initial state. -/
theorem execute_program_not_infinite {program : Program} {fuel : Nat}
    {total : Trace} {status : Integers.Int} {start : State}
    (hagrees : ExternalExecutorAgrees external program.globalenv)
    (hcheck : executeProgram external program fuel = some (total, status))
    (hinit : InitialState program start)
    (states : Nat → State) (traces : Nat → Trace) (hstart : states 0 = start)
    (hsteps : ∀ n, Step program.globalenv
      (states n) (traces n) (states (n + 1))) : False := by
  obtain ⟨checkedStart, finish, hcheckedInit, hcheckedRun, hfinal⟩ :=
    execute_program_checked_run hcheck
  obtain rfl := initial_state_unique hcheckedInit hinit
  exact execute_steps_not_infinite hagrees hcheckedRun
    (fun _ _ => final_state_stuck hfinal) states traces hstart hsteps

end Quadrature.Asm
