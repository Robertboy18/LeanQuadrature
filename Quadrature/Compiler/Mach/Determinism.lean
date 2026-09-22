import Quadrature.Compiler.Mach.ProgramExecution

/-!
# Uniqueness and termination of checked Mach executions

Agreement results for the Mach checker. Read `execute_step_agrees` first: when the
return-address predictor agrees with the oracle and the external executor agrees with
the external-call relation, a successful `executeStep` fixes every semantic successor
and its trace. A checked terminating run therefore excludes both a different maximal
finite result and an infinite execution. `StoredTotalCorrectness` discharges the
predictor contract from the table's consistency, and `GeneratedReturnPrograms` from the
Lean Asmgen translation.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Mach

open CC

/-- A predicted address agrees with every address permitted at the same continuation. -/
def ReturnAddressExecutorAgrees (predict : ReturnAddressExecutor)
    (relation : ReturnAddress) : Prop :=
  ∀ function code offset other, predict function code = some offset →
    relation function code other → offset = other

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

variable {predict : ReturnAddressExecutor} {returnAddress : ReturnAddress}
  {external : ExternalExecutor} {ge : Genv}

/-- A successful check fixes every relational successor and its exact trace. -/
theorem execute_step_agrees (hreturn : ReturnAddressExecutorAgrees predict returnAddress)
    (hexternal : ExternalExecutorAgrees external ge)
    {start finish other : State} {trace otherTrace : Trace}
    (h : executeStep predict external ge start = some (trace, finish))
    (hother : Step returnAddress ge start otherTrace other) :
    trace = otherTrace ∧ finish = other := by
  cases hother with
  | operation s f sp rs m op args result bb value hv =>
      simpa [executeStep, hv] using h.symm
  | load s f sp rs m chunk address args result bb pointer value hp hv =>
      simpa [executeStep, hp, hv] using h.symm
  | getstack s f sp rs m offset type result bb value hv =>
      simpa [executeStep, hv] using h.symm
  | setstack s f sp rs m source offset type bb m' hm =>
      simpa [executeStep, hm] using h.symm
  | getparam s fb f sp rs m offset type result bb value hf hlink hv =>
      simpa [executeStep, find_internal_iff.mpr hf, hlink, hv] using h.symm
  | store s f sp rs m chunk address args source bb pointer m' hp hm =>
      simpa [executeStep, hp, hm] using h.symm
  | call s fb f sp rs m signature target bb called offset hcalled hf hra =>
      simp only [executeStep, hcalled, find_internal_iff.mpr hf, bind,
        Option.bind_some, Option.bind_eq_some_iff] at h
      obtain ⟨checkedOffset, hchecked, h⟩ := h
      cases h
      obtain rfl := hreturn _ _ _ _ hchecked hra
      exact ⟨rfl, rfl⟩
  | tailcall s fb f block soff rs m signature target bb called m' hcalled hf hlink hra hfree =>
      have hrelease := release_frame_iff.mpr ⟨block, soff, rfl, hlink, hra, hfree⟩
      simpa [executeStep, hcalled, find_internal_iff.mpr hf, hrelease] using h.symm
  | builtin s f sp rs m ef args result bb values emitted value m' hv hext =>
      simp only [executeStep, eval_builtin_args_complete hv, bind,
        Option.bind_some, Option.bind_eq_some_iff] at h
      obtain ⟨⟨checkedTrace, checkedValue, checkedMemory⟩, hchecked, h⟩ := h
      cases h
      obtain ⟨rfl, rfl, rfl⟩ := hexternal _ _ _ _ _ _ _ _ _ hchecked hext
      exact ⟨rfl, rfl⟩
  | label =>
      simpa only [executeStep, Option.some.injEq, Prod.mk.injEq] using h.symm
  | goto s fb f sp rs m label bb target hf htarget =>
      simpa [executeStep, find_internal_iff.mpr hf, htarget] using h.symm
  | condition_true s fb f sp rs m condition args label bb target hb hf htarget =>
      simpa [executeStep, hb, find_internal_iff.mpr hf, htarget] using h.symm
  | condition_false s fb sp rs m condition args label bb hb =>
      simpa [executeStep, hb] using h.symm
  | jumpTable s fb f sp rs m arg table bb index label target harg hn hf htarget =>
      simpa [executeStep, harg, hn, find_internal_iff.mpr hf, htarget] using h.symm
  | returnValue s fb f block soff rs m bb m' hf hlink hra hfree =>
      have hrelease := release_frame_iff.mpr ⟨block, soff, rfl, hlink, hra, hfree⟩
      simpa [executeStep, find_internal_iff.mpr hf, hrelease] using h.symm
  | internal_function s fb f rs m m₁ m₂ m₃ block hf halloc hlink hra =>
      simpa [executeStep, hf, halloc, hlink, hra] using h.symm
  | external_function s fb ef rs m args emitted value m' hf hargs hext =>
      simp only [executeStep, hf, external_args_iff.mp hargs, bind,
        Option.bind_some, Option.bind_eq_some_iff] at h
      obtain ⟨⟨checkedTrace, checkedValue, checkedMemory⟩, hchecked, h⟩ := h
      cases h
      obtain ⟨rfl, rfl, rfl⟩ := hexternal _ _ _ _ _ _ _ _ _ hchecked hext
      exact ⟨rfl, rfl⟩
  | return_to_caller =>
      simpa only [executeStep, Option.some.injEq, Prod.mk.injEq] using h.symm

/-- Every semantic prefix of a checked terminating run has a checked suffix. -/
theorem execute_steps_prefix (hreturn : ReturnAddressExecutorAgrees predict returnAddress)
    (hexternal : ExternalExecutorAgrees external ge)
    {fuel : Nat} {start finish state : State} {total trace : Trace}
    (hcheck : executeSteps predict external ge fuel start = some (total, finish))
    (hstop : ∀ emitted next, ¬ Step returnAddress ge finish emitted next)
    (hprefix : Steps returnAddress ge start trace state) :
    ∃ remainingFuel remaining, remainingFuel ≤ fuel ∧ trace ++ remaining = total ∧
      executeSteps predict external ge remainingFuel state = some (remaining, finish) := by
  apply Execution.run_prefix (execute_step_agrees hreturn hexternal) ?_ hcheck hstop hprefix
  intro first last emitted h
  cases h with
  | refl => exact Or.inl ⟨rfl, rfl⟩
  | cons hstep hsuffix => exact Or.inr ⟨_, _, _, hstep, hsuffix, rfl⟩

/-- A maximal finite execution has exactly the checked trace and final state. -/
theorem execute_steps_unique (hreturnSound : ReturnAddressExecutorSound predict returnAddress)
    (hreturnAgrees : ReturnAddressExecutorAgrees predict returnAddress)
    (hsound : ExternalExecutorSound external ge) (hagrees : ExternalExecutorAgrees external ge)
    {fuel : Nat} {start finish state : State} {total trace : Trace}
    (hcheck : executeSteps predict external ge fuel start = some (total, finish))
    (hstop : ∀ emitted next, ¬ Step returnAddress ge finish emitted next)
    (hprefix : Steps returnAddress ge start trace state)
    (hotherStop : ∀ emitted next, ¬ Step returnAddress ge state emitted next) :
    trace = total ∧ state = finish := by
  obtain ⟨_, _, _, htrace, hremaining⟩ :=
    execute_steps_prefix hreturnAgrees hagrees hcheck hstop hprefix
  have hsuffix := execute_steps_sound hreturnSound hsound hremaining
  cases hsuffix with
  | refl => exact ⟨by simpa using htrace, rfl⟩
  | cons h _ => exact False.elim (hotherStop _ _ h)

/-- No infinite semantic execution can share the start of a checked terminating run. -/
theorem execute_steps_not_infinite (hreturn : ReturnAddressExecutorAgrees predict returnAddress)
    (hexternal : ExternalExecutorAgrees external ge)
    {fuel : Nat} {start finish : State} {total : Trace}
    (hcheck : executeSteps predict external ge fuel start = some (total, finish))
    (hstop : ∀ emitted next, ¬ Step returnAddress ge finish emitted next)
    (states : Nat → State) (traces : Nat → Trace) (hstart : states 0 = start)
    (hsteps : ∀ n, Step returnAddress ge (states n) (traces n) (states (n + 1))) : False := by
  rw [execute_steps_eq_run] at hcheck
  exact Execution.run_not_infinite (Step := Step returnAddress ge)
    (fun hstep hother => (execute_step_agrees hreturn hexternal hstep hother).2)
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
    (h : executeProgram predict external program fuel = some (trace, status)) :
    ∃ start finish, InitialState program start ∧
      executeSteps predict external program.globalenv fuel start = some (trace, finish) ∧
      FinalState finish status := by
  simp only [executeProgram, bind, Option.bind_eq_some_iff] at h
  obtain ⟨start, hstart, ⟨events, finish⟩, hrun, result, hfinish, h⟩ := h
  cases h
  exact ⟨start, finish, initial_state_sound hstart, hrun, exit_status_sound hfinish⟩

/-- Any execution from any initial state can finish with the certified observation. -/
theorem execute_program_prefix {program : Program} {fuel : Nat}
    {total trace : Trace} {status : Integers.Int} {start state : State}
    (hreturnSound : ReturnAddressExecutorSound predict returnAddress)
    (hreturnAgrees : ReturnAddressExecutorAgrees predict returnAddress)
    (hsound : ExternalExecutorSound external program.globalenv)
    (hagrees : ExternalExecutorAgrees external program.globalenv)
    (hcheck : executeProgram predict external program fuel = some (total, status))
    (hinit : InitialState program start)
    (hrun : Steps returnAddress program.globalenv start trace state) :
    ∃ remaining finish, trace ++ remaining = total ∧
      Steps returnAddress program.globalenv state remaining finish ∧
      FinalState finish status := by
  obtain ⟨checkedStart, finish, hcheckedInit, hcheckedRun, hfinal⟩ :=
    execute_program_checked_run hcheck
  obtain rfl := initial_state_unique hcheckedInit hinit
  obtain ⟨_, remaining, _, htrace, hremaining⟩ :=
    execute_steps_prefix hreturnAgrees hagrees hcheckedRun
      (fun _ _ => final_state_stuck hfinal) hrun
  exact ⟨remaining, finish, htrace, execute_steps_sound hreturnSound hsound hremaining, hfinal⟩

/-- Every reachable state is final with the certified status or admits another step. -/
theorem execute_program_progress {program : Program} {fuel : Nat}
    {total trace : Trace} {status : Integers.Int} {start state : State}
    (hreturnSound : ReturnAddressExecutorSound predict returnAddress)
    (hreturnAgrees : ReturnAddressExecutorAgrees predict returnAddress)
    (hsound : ExternalExecutorSound external program.globalenv)
    (hagrees : ExternalExecutorAgrees external program.globalenv)
    (hcheck : executeProgram predict external program fuel = some (total, status))
    (hinit : InitialState program start)
    (hrun : Steps returnAddress program.globalenv start trace state) :
    FinalState state status ∨
      ∃ emitted next, Step returnAddress program.globalenv state emitted next := by
  obtain ⟨_, _, _, hsuffix, hfinal⟩ :=
    execute_program_prefix hreturnSound hreturnAgrees hsound hagrees hcheck hinit hrun
  cases hsuffix with
  | refl => exact Or.inl hfinal
  | cons h _ => exact Or.inr ⟨_, _, h⟩

/-- Every maximal finite execution has the certified trace and exit status. -/
theorem execute_program_unique {program : Program} {fuel : Nat}
    {total trace : Trace} {status : Integers.Int} {start state : State}
    (hreturnSound : ReturnAddressExecutorSound predict returnAddress)
    (hreturnAgrees : ReturnAddressExecutorAgrees predict returnAddress)
    (hsound : ExternalExecutorSound external program.globalenv)
    (hagrees : ExternalExecutorAgrees external program.globalenv)
    (hcheck : executeProgram predict external program fuel = some (total, status))
    (hinit : InitialState program start)
    (hrun : Steps returnAddress program.globalenv start trace state)
    (hstop : ∀ emitted next, ¬ Step returnAddress program.globalenv state emitted next) :
    trace = total ∧ FinalState state status := by
  obtain ⟨_, _, htrace, hsuffix, hfinal⟩ :=
    execute_program_prefix hreturnSound hreturnAgrees hsound hagrees hcheck hinit hrun
  cases hsuffix with
  | refl => exact ⟨by simpa using htrace, hfinal⟩
  | cons h _ => exact False.elim (hstop _ _ h)

/-- A checked terminating program has no infinite execution from an initial state. -/
theorem execute_program_not_infinite {program : Program} {fuel : Nat}
    {total : Trace} {status : Integers.Int} {start : State}
    (hreturn : ReturnAddressExecutorAgrees predict returnAddress)
    (hagrees : ExternalExecutorAgrees external program.globalenv)
    (hcheck : executeProgram predict external program fuel = some (total, status))
    (hinit : InitialState program start)
    (states : Nat → State) (traces : Nat → Trace) (hstart : states 0 = start)
    (hsteps : ∀ n, Step returnAddress program.globalenv
      (states n) (traces n) (states (n + 1))) : False := by
  obtain ⟨checkedStart, finish, hcheckedInit, hcheckedRun, hfinal⟩ :=
    execute_program_checked_run hcheck
  obtain rfl := initial_state_unique hcheckedInit hinit
  exact execute_steps_not_infinite hreturn hagrees hcheckedRun
    (fun _ _ => final_state_stuck hfinal) states traces hstart hsteps

end Quadrature.Mach
