import Quadrature.Compiler.Mach.Execution

/-!
# Initialized Mach executions

The whole-program checker for Mach. Read `executeProgram` first, which allocates all
globals, resolves the entry symbol, runs a fixed number of transitions with a given
return-address predictor, and reads the exit status. `execute_program_sound` turns a
successful check into an initial state, a finite `Steps` execution, and a final state,
for any oracle the predictor is sound for.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Mach

open CC

/-- Computes the initial state of `program`: its initial memory and the block of `prog_main`. -/
def initialState (program : Program) : Option State := do
  let memory ← program.initMem
  let block ← CC.Genv.findSymbol program.globalenv program.prog_main
  pure (.Callstate [] block Regset.empty memory)

/-- A state computed by `initialState` satisfies `InitialState`. -/
theorem initial_state_sound {program : Program} {state : State}
    (h : initialState program = some state) : InitialState program state := by
  simp only [initialState, bind, Option.bind_eq_some_iff] at h
  obtain ⟨memory, hmemory, block, hblock, h⟩ := h
  cases h
  exact .intro block memory hmemory hblock

/-- Every `InitialState` is the state computed by `initialState`. -/
theorem initial_state_complete {program : Program} {state : State}
    (h : InitialState program state) : initialState program = some state := by
  cases h with
  | intro block memory hmemory hblock =>
      simp [initialState, hmemory, hblock]

/-- Reads the integer exit status from a frameless `Returnstate`, `none` for any other state. -/
def exitStatus : State → Option Integers.Int
  | .Returnstate [] registers _ =>
      match registers .AX with
      | .Vint status => some status
      | _ => none
  | _ => none

/-- A status read by `exitStatus` witnesses `FinalState`. -/
theorem exit_status_sound {state : State} {status : Integers.Int}
    (h : exitStatus state = some status) : FinalState state status := by
  cases state with
  | Running | Callstate => cases h
  | Returnstate frames registers memory =>
      cases frames with
      | cons => cases h
      | nil =>
          simp only [exitStatus] at h
          cases hvalue : registers .AX <;> simp only [hvalue] at h <;> cases h
          exact .intro _ _ _ hvalue

/-- Every `FinalState` status is the one read by `exitStatus`. -/
theorem exit_status_complete {state : State} {status : Integers.Int}
    (h : FinalState state status) : exitStatus state = some status := by
  cases h with
  | intro registers result memory hresult => simp [exitStatus, hresult]

/-- Runs `program` for `fuel` transitions from its initial state, predicting return addresses
with `predict`, and returns the trace and exit status. -/
def executeProgram (predict : ReturnAddressExecutor) (external : ExternalExecutor)
    (program : Program) (fuel : Nat) : Option (Trace × Integers.Int) := do
  let start ← initialState program
  let (trace, finish) ← executeSteps predict external program.globalenv fuel start
  let status ← exitStatus finish
  pure (trace, status)

/-- A successful `executeProgram` check under a sound predictor `hreturn` and a sound external
executor `hexternal` yields an initial state, a `Steps` execution, and a final state. The
execution has the checked trace and the final state the checked status. -/
theorem execute_program_sound [ExternalCalls] {predict : ReturnAddressExecutor}
    {returnAddress : ReturnAddress} {external : ExternalExecutor} {program : Program}
    {fuel : Nat} {trace : Trace} {status : Integers.Int}
    (hreturn : ReturnAddressExecutorSound predict returnAddress)
    (hexternal : ExternalExecutorSound external program.globalenv)
    (h : executeProgram predict external program fuel = some (trace, status)) :
    ∃ start finish, InitialState program start ∧
      Steps returnAddress program.globalenv start trace finish ∧ FinalState finish status := by
  simp only [executeProgram, bind, Option.bind_eq_some_iff] at h
  obtain ⟨start, hstart, ⟨events, finish⟩, hrun, result, hfinish, h⟩ := h
  cases h
  exact ⟨start, finish, initial_state_sound hstart,
    execute_steps_sound hreturn hexternal hrun, exit_status_sound hfinish⟩

end Quadrature.Mach
