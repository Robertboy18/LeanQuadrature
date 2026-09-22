import Quadrature.Compiler.Asm.Execution

/-!
# Initialized assembly executions

The whole-program checker for assembly. Read `executeProgram` first: it allocates all globals,
builds the entry registers, and runs a fixed number of transitions. The exit status is read
from a final state whose `PC` is null. `execute_program_sound` turns a successful check into
an initial state, a finite `Steps` execution, and a final state.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Asm

open CC

/-- Computes the initial state of `program`: `entryRegisters` and its initial memory. -/
def initialState (program : Program) : Option State := do
  let memory ← program.initMem
  pure ⟨entryRegisters program, memory⟩

/-- A state computed by `initialState` satisfies `InitialState`. -/
theorem initial_state_sound {program : Program} {state : State}
    (h : initialState program = some state) : InitialState program state := by
  simp only [initialState, bind, Option.bind_eq_some_iff] at h
  obtain ⟨memory, hmemory, h⟩ := h
  cases h
  exact .intro memory hmemory

/-- Every `InitialState` is the state computed by `initialState`. -/
theorem initial_state_complete {program : Program} {state : State}
    (h : InitialState program state) : initialState program = some state := by
  cases h with
  | intro memory hmemory => simp [initialState, hmemory]

/-- Reads the integer exit status from `RAX` when `PC` is the null pointer, `none` otherwise. -/
def exitStatus (state : State) : Option Integers.Int :=
  if state.registers .PC = Val.Vnullptr then
    match state.registers (.IR .RAX) with
    | .Vint status => some status
    | _ => none
  else none

/-- A status read by `exitStatus` witnesses `FinalState`. -/
theorem exit_status_sound {state : State} {status : Integers.Int}
    (h : exitStatus state = some status) : FinalState state status := by
  rcases state with ⟨registers, memory⟩
  unfold exitStatus at h
  split at h
  · next hpc =>
      cases hvalue : registers (.IR .RAX) <;> simp only [hvalue] at h <;> cases h
      exact .intro _ _ _ hpc hvalue
  · cases h

/-- Every `FinalState` status is the one read by `exitStatus`. -/
theorem exit_status_complete {state : State} {status : Integers.Int}
    (h : FinalState state status) : exitStatus state = some status := by
  cases h with
  | intro registers memory result hpc hresult => simp [exitStatus, hpc, hresult]

/-- Runs `program` for `fuel` transitions from its initial state and returns the trace and
exit status. -/
def executeProgram (external : ExternalExecutor) (program : Program) (fuel : Nat) :
    Option (Trace × Integers.Int) := do
  let start ← initialState program
  let (trace, finish) ← executeSteps external program.globalenv fuel start
  let status ← exitStatus finish
  pure (trace, status)

/-- A successful `executeProgram` check under a sound external executor `hexternal` yields an
initial state, a `Steps` execution, and a final state. The execution has the checked trace and
the final state the checked status. -/
theorem execute_program_sound [ExternalCalls] {external : ExternalExecutor} {program : Program}
    {fuel : Nat} {trace : Trace} {status : Integers.Int}
    (hexternal : ExternalExecutorSound external program.globalenv)
    (h : executeProgram external program fuel = some (trace, status)) :
    ∃ start finish, InitialState program start ∧
      Steps program.globalenv start trace finish ∧ FinalState finish status := by
  simp only [executeProgram, bind, Option.bind_eq_some_iff] at h
  obtain ⟨start, hstart, ⟨events, finish⟩, hrun, result, hfinish, h⟩ := h
  cases h
  exact ⟨start, finish, initial_state_sound hstart,
    execute_steps_sound hexternal hrun, exit_status_sound hfinish⟩

end Quadrature.Asm
