import Quadrature.Compiler.Linear.Execution

/-!
# From an initialized program to its observable result

The whole-program checker for Linear. Read `executeProgram` first, which allocates all
globals, resolves the entry symbol, runs a fixed number of transitions, and reads the
exit status. `execute_program_sound` turns a successful check into an initial state, a
finite `Steps` execution, and a final state, assuming nothing about memory or execution.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Linear

open CC

/-- Computes the initial state of `program`: its initial memory and the entry function of
`prog_main`, checked to have the signature of `int main(void)`. -/
def initialState (program : Program) : Option State := do
  let memory ← program.initMem
  let block ← CC.Genv.findSymbol program.globalenv program.prog_main
  let function ← CC.Genv.findFunctPtr program.globalenv block
  if function.signature = mksignature [] .Xint cc_default then
    pure (.Callstate [] function LTL.Locset.empty memory)
  else none

/-- A state computed by `initialState` satisfies `InitialState`. -/
theorem initial_state_sound {program : Program} {state : State}
    (h : initialState program = some state) : InitialState program state := by
  simp only [initialState, bind, Option.bind_eq_some_iff] at h
  obtain ⟨memory, hmemory, block, hblock, function, hfunction, h⟩ := h
  split at h
  next hsignature =>
    cases h
    exact .intro block function memory hmemory hblock hfunction hsignature
  next => cases h

/-- Reads the integer exit status from a frameless `Returnstate`, `none` for any other state. -/
def exitStatus : State → Option Integers.Int
  | .Returnstate [] locations _ =>
      match locations.reg .AX with
      | .Vint status => some status
      | _ => none
  | _ => none

/-- A status read by `exitStatus` witnesses `FinalState`. -/
theorem exit_status_sound {state : State} {status : Integers.Int}
    (h : exitStatus state = some status) : FinalState state status := by
  cases state with
  | Running | Callstate => cases h
  | Returnstate frames locations memory =>
      cases frames with
      | cons => cases h
      | nil =>
          simp only [exitStatus] at h
          cases hvalue : locations.reg .AX <;> simp only [hvalue] at h <;> cases h
          exact .intro _ _ _ hvalue

/-- Runs `program` for `fuel` transitions from its initial state and returns the trace and
exit status. -/
def executeProgram (external : ExternalExecutor) (program : Program) (fuel : Nat) :
    Option (Trace × Integers.Int) := do
  let start ← initialState program
  let (trace, finish) ← executeSteps external program.globalenv fuel start
  let status ← exitStatus finish
  pure (trace, status)

/-- A successful `executeProgram` check under a sound external executor `hsound` yields an
initial state, a `Steps` execution, and a final state. The execution has the checked trace and
the final state the checked status. -/
theorem execute_program_sound [ExternalCalls] {external : ExternalExecutor}
    {program : Program} {fuel : Nat} {trace : Trace} {status : Integers.Int}
    (hsound : ExternalExecutorSound external program.globalenv)
    (h : executeProgram external program fuel = some (trace, status)) :
    ∃ start finish, InitialState program start ∧
      Steps program.globalenv start trace finish ∧ FinalState finish status := by
  simp only [executeProgram, bind, Option.bind_eq_some_iff] at h
  obtain ⟨start, hstart, ⟨events, finish⟩, hrun, result, hfinish, h⟩ := h
  cases h
  exact ⟨start, finish, initial_state_sound hstart,
    execute_steps_sound hsound hrun, exit_status_sound hfinish⟩

end Quadrature.Linear
