import Quadrature.Compiler.RTL.Execution

/-!
# From an initialized program to its observable result

`executeProgram external program fuel` builds the initial state of `program`, runs
`fuel` checker steps, and reads the exit status. `initialState` allocates every global
and resolves the entry symbol. `execute_program_sound` turns a successful result into an
initial state, a `Steps` run with that trace, and a final state with that status.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.RTL

open CC

/-- `initialState program` computes the initial state: it allocates the globals, resolves the
entry symbol, and checks that the entry has signature `int main(void)`. -/
def initialState (program : Program) : Option State := do
  let memory ← program.initMem
  let block ← CC.Genv.findSymbol program.globalenv program.prog_main
  let function ← CC.Genv.findFunctPtr program.globalenv block
  if function.signature = mksignature [] .Xint cc_default then
    pure (.Callstate [] function [] memory)
  else none

/-- If `initialState program` returns `some s`, then `InitialState program s`. -/
theorem initial_state_sound {program : Program} {state : State}
    (h : initialState program = some state) : InitialState program state := by
  simp only [initialState, bind, Option.bind_eq_some_iff] at h
  obtain ⟨memory, hmemory, block, hblock, function, hfunction, h⟩ := h
  split at h
  next hsignature =>
    cases h
    exact .intro block function memory hmemory hblock hfunction hsignature
  next => cases h

/-- `exitStatus s` returns the exit status when `s` is a final state, and `none` otherwise. -/
def exitStatus : State → Option Integers.Int
  | .Returnstate [] (.Vint status) _ => some status
  | _ => none

/-- If `exitStatus s` returns `some r`, then `FinalState s r`. -/
theorem exit_status_sound {state : State} {status : Integers.Int}
    (h : exitStatus state = some status) : FinalState state status := by
  cases state with
  | Running => cases h
  | Callstate => cases h
  | Returnstate frames value memory =>
      cases frames <;> cases value <;> cases h
      constructor

/-- `executeProgram external program fuel` runs `fuel` checker steps from the initial state and
returns the observation: the event trace and the exit status. -/
def executeProgram (external : ExternalExecutor) (program : Program) (fuel : Nat) :
    Option (Trace × Integers.Int) := do
  let start ← initialState program
  let (trace, finish) ← executeSteps external program.globalenv fuel start
  let status ← exitStatus finish
  pure (trace, status)

/-- If `executeProgram external program fuel` returns `some (t, r)` and `external` is sound, some
initial state runs by `Steps` with trace `t` to a final state with status `r`. -/
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

end Quadrature.RTL
