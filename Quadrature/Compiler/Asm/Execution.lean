import Quadrature.Compiler.Asm.Semantics
import Quadrature.Compiler.Cminor.Annotations
import Quadrature.Compiler.Execution.Run

/-!
# A checked assembly executor

An executable checker for the rules of `Quadrature.Compiler.Asm.Semantics`. Read `executeStep`
first: it follows `PC` to an internal instruction or an external function and computes
the successor state, using an external executor for builtins and external calls.
`execute_step_sound` shows that every successful step is a `Step` derivation whenever
the external executor is sound.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Asm

open CC

/-- Executable external calls, the contract shared by every stage. -/
abbrev ExternalExecutor := Cminor.ExternalExecutor
/-- The external executor that emits numeric annotations and delegates other calls to CLean. -/
abbrev annotatedExternalCall := Cminor.annotatedExternalCall

/-- Executes one instruction at `PC`: a `Pbuiltin` through `external`, anything else through
`execInstr` with an empty trace. -/
def executeInstruction (external : ExternalExecutor) (ge : Genv) (function : Function)
    (instruction : Instruction) (registers : Regset) (memory : Mem) :
    Option (Trace × State) :=
  match instruction with
  | .Pbuiltin ef args result => do
      let values ← evalBuiltinArgs ge (registers (.IR .RSP)) registers memory args
      let (trace, value, memory') ← external ef values memory
      pure (trace, ⟨afterBuiltin registers ef result value, memory'⟩)
  | _ => do
      let next ← execInstr ge function instruction registers memory
      pure (E0, next)

/-- Computes one assembly transition, using `external` for builtins and external functions.
Returns `none` when `PC` is not a pointer into a function, the instruction is outside the
fragment, or a memory access fails. -/
def executeStep (external : ExternalExecutor) (ge : Genv) (state : State) :
    Option (Trace × State) := do
  let registers := state.registers
  let memory := state.memory
  match registers .PC with
  | .Vptr block offset =>
      let fd ← CC.Genv.findFunctPtr ge block
      match fd with
      | .Internal function =>
          let instruction ← findInstr (Integers.Ptrofs.unsigned offset) function.fn_code
          executeInstruction external ge function instruction registers memory
      | .External ef =>
          if offset = Integers.Ptrofs.zero then do
            let args ← externalArgs registers memory (registers (.IR .RSP)) ef.sig
            let (trace, value, memory') ← external ef args memory
            pure (trace, ⟨afterExternal registers ef value, memory'⟩)
          else none
  | _ => none

/-- Runs exactly `fuel` transitions from a state, concatenating their traces. -/
def executeSteps (external : ExternalExecutor) (ge : Genv) :
    Nat → State → Option (Trace × State) :=
  Execution.run (executeStep external ge)

/-- The stage-specific executor implements the shared finite runner. -/
theorem execute_steps_eq_run (external : ExternalExecutor) (ge : Genv)
    (fuel : Nat) (state : State) :
    executeSteps external ge fuel state = Execution.run (executeStep external ge) fuel state :=
  rfl

/-- Every result accepted by `external` is permitted by the external-call relation over `ge`. -/
def ExternalExecutorSound [ExternalCalls] (external : ExternalExecutor) (ge : Genv) : Prop :=
  Execution.ExternalExecutorSound external ge.toSenv

variable [ExternalCalls] {external : ExternalExecutor} {ge : Genv}

/-- A successful `executeInstruction` of the instruction at `PC` (`hpc`, `hfunction`,
`hinstruction`) is a `Step` under a sound external executor `hexternal`. -/
theorem execute_instruction_sound (hexternal : ExternalExecutorSound external ge)
    {block : Block} {offset : Integers.Ptrofs} {function : Function}
    {instruction : Instruction} {registers : Regset} {memory : Mem}
    {trace : Trace} {next : State}
    (hpc : registers .PC = .Vptr block offset)
    (hfunction : CC.Genv.findFunctPtr ge block = some (.Internal function))
    (hinstruction : findInstr (Integers.Ptrofs.unsigned offset) function.fn_code =
      some instruction)
    (h : executeInstruction external ge function instruction registers memory =
      some (trace, next)) :
    Step ge ⟨registers, memory⟩ trace next := by
  unfold executeInstruction at h
  split at h
  · next ef args result =>
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨values, hvalues, ⟨events, value, memory'⟩, hext, h⟩ := h
      cases h
      exact .builtin block offset function ef args result registers memory values
        events value memory' hpc hfunction hinstruction (eval_builtin_args_sound hvalues)
        (hexternal _ _ _ _ _ _ hext)
  · simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨finish, hfinish, h⟩ := h
    cases h
    exact .internal _ _ _ _ _ _ _ hpc hfunction hinstruction hfinish

/-- A successful `executeStep` under a sound external executor `hexternal` is a `Step`. -/
theorem execute_step_sound (hexternal : ExternalExecutorSound external ge)
    {start finish : State} {trace : Trace}
    (h : executeStep external ge start = some (trace, finish)) :
    Step ge start trace finish := by
  rcases start with ⟨registers, memory⟩
  simp only [executeStep] at h
  cases hpc : registers .PC <;> simp only [hpc] at h <;> try cases h
  case Vptr block offset =>
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨fd, hfd, h⟩ := h
    cases fd with
    | Internal function =>
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨instruction, hinstruction, h⟩ := h
        exact execute_instruction_sound hexternal hpc hfd hinstruction h
    | External ef =>
        dsimp only at h
        split at h
        · next hoffset =>
            subst offset
            simp only [Option.bind_eq_some_iff] at h
            obtain ⟨args, hargs, ⟨events, value, memory'⟩, hext, h⟩ := h
            cases h
            exact .external _ _ _ _ _ _ _ _ hpc hfd
              (external_args_iff.mpr hargs) (hexternal _ _ _ _ _ _ hext)
        · cases h

/-- A successful `executeSteps` run under a sound external executor `hexternal` is a `Steps`
derivation with the same trace. -/
theorem execute_steps_sound (hexternal : ExternalExecutorSound external ge)
    {fuel : Nat} {start finish : State} {trace : Trace}
    (h : executeSteps external ge fuel start = some (trace, finish)) :
    Steps ge start trace finish := by
  rw [execute_steps_eq_run] at h
  exact Execution.run_sound (execute_step_sound hexternal) Steps.refl Steps.cons h

/-- The numeric-annotation executor is sound in every global environment. -/
theorem annotated_external_executor_sound :
    ExternalExecutorSound annotatedExternalCall ge :=
  Cminor.annotated_external_call_sound

end Quadrature.Asm
