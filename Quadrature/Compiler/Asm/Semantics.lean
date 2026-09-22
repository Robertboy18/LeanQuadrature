import Quadrature.Compiler.Asm.Arguments
import Quadrature.Compiler.Asm.Instructions
import Quadrature.Compiler.Cminor.Semantics

/-!
# Assembly transition rules

Small-step rules for x86-64 assembly, after `x86/Asm.v`, for the fragment the ten programs
use and the ELF64 calling convention. Read `Step` first: its three rules execute an
internal instruction, a builtin, or an external function at the program counter. Calls
and returns use the `RA` register and memory of `State`, so there is no return-address
oracle.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Asm

open CC

/-- Registers after a builtin: clobbered registers undefined, the result written, flags
undefined, and `PC` advanced. -/
def afterBuiltin (registers : Regset) (ef : ExtFun) (result : BuiltinRes)
    (value : Val) : Regset :=
  nextInstrNf ((registers.undefRegs ((LTL.destroyedByBuiltin ef).map pregOf)).setResult
    result value)

/-- Registers after an external call: caller-save registers undefined, the result in the
convention's register, and `PC` set to `RA`. -/
def afterExternal (registers : Regset) (ef : ExtFun) (value : Val) : Regset :=
  (registers.undefCallerSave.set (pregOf (LTL.locResult ef.sig)) value).set .PC
    (registers .RA)

/-- One assembly transition under global environment `ge`, emitting a trace. `internal`
executes the instruction at `PC`, `builtin` runs a `Pbuiltin` through the external-call
relation `externalCall`, and `external` calls an external function at offset zero. -/
inductive Step [ExternalCalls] (ge : Genv) : State → Trace → State → Prop where
  | internal (block offset function instruction registers memory next) :
      registers .PC = .Vptr block offset →
      CC.Genv.findFunctPtr ge block = some (.Internal function) →
      findInstr (Integers.Ptrofs.unsigned offset) function.fn_code = some instruction →
      execInstr ge function instruction registers memory = some next →
      Step ge ⟨registers, memory⟩ E0 next
  | builtin (block offset function ef args result registers memory values trace value memory') :
      registers .PC = .Vptr block offset →
      CC.Genv.findFunctPtr ge block = some (.Internal function) →
      findInstr (Integers.Ptrofs.unsigned offset) function.fn_code =
        some (.Pbuiltin ef args result) →
      EvalBuiltinArgs ge (registers (.IR .RSP)) registers memory args values →
      externalCall ef ge.toSenv values memory trace value memory' →
      Step ge ⟨registers, memory⟩ trace ⟨afterBuiltin registers ef result value, memory'⟩
  | external (block ef registers memory args trace value memory') :
      registers .PC = .Vptr block Integers.Ptrofs.zero →
      CC.Genv.findFunctPtr ge block = some (.External ef) →
      ExternalArgs registers memory (registers (.IR .RSP)) ef.sig args →
      externalCall ef ge.toSenv args memory trace value memory' →
      Step ge ⟨registers, memory⟩ trace ⟨afterExternal registers ef value, memory'⟩

/-- The entry registers: `PC` at the entry symbol, `RA` and `RSP` null, all others `Vundef`. -/
def entryRegisters (program : Program) : Regset :=
  ((Regset.empty.set .PC
    (CC.Genv.symbolAddress program.globalenv program.prog_main Integers.Ptrofs.zero)).set
    .RA Val.Vnullptr).set (.IR .RSP) Val.Vnullptr

/-- The initial state of `program`: `entryRegisters` and the program's initial memory. -/
inductive InitialState (program : Program) : State → Prop where
  | intro (memory : Mem) :
      program.initMem = some memory →
      InitialState program ⟨entryRegisters program, memory⟩

/-- A final state has `PC` equal to the null pointer and the integer exit status in `RAX`. -/
inductive FinalState : State → Integers.Int → Prop where
  | intro (registers : Regset) (memory : Mem) (result : Integers.Int) :
      registers .PC = Val.Vnullptr →
      registers (.IR .RAX) = .Vint result →
      FinalState ⟨registers, memory⟩ result

/-- Finite sequences of transitions, concatenating their traces. -/
inductive Steps [ExternalCalls] (ge : Genv) : State → Trace → State → Prop where
  | refl (state : State) : Steps ge state [] state
  | cons {start next finish : State} {first rest : Trace} :
      Step ge start first next → Steps ge next rest finish →
      Steps ge start (first ++ rest) finish

variable [ExternalCalls] {ge : Genv}

/-- A single transition `h` is a one-step sequence with the same trace. -/
theorem steps_single {start finish : State} {trace : Trace} (h : Step ge start trace finish) :
    Steps ge start trace finish := by
  simpa using Steps.cons h (.refl finish)

/-- Two sequences `hleft` and `hright` compose, concatenating their traces. -/
theorem steps_trans {start middle finish : State} {left right : Trace}
    (hleft : Steps ge start left middle) (hright : Steps ge middle right finish) :
    Steps ge start (left ++ right) finish := by
  induction hleft with
  | refl => exact hright
  | cons h _ ih => simpa only [List.append_assoc] using Steps.cons h (ih hright)

/-- No transition leaves a final state `hfinal`. -/
theorem final_state_stuck {state next : State} {result : Integers.Int} {trace : Trace}
    (hfinal : FinalState state result) : ¬ Step ge state trace next := by
  cases hfinal with
  | intro registers memory result hpc _ =>
      intro hstep
      cases hstep <;> simp_all [Val.Vnullptr, Archi.ptr64]

end Quadrature.Asm
