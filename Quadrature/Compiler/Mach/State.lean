import Quadrature.Compiler.Mach.Syntax

/-!
# Concrete stack frames and machine registers

Register sets and stack frames for Mach, after `backend/Mach.v` on x86-64 ELF. Read
`State` first: a frame list, the current function's block, the stack pointer, the
remaining code, registers, and memory. Stack accesses use byte offsets in the ordinary
memory model, and saved registers are restored by the program's own load instructions.
`ReturnAddress` is the type of the return-address oracle that `Step` takes as a parameter.
The table oracle used by the ten programs is related to the Lean Asmgen translation's
return addresses in `Asm/GeneratedReturnAddresses.lean`.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Mach

open CC

/-- Machine registers map to values. Stack slots are memory after frame layout. -/
abbrev Regset := MachineReg → Val

/-- The register set with every register `Vundef`. -/
def Regset.empty : Regset := fun _ => .Vundef

/-- The values of a list of registers, in order. -/
def Regset.values (registers : Regset) (args : List MachineReg) : List Val :=
  args.map registers

/-- Updates one register. -/
def Regset.set (registers : Regset) (register : MachineReg) (value : Val) : Regset :=
  fun other => if register = other then value else registers other

/-- Sets each listed register to `Vundef`. -/
def Regset.undefRegs (registers : Regset) : List MachineReg → Regset
  | [] => registers
  | register :: rest => (registers.undefRegs rest).set register .Vundef

/-- Sets every caller-save register to `Vundef`, keeping the callee-save ones. -/
def Regset.undefCallerSave (registers : Regset) : Regset :=
  fun register => if LTL.isCalleeSave register then registers register else .Vundef

/-- Writes a builtin result, splitting a long into high and low words when required. -/
def Regset.setResult (registers : Regset) (result : BuiltinRes) (value : Val) : Regset :=
  match result with
  | .BR register => registers.set register value
  | .BR_none => registers
  | .BR_splitlong hi lo =>
      (registers.setResult hi (Val.hiword value)).setResult lo (Val.loword value)

/-- Reading the register just written returns the written value. -/
@[simp]
theorem set_same (registers : Regset) (register : MachineReg) (value : Val) :
    registers.set register value register = value := by
  simp [Regset.set]

/-- Writing `register` leaves a different register `other` unchanged, given `hne`. -/
theorem set_other (registers : Regset) (register other : MachineReg) (value : Val)
    (hne : register ≠ other) : registers.set register value other = registers other := by
  simp [Regset.set, hne]

/-- Loads a value of type `type` at byte offset `offset` from the stack pointer `stack`. -/
def loadStack (memory : Mem) (stack : Val) (type : ATyp) (offset : Integers.Ptrofs) :
    Option Val :=
  Mem.loadv (Chunk.ofTyp type) memory (Val.offsetPtr stack offset)

/-- Stores `value` with type `type` at byte offset `offset` from the stack pointer `stack`. -/
def storeStack (memory : Mem) (stack : Val) (type : ATyp) (offset : Integers.Ptrofs)
    (value : Val) : Option Mem :=
  Mem.storev (Chunk.ofTyp type) memory (Val.offsetPtr stack offset) value

/-- A caller's saved frame: its function block, stack pointer, return address, and
continuation code. -/
structure Stackframe where
  caller : Block
  stack : Val
  returnAddress : Val
  continuation : Code

/-- Mach execution states: running inside a function, entering a call, or returning. -/
inductive State where
  | Running (frames : List Stackframe) (function : Block) (stack : Val)
      (instructions : Code) (registers : Regset) (memory : Mem)
  | Callstate (frames : List Stackframe) (function : Block) (registers : Regset) (memory : Mem)
  | Returnstate (frames : List Stackframe) (registers : Regset) (memory : Mem)

/-- The caller's stack pointer, or the null pointer at the outermost frame. -/
def parentStack : List Stackframe → Val
  | [] => Val.Vnullptr
  | frame :: _ => frame.stack

/-- The caller's return address, or the null pointer at the outermost frame. -/
def parentReturnAddress : List Stackframe → Val
  | [] => Val.Vnullptr
  | frame :: _ => frame.returnAddress

/-- Resolves a call target to a function block, from a register holding an offset-zero pointer
or from a global symbol. -/
def findFunctionPtr (ge : Genv) (function : Sum MachineReg Ident) (registers : Regset) :
    Option Block :=
  match function with
  | .inl register =>
      match registers register with
      | .Vptr block offset => if offset = Integers.Ptrofs.zero then some block else none
      | _ => none
  | .inr symbol => CC.Genv.findSymbol ge symbol

/-- A return-address oracle. `returnAddress f k ofs` states that `ofs` is the assembly offset
following the call in `f` whose Mach continuation is `k`, CompCert's `return_address_offset`. -/
abbrev ReturnAddress := Function → Code → Integers.Ptrofs → Prop

/-- Evaluates an operation on argument values, as in LTL. -/
abbrev evalOperation := @LTL.evalOperation Fundef Unit
/-- Evaluates an addressing mode to a pointer, as in CminorSel. -/
abbrev evalAddressing := @CminorSel.evalAddressing Fundef Unit
/-- Evaluates a comparison condition to a Boolean, as in CminorSel. -/
abbrev evalCondition := CminorSel.evalCondition
/-- Registers clobbered by an operation on x86-64, as in LTL. -/
abbrev destroyedByOp := LTL.destroyedByOp
/-- Registers clobbered by writing a stack slot of the given type, as in LTL. -/
abbrev destroyedBySetstack := LTL.destroyedBySetstack
/-- Registers clobbered by a builtin call, as in LTL. -/
abbrev destroyedByBuiltin := LTL.destroyedByBuiltin
/-- The argument locations fixed by a signature under the x86-64 calling convention. -/
abbrev locArguments := LTL.locArguments
/-- The result register of a signature: `X0` for floats, `AX` otherwise. -/
abbrev locResult := LTL.locResult

end Quadrature.Mach
