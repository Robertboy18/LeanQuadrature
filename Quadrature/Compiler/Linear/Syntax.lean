import Quadrature.Compiler.LTL.Arguments

/-!
# Linear instruction syntax

Linear syntax after CompCert's `backend/Linear.v`: a function body is a list of
instructions in which labels and explicit jumps replace the LTL graph of basic blocks.
Read `Instruction` first, the thirteen instruction forms. Registers, stack slots,
builtin arguments, and the arithmetic operations are shared with `Quadrature.LTL`.
`findLabel` selects the code after the first matching label.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Linear

open CC

/-- Code labels are positive numbers, as in CompCert. -/
abbrev Label := Positive
/-- The x86-64 machine registers, shared with LTL. -/
abbrev MachineReg := LTL.MachineReg
/-- Stack slot kinds `Local`, `Incoming`, and `Outgoing`, shared with LTL. -/
abbrev Slot := LTL.Slot
/-- A location is a machine register or a typed stack slot, shared with LTL. -/
abbrev Location := LTL.Location
/-- Location sets map every location to a value, shared with LTL. -/
abbrev Locset := LTL.Locset
/-- Builtin argument expressions over locations, shared with LTL. -/
abbrev BuiltinArg := LTL.BuiltinArg
/-- Builtin result registers, shared with LTL. -/
abbrev BuiltinRes := LTL.BuiltinRes
/-- The x86-64 arithmetic operations, shared with LTL. -/
abbrev Operation := LTL.Operation
/-- The x86-64 addressing modes, shared with LTL. -/
abbrev Addressing := LTL.Addressing
/-- Integer comparison conditions, shared with LTL. -/
abbrev Condition := LTL.Condition

/-- The thirteen Linear instructions of `backend/Linear.v`. Labels and jumps replace the
LTL block graph, and the remaining forms keep their LTL meaning. -/
inductive Instruction where
  | Lop (operation : Operation) (args : List MachineReg) (result : MachineReg)
  | Lload (chunk : Chunk) (address : Addressing) (args : List MachineReg) (result : MachineReg)
  | Lgetstack (slot : Slot) (offset : Int) (type : ATyp) (result : MachineReg)
  | Lsetstack (source : MachineReg) (slot : Slot) (offset : Int) (type : ATyp)
  | Lstore (chunk : Chunk) (address : Addressing) (args : List MachineReg) (value : MachineReg)
  | Lcall (signature : Signature) (function : Sum MachineReg Ident)
  | Ltailcall (signature : Signature) (function : Sum MachineReg Ident)
  | Lbuiltin (function : ExtFun) (args : List BuiltinArg) (result : BuiltinRes)
  | Llabel (label : Label)
  | Lgoto (label : Label)
  | Lcond (condition : Condition) (args : List MachineReg) (target : Label)
  | Ljumptable (index : MachineReg) (table : List Label)
  | Lreturn
  deriving DecidableEq

/-- A function body is a list of instructions. -/
abbrev Code := List Instruction

/-- Finds the code following the first `Llabel label`, or `none` when the label is absent. -/
def findLabel (label : Label) : Code → Option Code
  | [] => none
  | .Llabel other :: rest => if label = other then some rest else findLabel label rest
  | _ :: rest => findLabel label rest

/-- An internal Linear function: signature, stack frame size in bytes, and body. -/
structure Function where
  fn_sig : Signature
  fn_stacksize : Int
  fn_code : Code

/-- A function definition is internal Linear code or an external function. -/
inductive Fundef where
  | Internal (function : Function)
  | External (function : ExtFun)

/-- The signature of a function definition, taken from the code or the external declaration. -/
def Fundef.signature : Fundef → Signature
  | .Internal f => f.fn_sig
  | .External f => f.sig

/-- A Linear program: global definitions, public symbols, and the entry symbol. -/
structure Program where
  prog_defs : List (Ident × GlobDef Fundef Unit)
  prog_public : List Ident
  prog_main : Ident

/-- Global environments mapping symbols and blocks to Linear function definitions. -/
abbrev Genv := CC.Genv Fundef Unit

/-- The global environment holding every definition of `program`. -/
def Program.globalenv (program : Program) : Genv :=
  CC.Genv.addGlobals (CC.Genv.emptyGenv program.prog_public) program.prog_defs

/-- Allocates every global of `program` in the empty memory, `none` if an allocation fails. -/
def Program.initMem (program : Program) : Option Mem :=
  CC.Genv.allocGlobals program.globalenv Mem.empty program.prog_defs

/-- A caller's saved frame: its function, stack pointer, locations, and continuation code. -/
structure Stackframe where
  caller : Function
  stack : Val
  locations : Locset
  continuation : Code

/-- Linear execution states: running inside a function, entering a call, or returning. -/
inductive State where
  | Running (frames : List Stackframe) (function : Function) (stack : Val)
      (instructions : Code) (locations : Locset) (memory : Mem)
  | Callstate (frames : List Stackframe) (function : Fundef) (locations : Locset) (memory : Mem)
  | Returnstate (frames : List Stackframe) (locations : Locset) (memory : Mem)

/-- The locations of the innermost caller, or the empty set when no frame remains. -/
def parentLocset : List Stackframe → Locset
  | [] => LTL.Locset.empty
  | frame :: _ => frame.locations

/-- Resolves a call target, a register holding a function pointer or a global symbol. -/
def findFunction (ge : Genv) (function : Sum MachineReg Ident) (locations : Locset) :
    Option Fundef :=
  match function with
  | .inl register => CC.Genv.findFunct ge (locations.reg register)
  | .inr symbol => do
      let block ← CC.Genv.findSymbol ge symbol
      CC.Genv.findFunctPtr ge block

/-- Evaluates an operation on argument values, as in LTL. -/
abbrev evalOperation := @LTL.evalOperation Fundef Unit
/-- Evaluates an addressing mode to a pointer, as in CminorSel. -/
abbrev evalAddressing := @CminorSel.evalAddressing Fundef Unit
/-- Evaluates a comparison condition to a Boolean, as in CminorSel. -/
abbrev evalCondition := CminorSel.evalCondition
/-- Registers clobbered by an operation on x86-64, as in LTL. -/
abbrev destroyedByOp := LTL.destroyedByOp
/-- Registers clobbered by reading a stack slot of the given kind, as in LTL. -/
abbrev destroyedByGetstack := LTL.destroyedByGetstack
/-- Registers clobbered by writing a stack slot of the given type, as in LTL. -/
abbrev destroyedBySetstack := LTL.destroyedBySetstack
/-- Registers clobbered by a builtin call, as in LTL. -/
abbrev destroyedByBuiltin := LTL.destroyedByBuiltin
/-- Locations after a return: callee-save registers and slots from the caller, the rest from
the callee, as in LTL. -/
abbrev returnRegs := LTL.returnRegs
/-- Locations at function entry: the caller's registers and outgoing slots as incoming ones,
as in LTL. -/
abbrev callRegs := LTL.callRegs
/-- The argument locations fixed by a signature under the x86-64 calling convention. -/
abbrev locArguments := LTL.locArguments
/-- The result register of a signature: `X0` for floats, `AX` otherwise. -/
abbrev locResult := LTL.locResult
/-- Sets every caller-save register and outgoing slot to `Vundef`, as in LTL. -/
abbrev undefCallerSaveRegs := LTL.undefCallerSaveRegs

/-- The relational evaluation of one builtin argument, as in LTL. -/
abbrev EvalBuiltinArg := @LTL.EvalBuiltinArg Fundef Unit
/-- The relational evaluation of a list of builtin arguments, as in LTL. -/
abbrev EvalBuiltinArgs := @LTL.EvalBuiltinArgs Fundef Unit
/-- The executable evaluation of one builtin argument, as in LTL. -/
abbrev evalBuiltinArg := @LTL.evalBuiltinArg Fundef Unit
/-- The executable evaluation of a list of builtin arguments, as in LTL. -/
abbrev evalBuiltinArgs := @LTL.evalBuiltinArgs Fundef Unit

end Quadrature.Linear
