import Quadrature.Compiler.LTL.Locations
import Quadrature.Compiler.RTL.Syntax

/-!
# LTL syntax

Location-transfer syntax after `backend/LTL.v`: nodes contain basic blocks, operands are
machine registers or abstract stack slots, and calls pass values through the ELF64
calling convention. `Instruction` is the instruction set, and `Function` maps nodes to
basic blocks. Every instruction form is represented. Arithmetic uses the same operation
fragment as RTL.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.LTL

open CC

/-- CFG nodes, positive numbers. -/
abbrev Node := Positive
/-- RTL's `Operation`, reused. -/
abbrev Operation := RTL.Operation
/-- CminorSel's `Addressing`, reused. -/
abbrev Addressing := CminorSel.Addressing
/-- CminorSel's `Condition`, reused. -/
abbrev Condition := CminorSel.Condition

/-- Builtin arguments over locations: a location, a literal, a stack or global load or address, a
split 64-bit pair, or a pointer sum. -/
inductive BuiltinArg where
  | BA (location : Location)
  | BA_int (value : Integers.Int)
  | BA_long (value : Integers.Int64)
  | BA_float (value : Floats.Float)
  | BA_single (value : Floats.Float32)
  | BA_loadstack (chunk : Chunk) (offset : Integers.Ptrofs)
  | BA_addrstack (offset : Integers.Ptrofs)
  | BA_loadglobal (chunk : Chunk) (symbol : Ident) (offset : Integers.Ptrofs)
  | BA_addrglobal (symbol : Ident) (offset : Integers.Ptrofs)
  | BA_splitlong (hi lo : BuiltinArg)
  | BA_addptr (left right : BuiltinArg)
  deriving DecidableEq

/-- LTL instructions: operations, loads, slot reads and writes, stores, calls, tail calls,
builtins, branches, conditional branches, jump tables, and return. -/
inductive Instruction where
  | Lop (operation : Operation) (args : List MachineReg) (result : MachineReg)
  | Lload (chunk : Chunk) (address : Addressing) (args : List MachineReg) (result : MachineReg)
  | Lgetstack (slot : Slot) (offset : Int) (type : ATyp) (result : MachineReg)
  | Lsetstack (source : MachineReg) (slot : Slot) (offset : Int) (type : ATyp)
  | Lstore (chunk : Chunk) (address : Addressing) (args : List MachineReg) (value : MachineReg)
  | Lcall (signature : Signature) (function : Sum MachineReg Ident)
  | Ltailcall (signature : Signature) (function : Sum MachineReg Ident)
  | Lbuiltin (function : ExtFun) (args : List BuiltinArg) (result : BuiltinRes)
  | Lbranch (next : Node)
  | Lcond (condition : Condition) (args : List MachineReg) (yes no : Node)
  | Ljumptable (index : MachineReg) (table : List Node)
  | Lreturn
  deriving DecidableEq

/-- A basic block: a list of instructions ending in a control transfer. -/
abbrev BasicBlock := List Instruction
/-- Code mapping nodes to basic blocks. -/
abbrev Code := PTree BasicBlock

/-- Reconstruct the code from the exported bindings, preserving each numeric node. -/
def codeOfList (bindings : List (Node × BasicBlock)) : Code :=
  bindings.foldr (fun entry code => code.set entry.1 entry.2) PTree.empty

/-- An internal LTL function: signature, frame size, code, and entry node. -/
structure Function where
  fn_sig : Signature
  fn_stacksize : Int
  fn_code : Code
  fn_entrypoint : Node

/-- A function definition, either an internal `Function` or an external function. -/
inductive Fundef where
  | Internal (function : Function)
  | External (function : ExtFun)

/-- `Fundef.signature fd` is the signature of an internal or external function. -/
def Fundef.signature : Fundef → Signature
  | .Internal f => f.fn_sig
  | .External f => f.sig

/-- An LTL program: global definitions, public symbols, and the entry symbol. -/
structure Program where
  prog_defs : List (Ident × GlobDef Fundef Unit)
  prog_public : List Ident
  prog_main : Ident

/-- Global environments mapping symbols to blocks and blocks to function definitions. -/
abbrev Genv := CC.Genv Fundef Unit

/-- `Program.globalenv p` builds the global environment of `p` from its definitions. -/
def Program.globalenv (program : Program) : Genv :=
  CC.Genv.addGlobals (CC.Genv.emptyGenv program.prog_public) program.prog_defs

/-- `Program.initMem p` allocates and initializes every global of `p` in the empty memory. -/
def Program.initMem (program : Program) : Option Mem :=
  CC.Genv.allocGlobals program.globalenv Mem.empty program.prog_defs

/-- A pending caller: its function, stack pointer, location map, and the rest of its basic
block. -/
structure Stackframe where
  caller : Function
  stack : Val
  locations : Locset
  continuation : BasicBlock

/-- Execution states: at a node, inside a basic block (`State.Block` holds the instructions left
to run), calling a function, or returning to the pending frames. -/
inductive State where
  | Running (frames : List Stackframe) (function : Function) (stack : Val)
      (pc : Node) (locations : Locset) (memory : Mem)
  | Block (frames : List Stackframe) (function : Function) (stack : Val)
      (instructions : BasicBlock) (locations : Locset) (memory : Mem)
  | Callstate (frames : List Stackframe) (function : Fundef) (locations : Locset) (memory : Mem)
  | Returnstate (frames : List Stackframe) (locations : Locset) (memory : Mem)

/-- `parentLocset frames` is the caller's location map, or the empty map for the outermost
function. -/
def parentLocset : List Stackframe → Locset
  | [] => Locset.empty
  | frame :: _ => frame.locations

/-- `findFunction ge target ls` resolves a call target: a register holding a function pointer, or
a global symbol. -/
def findFunction (ge : Genv) (function : Sum MachineReg Ident) (locations : Locset) :
    Option Fundef :=
  match function with
  | .inl register => CC.Genv.findFunct ge (locations.reg register)
  | .inr symbol => do
      let block ← CC.Genv.findSymbol ge symbol
      CC.Genv.findFunctPtr ge block

/-- `evalOperation ge sp op vs` computes a register move or a selected operation on `vs`, or
fails. -/
def evalOperation {F V : Type} (ge : CC.Genv F V) (stack : Val) (operation : Operation)
    (values : List Val) : Option Val :=
  match operation, values with
  | .Omove, [value] => some value
  | .Omove, _ => none
  | .selected operation, _ => CminorSel.evalOperation ge stack operation values

/-- CminorSel's `evalAddressing`, reused at this stage's `Genv`. -/
abbrev evalAddressing := @CminorSel.evalAddressing Fundef Unit
/-- CminorSel's `evalCondition`, reused. -/
abbrev evalCondition := CminorSel.evalCondition

/-- `destroyedByOp op` lists the registers an operation clobbers on x86-64: `AX` and `DX` for
division and modulo, `CX` for `Oshrximm`. -/
def destroyedByOp : Operation → List MachineReg
  | .selected .Odiv | .selected .Omod => [.AX, .DX]
  | .selected (.Oshrximm _) => [.CX]
  | _ => []

end Quadrature.LTL
