import Quadrature.Compiler.LTL.Syntax

/-!
# Mach syntax after stack-frame layout

Mach syntax after CompCert's `backend/Mach.v`. Read `Instruction` first, the fourteen
instruction forms. Stack accesses use byte offsets in ordinary memory, the link and
return-address offsets are fields of each `Function`, and builtin arguments read machine
registers.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Mach

open CC

/-- Code labels are positive numbers, as in CompCert. -/
abbrev Label := Positive
/-- The x86-64 machine registers, shared with LTL. -/
abbrev MachineReg := LTL.MachineReg
/-- Builtin result registers, shared with LTL. -/
abbrev BuiltinRes := LTL.BuiltinRes
/-- The x86-64 arithmetic operations, shared with LTL. -/
abbrev Operation := LTL.Operation
/-- The x86-64 addressing modes, shared with LTL. -/
abbrev Addressing := LTL.Addressing
/-- Integer comparison conditions, shared with LTL. -/
abbrev Condition := LTL.Condition

/-- Builtin arguments after frame layout: registers, constants, stack and global loads and
addresses, split longs, and pointer sums, as in `backend/Mach.v`. -/
inductive BuiltinArg where
  | BA (register : MachineReg)
  | BA_int (value : Integers.Int)
  | BA_long (value : Integers.Int64)
  | BA_float (value : Floats.Float)
  | BA_single (value : Floats.Float32)
  | BA_loadstack (chunk : Chunk) (offset : Integers.Ptrofs)
  | BA_addrstack (offset : Integers.Ptrofs)
  | BA_loadglobal (chunk : Chunk) (name : Ident) (offset : Integers.Ptrofs)
  | BA_addrglobal (name : Ident) (offset : Integers.Ptrofs)
  | BA_splitlong (hi lo : BuiltinArg)
  | BA_addptr (left right : BuiltinArg)
  deriving DecidableEq

/-- The fourteen Mach instructions of `backend/Mach.v`. Stack slots become byte offsets, and
`Mgetparam` reads an argument from the caller's frame through the saved link. -/
inductive Instruction where
  | Mop (operation : Operation) (args : List MachineReg) (result : MachineReg)
  | Mload (chunk : Chunk) (address : Addressing) (args : List MachineReg) (result : MachineReg)
  | Mgetstack (offset : Integers.Ptrofs) (type : ATyp) (result : MachineReg)
  | Msetstack (source : MachineReg) (offset : Integers.Ptrofs) (type : ATyp)
  | Mgetparam (offset : Integers.Ptrofs) (type : ATyp) (result : MachineReg)
  | Mstore (chunk : Chunk) (address : Addressing) (args : List MachineReg) (value : MachineReg)
  | Mcall (signature : Signature) (function : Sum MachineReg Ident)
  | Mtailcall (signature : Signature) (function : Sum MachineReg Ident)
  | Mbuiltin (function : ExtFun) (args : List BuiltinArg) (result : BuiltinRes)
  | Mlabel (label : Label)
  | Mgoto (label : Label)
  | Mcond (condition : Condition) (args : List MachineReg) (target : Label)
  | Mjumptable (index : MachineReg) (table : List Label)
  | Mreturn
  deriving DecidableEq

/-- A function body is a list of instructions. -/
abbrev Code := List Instruction

/-- Finds the code following the first `Mlabel label`, or `none` when the label is absent. -/
def findLabel (label : Label) : Code → Option Code
  | [] => none
  | .Mlabel other :: rest => if label = other then some rest else findLabel label rest
  | _ :: rest => findLabel label rest

/-- An internal Mach function: signature, frame size in bytes, the frame offsets of the saved
link and return address, and the body. -/
structure Function where
  fn_sig : Signature
  fn_stacksize : Int
  fn_link_ofs : Integers.Ptrofs
  fn_retaddr_ofs : Integers.Ptrofs
  fn_code : Code
  deriving DecidableEq

/-- A function definition is internal Mach code or an external function. -/
inductive Fundef where
  | Internal (function : Function)
  | External (function : ExtFun)
  deriving DecidableEq

/-- A Mach program: global definitions, public symbols, and the entry symbol. -/
structure Program where
  prog_defs : List (Ident × GlobDef Fundef Unit)
  prog_public : List Ident
  prog_main : Ident

/-- Global environments mapping symbols and blocks to Mach function definitions. -/
abbrev Genv := CC.Genv Fundef Unit

/-- The global environment holding every definition of `program`. -/
def Program.globalenv (program : Program) : Genv :=
  CC.Genv.addGlobals (CC.Genv.emptyGenv program.prog_public) program.prog_defs

/-- Allocates every global of `program` in the empty memory, `none` if an allocation fails. -/
def Program.initMem (program : Program) : Option Mem :=
  CC.Genv.allocGlobals program.globalenv Mem.empty program.prog_defs

end Quadrature.Mach
