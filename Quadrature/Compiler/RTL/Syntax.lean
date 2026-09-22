import Quadrature.Compiler.CminorSel.Operations

/-!
# RTL syntax

Register-transfer syntax after `backend/RTL.v`: instructions, CFG nodes,
pseudo-registers, and call frames. `Instruction` is the instruction set, and `Function`
holds a control-flow graph `fn_code` with an entry node. The operation fragment reuses
the selected arithmetic and adds register moves. Every instruction form is represented,
and `scripts/import-rtl.py` rejects other arithmetic and condition constructors.

Code is stored in CLean's finite trees. Register files are total maps with an
undefined default, as in CompCert.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.RTL

open CC

/-- Pseudo-registers, positive numbers. -/
abbrev Reg := Positive
/-- CFG nodes, positive numbers. -/
abbrev Node := Positive
/-- CminorSel's `Addressing`, reused. -/
abbrev Addressing := CminorSel.Addressing
/-- CminorSel's `Condition`, reused. -/
abbrev Condition := CminorSel.Condition
/-- CminorSel's `BuiltinRes`, reused. -/
abbrev BuiltinRes := CminorSel.BuiltinRes

/-- RTL operations: a register move or one of the selected x86-64 operations. -/
inductive Operation where
  | Omove
  | selected (operation : CminorSel.Operation)
  deriving DecidableEq

/-- Builtin arguments over registers: a register, a literal, a stack or global load or address, a
split 64-bit pair, or a pointer sum. -/
inductive BuiltinArg where
  | BA (register : Reg)
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

/-- RTL instructions: no-op, operation, load, store, call, tail call, builtin, conditional branch,
jump table, and return, each naming its successor nodes. -/
inductive Instruction where
  | Inop (next : Node)
  | Iop (operation : Operation) (args : List Reg) (result : Reg) (next : Node)
  | Iload (chunk : Chunk) (address : Addressing) (args : List Reg) (result : Reg) (next : Node)
  | Istore (chunk : Chunk) (address : Addressing) (args : List Reg) (value : Reg) (next : Node)
  | Icall (signature : Signature) (function : Sum Reg Ident) (args : List Reg)
      (result : Reg) (next : Node)
  | Itailcall (signature : Signature) (function : Sum Reg Ident) (args : List Reg)
  | Ibuiltin (function : ExtFun) (args : List BuiltinArg) (result : BuiltinRes) (next : Node)
  | Icond (condition : Condition) (args : List Reg) (yes no : Node)
  | Ijumptable (index : Reg) (table : List Node)
  | Ireturn (result : Option Reg)
  deriving DecidableEq

/-- Control-flow graphs mapping nodes to instructions. -/
abbrev Code := PTree Instruction

/-- Reconstruct a CFG from the exported bindings, preserving each numeric node. -/
def codeOfList (bindings : List (Node × Instruction)) : Code :=
  bindings.foldr (fun entry code => code.set entry.1 entry.2) PTree.empty

/-- An internal RTL function: signature, parameter registers, frame size, code, and entry node. -/
structure Function where
  fn_sig : Signature
  fn_params : List Reg
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

/-- An RTL program: global definitions, public symbols, and the entry symbol. -/
structure Program where
  prog_defs : List (Ident × GlobDef Fundef Unit)
  prog_public : List Ident
  prog_main : Ident

/-- Global environments mapping symbols to blocks and blocks to function definitions. -/
abbrev Genv := CC.Genv Fundef Unit
/-- Register files: total maps from registers to values. -/
abbrev Regset := PMap Val

/-- `Regset.get rs r` reads register `r`. -/
def Regset.get (registers : Regset) (register : Reg) : Val :=
  PMap.get register registers

/-- `Regset.set rs r v` writes `v` to register `r`. -/
def Regset.set (registers : Regset) (register : Reg) (value : Val) : Regset :=
  PMap.set register value registers

/-- `Regset.values rs args` reads the registers `args` in order. -/
def Regset.values (registers : Regset) (args : List Reg) : List Val :=
  args.map registers.get

/-- `Regset.optget rs r` reads an optional register, giving `Vundef` when there is none. -/
def Regset.optget (registers : Regset) (register : Option Reg) : Val :=
  match register with
  | none => .Vundef
  | some r => registers.get r

/-- `Regset.setResult rs res v` writes `v` to the register of a `BR` builtin result and leaves `rs`
unchanged otherwise. -/
def Regset.setResult (registers : Regset) (result : BuiltinRes) (value : Val) : Regset :=
  match result with
  | .BR r => registers.set r value
  | _ => registers

/-- `initRegs vs params` binds each parameter register to its argument, leaving every other
register `Vundef`. An exhausted argument or parameter list ends the binding. -/
def initRegs : List Val → List Reg → Regset
  | value :: values, register :: registers => (initRegs values registers).set register value
  | _, _ => PMap.init .Vundef

/-- `Program.globalenv p` builds the global environment of `p` from its definitions. -/
def Program.globalenv (program : Program) : Genv :=
  CC.Genv.addGlobals (CC.Genv.emptyGenv program.prog_public) program.prog_defs

/-- `Program.initMem p` allocates and initializes every global of `p` in the empty memory. -/
def Program.initMem (program : Program) : Option Mem :=
  CC.Genv.allocGlobals program.globalenv Mem.empty program.prog_defs

/-- A pending caller: its result register, function, stack pointer, return node, and register
file. -/
structure Stackframe where
  result : Reg
  caller : Function
  stack : Val
  next : Node
  registers : Regset

/-- Execution states: running at a CFG node, calling a function, or returning a value to the
pending frames. -/
inductive State where
  | Running (frames : List Stackframe) (function : Function) (stack : Val)
      (pc : Node) (registers : Regset) (memory : Mem)
  | Callstate (frames : List Stackframe) (function : Fundef) (args : List Val) (memory : Mem)
  | Returnstate (frames : List Stackframe) (value : Val) (memory : Mem)

/-- `findFunction ge target rs` resolves a call target: a register holding a function pointer, or
a global symbol. -/
def findFunction (ge : Genv) (function : Sum Reg Ident) (registers : Regset) : Option Fundef :=
  match function with
  | .inl register => CC.Genv.findFunct ge (registers.get register)
  | .inr symbol => do
      let block ← CC.Genv.findSymbol ge symbol
      CC.Genv.findFunctPtr ge block

/-- `evalOperation ge sp op vs` computes a register move or a selected operation on `vs`, or
fails. -/
def evalOperation (ge : Genv) (stack : Val) (operation : Operation)
    (values : List Val) : Option Val :=
  match operation, values with
  | .Omove, [value] => some value
  | .Omove, _ => none
  | .selected operation, _ => CminorSel.evalOperation ge stack operation values

/-- CminorSel's `evalAddressing`, reused at this stage's `Genv`. -/
abbrev evalAddressing := @CminorSel.evalAddressing Fundef Unit
/-- CminorSel's `evalCondition`, reused. -/
abbrev evalCondition := CminorSel.evalCondition

end Quadrature.RTL
