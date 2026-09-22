import Quadrature.Compiler.Cminor.Syntax

/-!
# CminorSel syntax

Abstract syntax after instruction selection, after `backend/CminorSel.v` and `x86/Op.v`
at CompCert revision `7b1f02b09954b9b916eb2a91d283c9b5355bf172`. `Expr` is the
expression language, with `Operation` and `Addressing` from the x86-64 backend, and
`Stmt` is the statement language. Values and memory come from the FloatLib adaptation
of CLean.

`Operation` and `Condition` contain only the constructors that occur in the ten
programs, including their unused library functions. Expressions exclude effectful
builtin and external calls, and statement calls remain available.
`scripts/import-cminorsel.py` rejects other constructors.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.CminorSel

open CC

/-- Conditions of the x86-64 backend used by the ten programs: signed integer comparison of two
registers or of a register and an immediate. -/
inductive Condition where
  | Ccomp (comparison : Comparison)
  | Ccompimm (comparison : Comparison) (value : Integers.Int)
  deriving DecidableEq

/-- x86-64 addressing modes: indexed, scaled, global-relative, and stack-relative addresses. -/
inductive Addressing where
  | Aindexed (offset : Int)
  | Aindexed2 (offset : Int)
  | Ascaled (scale offset : Int)
  | Aindexed2scaled (scale offset : Int)
  | Aglobal (symbol : Ident) (offset : Integers.Ptrofs)
  | Abased (symbol : Ident) (offset : Integers.Ptrofs)
  | Abasedscaled (scale : Int) (symbol : Ident) (offset : Integers.Ptrofs)
  | Ainstack (offset : Integers.Ptrofs)
  deriving DecidableEq

/-- x86-64 operations used by the ten programs: constants, integer multiply, divide, modulo, and
shift, address computations `Olea` and `Oleal`, sign extension, and binary64 arithmetic. -/
inductive Operation where
  | Ointconst (value : Integers.Int)
  | Ofloatconst (value : Floats.Float)
  | Omul | Odiv | Omod
  | Oshrximm (amount : Integers.Int)
  | Olea (addressing : Addressing)
  | Ocast32signed
  | Oleal (addressing : Addressing)
  | Oaddf | Osubf | Omulf | Odivf
  deriving DecidableEq

mutual
/-- CminorSel expressions: variables, operations, loads, conditionals, and let bindings addressed
by de Bruijn index. -/
inductive Expr where
  | Evar (name : Ident)
  | Eop (operation : Operation) (args : ExprList)
  | Eload (chunk : Chunk) (addressing : Addressing) (args : ExprList)
  | Econdition (condition : CondExpr) (yes no : Expr)
  | Elet (value body : Expr)
  | Eletvar (index : Nat)
  deriving DecidableEq

/-- Argument lists of CminorSel expressions. -/
inductive ExprList where
  | Enil
  | Econs (head : Expr) (tail : ExprList)
  deriving DecidableEq

/-- Conditional expressions: a condition on arguments, a nested conditional, or a let binding. -/
inductive CondExpr where
  | CEcond (condition : Condition) (args : ExprList)
  | CEcondition (condition yes no : CondExpr)
  | CElet (value : Expr) (body : CondExpr)
  deriving DecidableEq
end

/-- Exit expressions of switches: a fixed depth, a jump table, a conditional, or a let binding. -/
inductive ExitExpr where
  | XEexit (depth : Nat)
  | XEjumptable (index : Expr) (table : List Nat)
  | XEcondition (condition : CondExpr) (yes no : ExitExpr)
  | XElet (value : Expr) (body : ExitExpr)
  deriving DecidableEq

/-- Builtin arguments: an expression, a literal, a stack or global load or address, a split
64-bit pair, or a pointer sum. -/
inductive BuiltinArg where
  | BA (value : Expr)
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

/-- Builtin results: a variable, no result, or a split 64-bit pair. -/
inductive BuiltinRes where
  | BR (name : Ident)
  | BR_none
  | BR_splitlong (hi lo : BuiltinRes)
  deriving DecidableEq

/-- CminorSel statements, with stores through an addressing mode, calls to an expression or a
symbol, and switches through `ExitExpr`. -/
inductive Stmt where
  | Sskip
  | Sassign (name : Ident) (value : Expr)
  | Sstore (chunk : Chunk) (addressing : Addressing) (args : ExprList) (value : Expr)
  | Scall (result : Option Ident) (signature : Signature) (function : Sum Expr Ident)
      (args : ExprList)
  | Stailcall (signature : Signature) (function : Sum Expr Ident) (args : ExprList)
  | Sbuiltin (result : BuiltinRes) (function : ExtFun) (args : List BuiltinArg)
  | Sseq (first second : Stmt)
  | Sifthenelse (condition : CondExpr) (yes no : Stmt)
  | Sloop (body : Stmt)
  | Sblock (body : Stmt)
  | Sexit (depth : Nat)
  | Sswitch (value : ExitExpr)
  | Sreturn (value : Option Expr)
  | Slabel (label : Ident) (body : Stmt)
  | Sgoto (label : Ident)
  deriving DecidableEq

/-- An internal function: signature, parameters, local variables, stack-frame size, and body. -/
structure Function where
  fn_sig : Signature
  fn_params : List Ident
  fn_vars : List Ident
  fn_stackspace : Int
  fn_body : Stmt
  deriving DecidableEq

/-- A function definition, either an internal `Function` or an external function. -/
inductive Fundef where
  | Internal (function : Function)
  | External (function : ExtFun)
  deriving DecidableEq

/-- `Fundef.signature fd` is the signature of an internal or external function. -/
def Fundef.signature : Fundef → Signature
  | .Internal f => f.fn_sig
  | .External f => f.sig

/-- A CminorSel program: global definitions, public symbols, and the entry symbol. -/
structure Program where
  prog_defs : List (Ident × GlobDef Fundef Unit)
  prog_public : List Ident
  prog_main : Ident

/-- Global environments mapping symbols to blocks and blocks to function definitions. -/
abbrev Genv := CC.Genv Fundef Unit
/-- Local environments, Cminor's `Env`. -/
abbrev Env := Cminor.Env
/-- Let-bound values, indexed by de Bruijn position with the innermost binding first. -/
abbrev LetEnv := List Val
/-- Cminor's `setParams`, reused. -/
abbrev setParams := Cminor.setParams
/-- Cminor's `setLocals`, reused. -/
abbrev setLocals := Cminor.setLocals
/-- Cminor's `setOptvar`, reused. -/
abbrev setOptvar := Cminor.setOptvar

/-- `Program.globalenv p` builds the global environment of `p` from its definitions. -/
def Program.globalenv (program : Program) : Genv :=
  CC.Genv.addGlobals (CC.Genv.emptyGenv program.prog_public) program.prog_defs

/-- `Program.initMem p` allocates and initializes every global of `p` in the empty memory. -/
def Program.initMem (program : Program) : Option Mem :=
  CC.Genv.allocGlobals program.globalenv Mem.empty program.prog_defs

/-- `setBuiltinRes res v env` assigns `v` to the variable of a `BR` result and leaves `env`
unchanged for `BR_none` and split results. -/
def setBuiltinRes (result : BuiltinRes) (value : Val) (env : Env) : Env :=
  match result with
  | .BR name => env.set name value
  | _ => env

/-- Continuations: stop, a pending statement, an enclosing block, or a pending caller frame. -/
inductive Cont where
  | Kstop
  | Kseq (statement : Stmt) (continuation : Cont)
  | Kblock (continuation : Cont)
  | Kcall (result : Option Ident) (caller : Function) (stack : Val)
      (env : Env) (continuation : Cont)

/-- Execution states: running a statement, calling a function, or returning a value. -/
inductive State where
  | Running (function : Function) (statement : Stmt) (continuation : Cont)
      (stack : Val) (env : Env) (memory : Mem)
  | Callstate (function : Fundef) (args : List Val) (continuation : Cont) (memory : Mem)
  | Returnstate (value : Val) (continuation : Cont) (memory : Mem)

/-- `callCont k` strips `Kseq` and `Kblock` frames from `k`, leaving the enclosing call or stop
continuation. -/
def callCont : Cont → Cont
  | .Kseq _ k | .Kblock k => callCont k
  | k => k

/-- `IsCallCont k` holds when `k` is `Kstop` or a `Kcall` frame. -/
def IsCallCont : Cont → Prop
  | .Kstop | .Kcall .. => True
  | _ => False

/-- `IsCallCont` is decidable by case analysis on the continuation. -/
instance (k : Cont) : Decidable (IsCallCont k) := by
  cases k <;> unfold IsCallCont <;> infer_instance

/-- `findLabel lbl s k` finds the statement labelled `lbl` inside `s` together with the
continuation in force there, or returns `none`. -/
def findLabel (label : Ident) : Stmt → Cont → Option (Stmt × Cont)
  | .Sseq first second, k =>
      (findLabel label first (.Kseq second k)).orElse fun _ => findLabel label second k
  | .Sifthenelse _ yes no, k =>
      (findLabel label yes k).orElse fun _ => findLabel label no k
  | .Sloop body, k => findLabel label body (.Kseq (.Sloop body) k)
  | .Sblock body, k => findLabel label body (.Kblock k)
  | .Slabel name body, k =>
      if label = name then some (body, k) else findLabel label body k
  | _, _ => none

end Quadrature.CminorSel
