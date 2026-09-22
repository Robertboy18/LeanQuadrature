import CCLib.Events

/-!
# Cminor syntax

Abstract syntax of Cminor, after `backend/Cminor.v` at CompCert revision
`7b1f02b09954b9b916eb2a91d283c9b5355bf172`. `Stmt` is the statement language, and
`Program` is a list of global definitions with an entry symbol. Values and memory come
from this project's FloatLib adaptation of CLean.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Cminor

open CC

/-- Constant expressions: integer, float, single, and long literals, and symbol or stack
addresses. -/
inductive Constant where
  | Ointconst (value : Integers.Int)
  | Ofloatconst (value : Floats.Float)
  | Osingleconst (value : Floats.Float32)
  | Olongconst (value : Integers.Int64)
  | Oaddrsymbol (symbol : Ident) (offset : Integers.Ptrofs)
  | Oaddrstack (offset : Integers.Ptrofs)
  deriving DecidableEq

/-- Unary operators of Cminor: casts, negations, absolute values, and numeric conversions. -/
inductive UnaryOp where
  | Ocast8unsigned | Ocast8signed | Ocast16unsigned | Ocast16signed
  | Onegint | Onotint | Onegf | Oabsf | Onegfs | Oabsfs
  | Osingleoffloat | Ofloatofsingle | Ointoffloat | Ointuoffloat
  | Ofloatofint | Ofloatofintu | Ointofsingle | Ointuofsingle
  | Osingleofint | Osingleofintu | Onegl | Onotl
  | Ointoflong | Olongofint | Olongofintu | Olongoffloat | Olonguoffloat
  | Ofloatoflong | Ofloatoflongu | Olongofsingle | Olonguofsingle
  | Osingleoflong | Osingleoflongu
  deriving DecidableEq

/-- Binary operators of Cminor: integer, long, and float arithmetic, shifts, and comparisons. -/
inductive BinaryOp where
  | Oadd | Osub | Omul | Odiv | Odivu | Omod | Omodu
  | Oand | Oor | Oxor | Oshl | Oshr | Oshru
  | Oaddf | Osubf | Omulf | Odivf | Oaddfs | Osubfs | Omulfs | Odivfs
  | Oaddl | Osubl | Omull | Odivl | Odivlu | Omodl | Omodlu
  | Oandl | Oorl | Oxorl | Oshll | Oshrl | Oshrlu
  | Ocmp (comparison : Comparison)
  | Ocmpu (comparison : Comparison)
  | Ocmpf (comparison : Comparison)
  | Ocmpfs (comparison : Comparison)
  | Ocmpl (comparison : Comparison)
  | Ocmplu (comparison : Comparison)
  deriving DecidableEq

/-- Cminor expressions: variables, constants, unary and binary operations, and memory loads. -/
inductive Expr where
  | Evar (name : Ident)
  | Econst (constant : Constant)
  | Eunop (op : UnaryOp) (arg : Expr)
  | Ebinop (op : BinaryOp) (left right : Expr)
  | Eload (chunk : Chunk) (address : Expr)
  deriving DecidableEq

/-- Cminor statements: assignments, stores, calls, builtins, structured control flow through
`Sblock` and `Sexit`, loops, switches, returns, labels, and gotos. -/
inductive Stmt where
  | Sskip
  | Sassign (name : Ident) (value : Expr)
  | Sstore (chunk : Chunk) (address value : Expr)
  | Scall (result : Option Ident) (signature : Signature) (function : Expr) (args : List Expr)
  | Stailcall (signature : Signature) (function : Expr) (args : List Expr)
  | Sbuiltin (result : Option Ident) (function : ExtFun) (args : List Expr)
  | Sseq (first second : Stmt)
  | Sifthenelse (condition : Expr) (yes no : Stmt)
  | Sloop (body : Stmt)
  | Sblock (body : Stmt)
  | Sexit (depth : Nat)
  | Sswitch (isLong : Bool) (arg : Expr) (cases : List (Int × Nat)) (fallback : Nat)
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

/-- A Cminor program: global definitions, public symbols, and the entry symbol. -/
structure Program where
  prog_defs : List (Ident × GlobDef Fundef Unit)
  prog_public : List Ident
  prog_main : Ident

/-- Global environments mapping symbols to blocks and blocks to function definitions. -/
abbrev Genv := CC.Genv Fundef Unit
/-- Local environments mapping identifiers to values. -/
abbrev Env := PTree Val

/-- `Program.globalenv p` builds the global environment of `p` from its definitions. -/
def Program.globalenv (program : Program) : Genv :=
  CC.Genv.addGlobals (CC.Genv.emptyGenv program.prog_public) program.prog_defs

/-- `Program.initMem p` allocates and initializes every global of `p` in the empty memory. -/
def Program.initMem (program : Program) : Option Mem :=
  CC.Genv.allocGlobals program.globalenv Mem.empty program.prog_defs

/-- `setParams vs names` binds each parameter name to the corresponding argument value, and
names without a value to `Vundef`. -/
def setParams : List Val → List Ident → Env
  | value :: values, name :: names => (setParams values names).set name value
  | [], name :: names => (setParams [] names).set name .Vundef
  | _, [] => PTree.empty

/-- `setLocals names env` binds each local variable to `Vundef` in `env`. -/
def setLocals : List Ident → Env → Env
  | [], env => env
  | name :: names, env => (setLocals names env).set name .Vundef

/-- `setOptvar dst v env` assigns `v` to `dst` when a destination is given, and leaves `env`
unchanged otherwise. -/
def setOptvar (name : Option Ident) (value : Val) (env : Env) : Env :=
  match name with
  | none => env
  | some name => env.set name value

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

/-- `switchTarget n fallback cases` is the exit depth of the first case with key `n`, or
`fallback` when no case matches. -/
def switchTarget (value : Int) (fallback : Nat) : List (Int × Nat) → Nat
  | [] => fallback
  | (key, target) :: rest => if value = key then target else switchTarget value fallback rest

end Quadrature.Cminor
