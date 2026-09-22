import CCLib.Clight

/-!
# Typed C expressions before call extraction

`Expr`, `Exprlist` and `typeof` follow `cfrontend/Csyntax.v` of CompCert
(revision recorded in `Quadrature.Clight.Source`). Unlike Clight, this syntax
distinguishes a location (`Evar`, `Ederef`, `Efield`) from reading it
(`Evalof`) and permits calls, assignments and increments inside expressions.
These typed terms are distinct from the parser's untyped `CSource.Expr`:
`Quadrature.CSource.Frontend.Elaboration` maps the supported parsed syntax to them, and
`Quadrature.CSource.Frontend.TypedFunctions` checks the five original functions.
-/

namespace Quadrature.CSource.C

open CC

/-- The direction of a postfix `++` or `--`. -/
inductive IncrOrDecr where
  | incr
  | decr

mutual
/-- Typed C expressions, each constructor carrying its C type. `Eval v ty` is an already computed
value and `Eloc` an already computed location. `Eparen` is an intermediate term whose cast is
performed by the small-step semantics. -/
inductive Expr where
  | Eval (value : Val) (type : Ty)
  | Evar (name : Ident) (type : Ty)
  | Efield (arg : Expr) (field : Ident) (type : Ty)
  | Evalof (arg : Expr) (type : Ty)
  | Ederef (arg : Expr) (type : Ty)
  | Eaddrof (arg : Expr) (type : Ty)
  | Eunop (op : Unop) (arg : Expr) (type : Ty)
  | Ebinop (op : Binop) (left right : Expr) (type : Ty)
  | Ecast (arg : Expr) (type : Ty)
  | Eseqand (left right : Expr) (type : Ty)
  | Eseqor (left right : Expr) (type : Ty)
  | Econdition (test yes no : Expr) (type : Ty)
  | Esizeof (arg type : Ty)
  | Ealignof (arg type : Ty)
  | Eassign (left right : Expr) (type : Ty)
  | Eassignop (op : Binop) (left right : Expr) (resultType type : Ty)
  | Epostincr (op : IncrOrDecr) (arg : Expr) (type : Ty)
  | Ecomma (left right : Expr) (type : Ty)
  | Ecall (fn : Expr) (args : Exprlist) (type : Ty)
  | Ebuiltin (fn : ExtFun) (argTypes : List Ty) (args : Exprlist) (type : Ty)
  | Eloc (block : Block) (offset : Integers.Ptrofs) (field : Bitfield) (type : Ty)
  | Eparen (arg : Expr) (castType type : Ty)

/-- The argument list of a call. -/
inductive Exprlist where
  | Enil
  | Econs (head : Expr) (tail : Exprlist)
end

/-- The type annotation carried by an expression. -/
def typeof : Expr → Ty
  | .Eval _ ty | .Evar _ ty | .Efield _ _ ty | .Evalof _ ty
  | .Ederef _ ty | .Eaddrof _ ty | .Eunop _ _ ty | .Ebinop _ _ _ ty
  | .Ecast _ ty | .Eseqand _ _ ty | .Eseqor _ _ ty | .Econdition _ _ _ ty
  | .Esizeof _ ty | .Ealignof _ ty | .Eassign _ _ ty | .Eassignop _ _ _ _ ty
  | .Epostincr _ _ ty | .Ecomma _ _ ty | .Ecall _ _ ty | .Ebuiltin _ _ _ ty
  | .Eloc _ _ _ ty | .Eparen _ _ ty => ty

/-- The part of a global environment that simple expressions and memory accesses use: the symbol
environment and the composite environment. -/
structure ExpressionEnv where
  symbols : Senv
  composites : CompositeEnv

/-- The expression environment of a Clight `CGenv`, forgetting function bodies. -/
def ExpressionEnv.ofClight (ge : CGenv) : ExpressionEnv :=
  ⟨Genv.toSenv ge.genv_genv, ge.genv_cenv⟩

end Quadrature.CSource.C
