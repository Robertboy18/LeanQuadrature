import Quadrature.CSource.Semantics.Syntax

/-!
# C statement and function syntax

`Stmt`, `LabeledStatements` and `Function` follow `cfrontend/Csyntax.v` of
CompCert (revision recorded in `Quadrature.Clight.Source`). `Sfor` keeps its
initializer, condition, increment and body, and `Sdo` keeps an expression
statement with its side effects. Execution is defined in
`Quadrature.CSource.Semantics.Strategy`.
-/

namespace Quadrature.CSource.C

open CC

mutual
/-- C statements. `Sdo a` evaluates `a` for its effects, `Sfor init test incr body` is the
three-clause loop, and `Sswitch` carries its labeled cases. -/
inductive Stmt where
  | Sskip
  | Sdo (value : Expr)
  | Ssequence (first second : Stmt)
  | Sifthenelse (test : Expr) (yes no : Stmt)
  | Swhile (test : Expr) (body : Stmt)
  | Sdowhile (test : Expr) (body : Stmt)
  | Sfor (initial : Stmt) (test : Expr) (increment body : Stmt)
  | Sbreak
  | Scontinue
  | Sreturn (value : Option Expr)
  | Sswitch (value : Expr) (cases : LabeledStatements)
  | Slabel (name : Ident) (body : Stmt)
  | Sgoto (name : Ident)

/-- The cases of a `switch`: each carries an optional integer label (`none` for `default`) and a
body. -/
inductive LabeledStatements where
  | LSnil
  | LScons (value : Option Int) (body : Stmt) (rest : LabeledStatements)
end

/-- A C function: return type, calling convention, parameters, local variables and body. There is
no temporary list, since every local lives in memory. -/
structure Function where
  fn_return : Ty
  fn_callconv : CallConv
  fn_params : List (Ident × Ty)
  fn_vars : List (Ident × Ty)
  fn_body : Stmt

end Quadrature.CSource.C
