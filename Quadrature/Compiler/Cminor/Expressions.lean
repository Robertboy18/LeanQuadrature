import Quadrature.Compiler.Cminor.Syntax

/-!
# Cminor expression evaluation

Relational and executable evaluation of Cminor expressions, after `backend/Cminor.v`
at the revision recorded in `Syntax.lean`. `EvalExpr ge sp e m a v` says the expression
`a` evaluates to `v`, and `evalExpr` computes that value. `eval_expr_iff` shows the two
agree. Both use the CLean value and memory operations.

An undefined long comparison fails, whereas an undefined 32-bit comparison produces
`Vundef`. Single-precision conversions use the binary32 operations directly.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Cminor

open CC

/-- `evalConstant ge sp c` is the value of the constant `c`, resolving symbol addresses in `ge`
and stack addresses relative to `sp`. -/
def evalConstant (ge : Genv) (stack : Val) : Constant → Option Val
  | .Ointconst value => some (.Vint value)
  | .Ofloatconst value => some (.Vfloat value)
  | .Osingleconst value => some (.Vsingle value)
  | .Olongconst value => some (.Vlong value)
  | .Oaddrsymbol symbol offset => some (CC.Genv.symbolAddress ge symbol offset)
  | .Oaddrstack offset => some (Val.offsetPtr stack offset)

/-- `evalUnary op v` applies the unary operator `op` to `v`, failing where CompCert's `eval_unop`
fails, for example on out-of-range float-to-integer conversions. -/
def evalUnary : UnaryOp → Val → Option Val
  | .Ocast8unsigned, value => some (Val.zeroExt 8 value)
  | .Ocast8signed, value => some (Val.signExt 8 value)
  | .Ocast16unsigned, value => some (Val.zeroExt 16 value)
  | .Ocast16signed, value => some (Val.signExt 16 value)
  | .Onegint, value => some (Val.neg value)
  | .Onotint, value => some (Val.notint value)
  | .Onegf, value => some (Val.negf value)
  | .Oabsf, value => some (Val.absf value)
  | .Onegfs, value => some (Val.negfs value)
  | .Oabsfs, value => some (Val.absfs value)
  | .Osingleoffloat, value => some (Val.singleoffloat value)
  | .Ofloatofsingle, value => some (Val.floatofsingle value)
  | .Ointoffloat, value => Val.intoffloat value
  | .Ointuoffloat, value => Val.intuoffloat value
  | .Ofloatofint, value => Val.floatofint value
  | .Ofloatofintu, value => Val.floatofintu value
  | .Ointofsingle, .Vsingle value => (Floats.Float32.toInt value).map Val.Vint
  | .Ointuofsingle, .Vsingle value => (Floats.Float32.toIntu value).map Val.Vint
  | .Osingleofint, .Vint value => some (.Vsingle (Floats.Float32.ofInt value))
  | .Osingleofintu, .Vint value => some (.Vsingle (Floats.Float32.ofIntu value))
  | .Onegl, value => some (Val.negl value)
  | .Onotl, value => some (Val.notl value)
  | .Ointoflong, value => some (Val.loword value)
  | .Olongofint, value => some (Val.longofint value)
  | .Olongofintu, value => some (Val.longofintu value)
  | .Olongoffloat, value => Val.longoffloat value
  | .Olonguoffloat, value => Val.longuoffloat value
  | .Ofloatoflong, value => Val.floatoflong value
  | .Ofloatoflongu, value => Val.floatoflongu value
  | .Olongofsingle, .Vsingle value => (Floats.Float32.toLong value).map Val.Vlong
  | .Olonguofsingle, .Vsingle value => (Floats.Float32.toLongu value).map Val.Vlong
  | .Osingleoflong, .Vlong value => some (.Vsingle (Floats.Float32.ofLong value))
  | .Osingleoflongu, .Vlong value => some (.Vsingle (Floats.Float32.ofLongu value))
  | _, _ => none

/-- `evalBinary op v1 v2 m` applies the binary operator `op`, failing on division by zero and on
undefined long comparisons. Unsigned comparisons consult `m` for pointer validity. -/
def evalBinary (op : BinaryOp) (left right : Val) (memory : Mem) : Option Val :=
  match op with
  | .Oadd => some (Val.add left right)
  | .Osub => some (Val.sub left right)
  | .Omul => some (Val.mul left right)
  | .Odiv => Val.divs left right
  | .Odivu => Val.divu left right
  | .Omod => Val.mods left right
  | .Omodu => Val.modu left right
  | .Oand => some (Val.and left right)
  | .Oor => some (Val.or left right)
  | .Oxor => some (Val.xor left right)
  | .Oshl => some (Val.shl left right)
  | .Oshr => some (Val.shr left right)
  | .Oshru => some (Val.shru left right)
  | .Oaddf => some (Val.addf left right)
  | .Osubf => some (Val.subf left right)
  | .Omulf => some (Val.mulf left right)
  | .Odivf => some (Val.divf left right)
  | .Oaddfs => some (Val.addfs left right)
  | .Osubfs => some (Val.subfs left right)
  | .Omulfs => some (Val.mulfs left right)
  | .Odivfs => some (Val.divfs left right)
  | .Oaddl => some (Val.addl left right)
  | .Osubl => some (Val.subl left right)
  | .Omull => some (Val.mull left right)
  | .Odivl => Val.divls left right
  | .Odivlu => Val.divlu left right
  | .Omodl => Val.modls left right
  | .Omodlu => Val.modlu left right
  | .Oandl => some (Val.andl left right)
  | .Oorl => some (Val.orl left right)
  | .Oxorl => some (Val.xorl left right)
  | .Oshll => some (Val.shll left right)
  | .Oshrl => some (Val.shrl left right)
  | .Oshrlu => some (Val.shrlu left right)
  | .Ocmp comparison => some (Val.cmp comparison left right)
  | .Ocmpu comparison =>
      some (Val.ofOptbool (Val.cmpu_bool (Mem.validPointer memory) comparison left right))
  | .Ocmpf comparison => some (Val.cmpf comparison left right)
  | .Ocmpfs comparison => some (Val.cmpfs comparison left right)
  | .Ocmpl comparison => (Val.cmpl_bool comparison left right).map Val.ofBool
  | .Ocmplu comparison =>
      (Val.cmplu_bool (Mem.validPointer memory) comparison left right).map Val.ofBool

/-- `EvalExpr ge sp e m a v` says the expression `a` evaluates to `v` with stack pointer `sp`,
local environment `e`, and memory `m`. -/
inductive EvalExpr (ge : Genv) (stack : Val) (env : Env) (memory : Mem) :
    Expr → Val → Prop where
  | var (name : Ident) (value : Val) :
      env.get name = some value → EvalExpr ge stack env memory (.Evar name) value
  | constant (constant : Constant) (value : Val) :
      evalConstant ge stack constant = some value →
      EvalExpr ge stack env memory (.Econst constant) value
  | unary (op : UnaryOp) (arg : Expr) (input value : Val) :
      EvalExpr ge stack env memory arg input →
      evalUnary op input = some value →
      EvalExpr ge stack env memory (.Eunop op arg) value
  | binary (op : BinaryOp) (left right : Expr) (vleft vright value : Val) :
      EvalExpr ge stack env memory left vleft →
      EvalExpr ge stack env memory right vright →
      evalBinary op vleft vright memory = some value →
      EvalExpr ge stack env memory (.Ebinop op left right) value
  | load (chunk : Chunk) (address : Expr) (pointer value : Val) :
      EvalExpr ge stack env memory address pointer →
      Mem.loadv chunk memory pointer = some value →
      EvalExpr ge stack env memory (.Eload chunk address) value

/-- `EvalExprList ge sp e m as vs` evaluates the expressions `as` pointwise to the values `vs`. -/
inductive EvalExprList (ge : Genv) (stack : Val) (env : Env) (memory : Mem) :
    List Expr → List Val → Prop where
  | nil : EvalExprList ge stack env memory [] []
  | cons (arg : Expr) (args : List Expr) (value : Val) (values : List Val) :
      EvalExpr ge stack env memory arg value →
      EvalExprList ge stack env memory args values →
      EvalExprList ge stack env memory (arg :: args) (value :: values)

/-- `evalExpr ge sp e m a` computes the value of `a`, or `none` when a variable is unbound or an
operation or load fails. -/
def evalExpr (ge : Genv) (stack : Val) (env : Env) (memory : Mem) : Expr → Option Val
  | .Evar name => env.get name
  | .Econst constant => evalConstant ge stack constant
  | .Eunop op arg => do
      let input ← evalExpr ge stack env memory arg
      evalUnary op input
  | .Ebinop op left right => do
      let vleft ← evalExpr ge stack env memory left
      let vright ← evalExpr ge stack env memory right
      evalBinary op vleft vright memory
  | .Eload chunk address => do
      let pointer ← evalExpr ge stack env memory address
      Mem.loadv chunk memory pointer

/-- `evalExprList ge sp e m as` computes the values of `as` in order, failing if any fails. -/
def evalExprList (ge : Genv) (stack : Val) (env : Env) (memory : Mem) :
    List Expr → Option (List Val)
  | [] => some []
  | arg :: args => do
      let value ← evalExpr ge stack env memory arg
      let values ← evalExprList ge stack env memory args
      pure (value :: values)

variable {ge : Genv} {stack : Val} {env : Env} {memory : Mem}
  {expr : Expr} {value : Val} {args : List Expr} {values : List Val}

/-- If `EvalExpr ge sp e m a v` holds, then `evalExpr ge sp e m a` returns `some v`. -/
theorem eval_expr_complete (h : EvalExpr ge stack env memory expr value) :
    evalExpr ge stack env memory expr = some value := by
  induction h with
  | var _ _ h => exact h
  | constant _ _ h => exact h
  | unary _ _ _ _ _ h ih => simp [evalExpr, ih, h]
  | binary _ _ _ _ _ _ _ _ h ihleft ihright => simp [evalExpr, ihleft, ihright, h]
  | load _ _ _ _ _ h ih => simp [evalExpr, ih, h]

/-- If `evalExpr ge sp e m a` returns `some v`, then `EvalExpr ge sp e m a v` holds. -/
theorem eval_expr_sound (h : evalExpr ge stack env memory expr = some value) :
    EvalExpr ge stack env memory expr value := by
  induction expr generalizing value with
  | Evar name => exact .var name value h
  | Econst constant => exact .constant constant value h
  | Eunop op arg ih =>
      simp only [evalExpr, bind, Option.bind_eq_some_iff] at h
      obtain ⟨input, harg, hop⟩ := h
      exact .unary op arg input value (ih harg) hop
  | Ebinop op left right ihleft ihright =>
      simp only [evalExpr, bind, Option.bind_eq_some_iff] at h
      obtain ⟨vleft, hleft, vright, hright, hop⟩ := h
      exact .binary op left right vleft vright value (ihleft hleft) (ihright hright) hop
  | Eload chunk address ih =>
      simp only [evalExpr, bind, Option.bind_eq_some_iff] at h
      obtain ⟨pointer, haddress, hload⟩ := h
      exact .load chunk address pointer value (ih haddress) hload

/-- `EvalExpr` holds exactly when `evalExpr` returns that value. -/
theorem eval_expr_iff :
    EvalExpr ge stack env memory expr value ↔
      evalExpr ge stack env memory expr = some value :=
  ⟨eval_expr_complete, eval_expr_sound⟩

/-- An expression evaluates to at most one value. -/
theorem eval_expr_deterministic {other : Val}
    (h : EvalExpr ge stack env memory expr value)
    (hother : EvalExpr ge stack env memory expr other) : value = other :=
  Option.some.inj ((eval_expr_complete h).symm.trans (eval_expr_complete hother))

/-- If `EvalExprList ge sp e m as vs` holds, then `evalExprList ge sp e m as` returns `some vs`. -/
theorem eval_expr_list_complete (h : EvalExprList ge stack env memory args values) :
    evalExprList ge stack env memory args = some values := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ h _ ih => simp [evalExprList, eval_expr_complete h, ih]

/-- If `evalExprList ge sp e m as` returns `some vs`, then `EvalExprList ge sp e m as vs` holds. -/
theorem eval_expr_list_sound (h : evalExprList ge stack env memory args = some values) :
    EvalExprList ge stack env memory args values := by
  induction args generalizing values with
  | nil =>
      simp only [evalExprList, Option.some.injEq] at h
      subst values
      exact .nil
  | cons arg args ih =>
      simp only [evalExprList, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨value, harg, rest, hargs, rfl⟩ := h
      exact .cons arg args value rest (eval_expr_sound harg) (ih hargs)

/-- `EvalExprList` holds exactly when `evalExprList` returns those values. -/
theorem eval_expr_list_iff :
    EvalExprList ge stack env memory args values ↔
      evalExprList ge stack env memory args = some values :=
  ⟨eval_expr_list_complete, eval_expr_list_sound⟩

/-- An expression list evaluates to at most one list of values. -/
theorem eval_expr_list_deterministic {other : List Val}
    (h : EvalExprList ge stack env memory args values)
    (hother : EvalExprList ge stack env memory args other) : values = other :=
  Option.some.inj ((eval_expr_list_complete h).symm.trans (eval_expr_list_complete hother))

end Quadrature.Cminor
