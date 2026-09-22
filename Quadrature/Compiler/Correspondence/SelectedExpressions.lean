import Quadrature.Compiler.CminorSel.Expressions
import Quadrature.Compiler.CminorSel.Imported
import Quadrature.Compiler.Correspondence.PolynomialFunction

/-!
# Double expressions after instruction selection

Relates Cminor and CminorSel double expressions for the ten programs. Read
`FloatExprSelection` first: constants, unchanged variables, and the four separately rounded
double operations. `FloatExprSelection.eval_eq` shows the two evaluations are equal as
optional values, including failure and `Vundef`, with no finiteness assumption. The
imported selected polynomial body is identified with `hornerSelected`, whose value is
proved for every binary64 input.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Compiler

open CC
open Binary64.Clight

/-- The CminorSel operation of a double operation. -/
def DoubleOp.selected : DoubleOp → CminorSel.Operation
  | .add => .Oaddf
  | .sub => .Osubf
  | .mul => .Omulf
  | .div => .Odivf

/-- CminorSel evaluates `op.selected` on two values as Cminor evaluates `op.target`. -/
theorem DoubleOp.selected_semantics (op : DoubleOp) (ge : CminorSel.Genv)
    (stack : Val) (memory : Mem) (left right : Val) :
    CminorSel.evalOperation ge stack op.selected [left, right] =
      Cminor.evalBinary op.target left right memory := by
  cases op <;> rfl

/-- The floating-point syntax preserved by this configured selection pass. -/
inductive FloatExprSelection : Cminor.Expr → CminorSel.Expr → Prop where
  | constant (value : Floats.Float) :
      FloatExprSelection (.Econst (.Ofloatconst value)) (.Eop (.Ofloatconst value) .Enil)
  | var (name : Ident) : FloatExprSelection (.Evar name) (.Evar name)
  | binary (op : DoubleOp) {left right : Cminor.Expr} {left' right' : CminorSel.Expr} :
      FloatExprSelection left left' → FloatExprSelection right right' →
      FloatExprSelection (.Ebinop op.target left right)
        (.Eop op.selected (.Econs left' (.Econs right' .Enil)))

namespace FloatExprSelection

/-- Selection preserves the entire optional result, including failed evaluation. -/
theorem eval_eq {source : Cminor.Expr} {target : CminorSel.Expr}
    (h : FloatExprSelection source target)
    (sourceGe : Cminor.Genv) (targetGe : CminorSel.Genv)
    (sourceStack targetStack : Val) (sourceMemory targetMemory : Mem)
    (env : Cminor.Env) (locals : CminorSel.LetEnv) :
    CminorSel.evalExpr targetGe targetStack env targetMemory locals target =
      Cminor.evalExpr sourceGe sourceStack env sourceMemory source := by
  induction h with
  | constant => rfl
  | var => rfl
  | @binary op left right left' right' _ _ ihleft ihright =>
      simp only [CminorSel.evalExpr, CminorSel.evalExprList, ihleft, ihright, Cminor.evalExpr]
      cases Cminor.evalExpr sourceGe sourceStack env sourceMemory left <;>
        cases Cminor.evalExpr sourceGe sourceStack env sourceMemory right <;>
        first
        | rfl
        | exact op.selected_semantics targetGe targetStack sourceMemory _ _

/-- The equality also connects the relational evaluation rules in both directions. -/
theorem eval_relation_iff {source : Cminor.Expr} {target : CminorSel.Expr}
    (h : FloatExprSelection source target)
    (sourceGe : Cminor.Genv) (targetGe : CminorSel.Genv)
    (sourceStack targetStack : Val) (sourceMemory targetMemory : Mem)
    (env : Cminor.Env) (locals : CminorSel.LetEnv) (value : Val) :
    CminorSel.EvalExpr targetGe targetStack env targetMemory locals target value ↔
      Cminor.EvalExpr sourceGe sourceStack env sourceMemory source value := by
  rw [CminorSel.eval_expr_iff, Cminor.eval_expr_iff,
    h.eval_eq sourceGe targetGe sourceStack targetStack sourceMemory targetMemory env locals]

end FloatExprSelection

/-- The selected internal polynomial, compiler global 68, with the identifiers of the Cminor
version. -/
def polynomialSelected : CminorSel.Function :=
  match h : CminorSel.Imported.global68.2 with
  | .Gfun (.Internal f) => f
  | .Gfun (.External _) => False.elim (by cases h)
  | .Gvar _ => False.elim (by cases h)

/-- CminorSel syntax for the separately rounded Horner recurrence over `polynomialSquare`. -/
def hornerSelected : List Binary64.Value → CminorSel.Expr
  | [] => .Eop (.Ofloatconst Binary64.zero) .Enil
  | c :: cs => .Eop .Oaddf (.Econs (.Eop (.Ofloatconst c) .Enil)
      (.Econs (.Eop .Omulf (.Econs (.Evar polynomialSquare)
        (.Econs (hornerSelected cs) .Enil))) .Enil))

/-- The Cminor Horner expression selects to `hornerSelected`. -/
theorem horner_selection (coefficients : List Binary64.Value) :
    FloatExprSelection (hornerTarget id coefficients) (hornerSelected coefficients) := by
  induction coefficients with
  | nil => exact .constant _
  | cons c cs ih => exact .binary .add (.constant c) (.binary .mul (.var _) ih)

/-- Global 68 of the selected program is `polynomialSelected`. -/
theorem polynomial_selected_definition :
    CminorSel.Imported.global68.2 = .Gfun (.Internal polynomialSelected) := rfl

/-- The selected body squares the argument and returns `hornerSelected`. -/
theorem polynomial_selected_body :
    polynomialSelected.fn_body =
      .Sseq (.Sassign polynomialSquare
        (.Eop .Omulf (.Econs (.Evar polynomialArgument)
          (.Econs (.Evar polynomialArgument) .Enil))))
        (.Sreturn (some (hornerSelected Binary64.Polynomial.coefficients))) := rfl

/-- The selected polynomial keeps the Cminor signature. -/
theorem polynomial_selected_signature :
    polynomialSelected.fn_sig = polynomialTarget.fn_sig := rfl

/-- The selected polynomial has a zero-size stack frame. -/
theorem polynomial_selected_stackspace :
    polynomialSelected.fn_stackspace = 0 := rfl

/-- The selected polynomial keeps the Cminor parameters. -/
theorem polynomial_selected_parameters :
    polynomialSelected.fn_params = polynomialTarget.fn_params := rfl

/-- The selected polynomial keeps the Cminor local variables. -/
theorem polynomial_selected_variables :
    polynomialSelected.fn_vars = polynomialTarget.fn_vars := rfl

/-- The selected assignment computes the argument's rounded square. -/
theorem polynomial_selected_square_eval (ge : CminorSel.Genv) (stack : Val)
    (env : CminorSel.Env) (memory : Mem) (locals : CminorSel.LetEnv) (x : Binary64.Value)
    (hx : env.get polynomialArgument = some (.Vfloat x)) :
    CminorSel.evalExpr ge stack env memory locals
      (.Eop .Omulf (.Econs (.Evar polynomialArgument) (.Econs (.Evar polynomialArgument) .Enil))) =
      some (.Vfloat (Floats.Float.mul x x)) := by
  simp only [CminorSel.evalExpr, CminorSel.evalExprList, hx, bind, Option.bind_some,
    pure, CminorSel.evalOperation]
  rfl

/-- Selected Horner evaluation computes the FloatLib recurrence, rounding each operation in
order. -/
theorem horner_selected_eval (ge : CminorSel.Genv) (stack : Val) (env : CminorSel.Env)
    (memory : Mem) (locals : CminorSel.LetEnv) (z : Binary64.Value)
    (hz : env.get polynomialSquare = some (.Vfloat z)) (coefficients : List Binary64.Value) :
    CminorSel.evalExpr ge stack env memory locals (hornerSelected coefficients) =
      some (.Vfloat (Binary64.Polynomial.horner z coefficients)) := by
  induction coefficients with
  | nil => rfl
  | cons c cs ih =>
      simp only [hornerSelected, CminorSel.evalExpr, CminorSel.evalExprList, hz, ih,
        bind, Option.bind_some, pure, CminorSel.evalOperation]
      rfl

/-- After assigning the square, the selected return expression computes the polynomial. -/
theorem polynomial_selected_return_eval (ge : CminorSel.Genv) (stack : Val)
    (env : CminorSel.Env) (memory : Mem) (locals : CminorSel.LetEnv) (x : Binary64.Value) :
    CminorSel.evalExpr ge stack
      (env.set polynomialSquare (.Vfloat (Floats.Float.mul x x))) memory locals
      (hornerSelected Binary64.Polynomial.coefficients) =
      some (.Vfloat (Binary64.Polynomial.cosine x)) :=
  horner_selected_eval ge stack _ memory locals _ (PTree.gss _ _ _) _

end Quadrature.Compiler
