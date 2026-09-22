import Quadrature.CSource.Semantics.Entry
import Quadrature.CSource.Semantics.Simple

/-!
# Terminating execution in the C reduction strategy

Vocabulary for the `Quadrature.CSource` execution files. The *strategy
semantics* is an adaptation of the big-step section of CompCert's
`cfrontend/Cstrategy.v` (revision recorded in `Quadrature.Clight.Source`) to
the FloatLib memory and value model. Expression evaluation has two phases. The
*effect phase* `EvalExpr ge e m kind a t m' a'` performs the calls and stores
inside `a`, emitting trace `t` and taking memory `m` to `m'`, and leaves a
residual side-effect-free expression `a'`. The *pure phase* `EvalRvalue` (in
`Quadrature.CSource.Semantics.Simple`) then reads the value of the residual expression
without changing memory. An `Outcome` records how a statement finished:
normally, by `break`, by `continue`, or by `return` with an optional value.
A function's locals are *freeable* when every block of its environment can be
freed at return, so that `Mem.freeList` succeeds. `CallMemory initial final`
(in `Quadrature.CSource.Semantics.CallMemory`) is the relation saying a call preserves
every load and permission on the caller's previously allocated blocks.

The five mutually inductive relations below cover expressions, expression
lists, statements and function calls, with traces, statement outcomes, return
casts and freeing of locals. There are no rules for `goto`, labels, builtin
expressions or divergence, and parenthesized intermediate terms (`Eparen`) are
not modeled.
-/

namespace Quadrature.CSource.C

open CC

/-- A C function definition: `Internal f` with a body, or `External ef args res cc`, an external
function with its argument types, result type and calling convention. -/
inductive FunDef where
  | Internal (function : Function)
  | External (function : ExtFun) (arguments : List Ty) (result : Ty) (cc : CallConv)

/-- The function type of a definition: parameter types, return type and calling convention. -/
def typeOfFundef : FunDef → Ty
  | .Internal f => .Tfunction (f.fn_params.map Prod.snd) f.fn_return f.fn_callconv
  | .External _ args res cc => .Tfunction args res cc

/-- A C global environment: CLean's `Genv` of symbols and global definitions, instantiated with
C `FunDef`s, together with the composite environment. -/
structure GlobalEnv where
  globals : CC.Genv FunDef Ty
  composites : CompositeEnv

/-- The symbol and composite part of `ge`, which is all the pure phase and memory accesses
need. -/
def GlobalEnv.expressionEnv (ge : GlobalEnv) : ExpressionEnv :=
  ⟨Genv.toSenv ge.globals, ge.composites⟩

/-- The context of the effect phase: `LV` evaluates an expression as a location, `RV` as a
value. -/
inductive Kind where
  | LV
  | RV

/-- How a statement finished: `normal`, `break`, `continue`, or `return value`, where `value`
carries the returned value and its type when the `return` had an operand. -/
inductive Outcome where
  | break
  | continue
  | normal
  | return (value : Option (Val × Ty))

/-- The outcomes after which a loop body proceeds to the next test: `normal` and `continue`. -/
inductive NormalOrContinue : Outcome → Prop where
  | normal : NormalOrContinue .normal
  | continue : NormalOrContinue .continue

/-- Relates a loop body outcome that leaves the loop to the outcome of the whole loop: `break`
becomes `normal`, and `return value` stays `return value`. -/
inductive BreakOrReturn : Outcome → Outcome → Prop where
  | break : BreakOrReturn .break .normal
  | return (value) : BreakOrReturn (.return value) (.return value)

/-- The outcome of a `switch` from the outcome of its body: `break` becomes `normal`, every other
outcome passes through. -/
def outcomeSwitch : Outcome → Outcome
  | .break => .normal
  | outcome => outcome

/-- `OutcomeResult outcome type value memory`: a function with return type `type` finishing with
`outcome` returns `value`. A `void` function finishing normally or by a bare `return` yields
`Vundef`. A `return (v, ty)` yields the cast of `v` from `ty` to `type` in `memory`, with `type`
not `void`. Every other combination is impossible. -/
def OutcomeResult (outcome : Outcome) (type : Ty) (value : Val) (memory : Mem) : Prop :=
  match outcome, type with
  | .normal, .Tvoid | .return none, .Tvoid => value = .Vundef
  | .return (some (v, ty)), result =>
      result ≠ .Tvoid ∧ Cop.semCast v ty result memory = some value
  | _, _ => False

/-- The labeled statements from the `default` case onward, or `LSnil` when there is none. -/
def selectSwitchDefault : LabeledStatements → LabeledStatements
  | .LSnil => .LSnil
  | cases@(.LScons none _ _) => cases
  | .LScons (some _) _ rest => selectSwitchDefault rest

/-- The labeled statements from the case labeled `value` onward, if such a case exists. -/
def selectSwitchCase (value : Z) : LabeledStatements → Option LabeledStatements
  | .LSnil => none
  | .LScons none _ rest => selectSwitchCase value rest
  | cases@(.LScons (some label) _ rest) =>
      if label = value then some cases else selectSwitchCase value rest

/-- The cases a `switch` on `value` executes: from the matching label, otherwise from
`default`. -/
def selectSwitch (value : Z) (cases : LabeledStatements) : LabeledStatements :=
  (selectSwitchCase value cases).getD (selectSwitchDefault cases)

/-- The bodies of a case list sequenced into one statement, so that fall-through is implicit. -/
def seqOfLabeledStatement : LabeledStatements → Stmt
  | .LSnil => .Sskip
  | .LScons _ body rest => .Ssequence body (seqOfLabeledStatement rest)

/-- The value of `++` or `--` applied to `value` of type `type`: `value + 1` or `value - 1`
through CompCert's `semAdd` and `semSub` with the constant of type `int`. -/
def semIncrDecr (composites : CompositeEnv) (op : IncrOrDecr)
    (value : Val) (type : Ty) (memory : Mem) : Option Val :=
  match op with
  | .incr => Cop.semAdd composites value type (.Vint Integers.Int.one) type_int32s memory
  | .decr => Cop.semSub composites value type (.Vint Integers.Int.one) type_int32s memory

/-- The type of the result of `++` or `--` on an operand of type `type`: `typeconv type` with its
attributes cleared, or `Tvoid` for unsupported types. The result is cast back to `type`. -/
def incrDecrType (type : Ty) : Ty :=
  match typeconv type with
  | .Tpointer target attr => .Tpointer target attr
  | .Tint size sign _ => .Tint size sign noattr
  | .Tlong sign _ => .Tlong sign noattr
  | .Tfloat size _ => .Tfloat size noattr
  | _ => .Tvoid

private def boolType : Ty := .Tint .IBool .Signed noattr

variable [ExternalCalls]

mutual
/-- `EvalExpression ge e m a trace m' value`: full evaluation of `a` in environment `e` from
memory `m`. The effect phase produces `m'` and a residual `a'`, and the pure phase reads `value`
from `a'` in `m'`. -/
inductive EvalExpression (ge : GlobalEnv) :
    Env → Mem → Expr → Trace → Mem → Val → Prop where
  | intro (e m a trace m' a' value) :
      EvalExpr ge e m .RV a trace m' a' →
      EvalRvalue ge.expressionEnv e m' a' value →
      EvalExpression ge e m a trace m' value

/-- The effect phase. `EvalExpr ge e m kind a t m' a'` performs the calls, assignments and
increments inside `a` (as a location for `LV`, a value for `RV`), emitting trace `t`, taking
memory `m` to `m'` and leaving the residual expression `a'`. Operands are evaluated left to
right, and the residual of an effectful subterm is `Eval v ty`. -/
inductive EvalExpr (ge : GlobalEnv) :
    Env → Mem → Kind → Expr → Trace → Mem → Expr → Prop where
  | value (e m v ty) : EvalExpr ge e m .RV (.Eval v ty) E0 m (.Eval v ty)
  | var (e m name ty) : EvalExpr ge e m .LV (.Evar name ty) E0 m (.Evar name ty)
  | field (e m a t m' a' name ty) :
      EvalExpr ge e m .RV a t m' a' →
      EvalExpr ge e m .LV (.Efield a name ty) t m' (.Efield a' name ty)
  | valof (e m a t m' a' ty) :
      typeIsVolatile (typeof a) = false →
      EvalExpr ge e m .LV a t m' a' →
      EvalExpr ge e m .RV (.Evalof a ty) t m' (.Evalof a' ty)
  | valof_volatile (e m a t₁ m' a' ty block ofs bf t₂ value) :
      typeIsVolatile (typeof a) = true →
      EvalExpr ge e m .LV a t₁ m' a' →
      EvalLvalue ge.expressionEnv e m' a' block ofs bf →
      DerefLoc ge.expressionEnv (typeof a) m' block ofs bf t₂ value →
      ty = typeof a →
      EvalExpr ge e m .RV (.Evalof a ty) (t₁ ++ t₂) m' (.Eval value ty)
  | deref (e m a t m' a' ty) :
      EvalExpr ge e m .RV a t m' a' →
      EvalExpr ge e m .LV (.Ederef a ty) t m' (.Ederef a' ty)
  | addrof (e m a t m' a' ty) :
      EvalExpr ge e m .LV a t m' a' →
      EvalExpr ge e m .RV (.Eaddrof a ty) t m' (.Eaddrof a' ty)
  | unop (e m a t m' a' op ty) :
      EvalExpr ge e m .RV a t m' a' →
      EvalExpr ge e m .RV (.Eunop op a ty) t m' (.Eunop op a' ty)
  | binop (e m a₁ t₁ m₁ a₁' a₂ t₂ m₂ a₂' op ty) :
      EvalExpr ge e m .RV a₁ t₁ m₁ a₁' →
      EvalExpr ge e m₁ .RV a₂ t₂ m₂ a₂' →
      EvalExpr ge e m .RV (.Ebinop op a₁ a₂ ty) (t₁ ++ t₂) m₂ (.Ebinop op a₁' a₂' ty)
  | cast (e m a t m' a' ty) :
      EvalExpr ge e m .RV a t m' a' →
      EvalExpr ge e m .RV (.Ecast a ty) t m' (.Ecast a' ty)
  | seqand_true (e m a₁ a₂ ty t₁ m₁ a₁' v₁ t₂ m₂ a₂' v₂ v) :
      EvalExpr ge e m .RV a₁ t₁ m₁ a₁' →
      EvalRvalue ge.expressionEnv e m₁ a₁' v₁ →
      Cop.boolVal v₁ (typeof a₁) m₁ = some true →
      EvalExpr ge e m₁ .RV a₂ t₂ m₂ a₂' →
      EvalRvalue ge.expressionEnv e m₂ a₂' v₂ →
      Cop.semCast v₂ (typeof a₂) boolType m₂ = some v →
      EvalExpr ge e m .RV (.Eseqand a₁ a₂ ty) (t₁ ++ t₂) m₂ (.Eval v ty)
  | seqand_false (e m a₁ a₂ ty t₁ m₁ a₁' v₁) :
      EvalExpr ge e m .RV a₁ t₁ m₁ a₁' →
      EvalRvalue ge.expressionEnv e m₁ a₁' v₁ →
      Cop.boolVal v₁ (typeof a₁) m₁ = some false →
      EvalExpr ge e m .RV (.Eseqand a₁ a₂ ty) t₁ m₁ (.Eval (.Vint Integers.Int.zero) ty)
  | seqor_false (e m a₁ a₂ ty t₁ m₁ a₁' v₁ t₂ m₂ a₂' v₂ v) :
      EvalExpr ge e m .RV a₁ t₁ m₁ a₁' →
      EvalRvalue ge.expressionEnv e m₁ a₁' v₁ →
      Cop.boolVal v₁ (typeof a₁) m₁ = some false →
      EvalExpr ge e m₁ .RV a₂ t₂ m₂ a₂' →
      EvalRvalue ge.expressionEnv e m₂ a₂' v₂ →
      Cop.semCast v₂ (typeof a₂) boolType m₂ = some v →
      EvalExpr ge e m .RV (.Eseqor a₁ a₂ ty) (t₁ ++ t₂) m₂ (.Eval v ty)
  | seqor_true (e m a₁ a₂ ty t₁ m₁ a₁' v₁) :
      EvalExpr ge e m .RV a₁ t₁ m₁ a₁' →
      EvalRvalue ge.expressionEnv e m₁ a₁' v₁ →
      Cop.boolVal v₁ (typeof a₁) m₁ = some true →
      EvalExpr ge e m .RV (.Eseqor a₁ a₂ ty) t₁ m₁ (.Eval (.Vint Integers.Int.one) ty)
  | condition (e m a₁ a₂ a₃ ty t₁ m₁ a₁' v₁ t₂ m₂ a' v' test v) :
      EvalExpr ge e m .RV a₁ t₁ m₁ a₁' →
      EvalRvalue ge.expressionEnv e m₁ a₁' v₁ →
      Cop.boolVal v₁ (typeof a₁) m₁ = some test →
      EvalExpr ge e m₁ .RV (if test then a₂ else a₃) t₂ m₂ a' →
      EvalRvalue ge.expressionEnv e m₂ a' v' →
      Cop.semCast v' (typeof (if test then a₂ else a₃)) ty m₂ = some v →
      EvalExpr ge e m .RV (.Econdition a₁ a₂ a₃ ty) (t₁ ++ t₂) m₂ (.Eval v ty)
  | sizeof (e m arg ty) : EvalExpr ge e m .RV (.Esizeof arg ty) E0 m (.Esizeof arg ty)
  | alignof (e m arg ty) : EvalExpr ge e m .RV (.Ealignof arg ty) E0 m (.Ealignof arg ty)
  | assign (e m l r ty t₁ m₁ l' t₂ m₂ r' block ofs bf v v₁ v' t₃ m₃) :
      EvalExpr ge e m .LV l t₁ m₁ l' →
      EvalExpr ge e m₁ .RV r t₂ m₂ r' →
      EvalLvalue ge.expressionEnv e m₂ l' block ofs bf →
      EvalRvalue ge.expressionEnv e m₂ r' v →
      Cop.semCast v (typeof r) (typeof l) m₂ = some v₁ →
      AssignLoc ge.expressionEnv (typeof l) m₂ block ofs bf v₁ t₃ m₃ v' →
      ty = typeof l →
      EvalExpr ge e m .RV (.Eassign l r ty) (t₁ ++ t₂ ++ t₃) m₃ (.Eval v' ty)
  | assignop (e m op l r tyres ty t₁ m₁ l' t₂ m₂ r' block ofs bf
      v₁ v₂ v₃ v₄ v' t₃ t₄ m₃) :
      EvalExpr ge e m .LV l t₁ m₁ l' →
      EvalExpr ge e m₁ .RV r t₂ m₂ r' →
      EvalLvalue ge.expressionEnv e m₂ l' block ofs bf →
      DerefLoc ge.expressionEnv (typeof l) m₂ block ofs bf t₃ v₁ →
      EvalRvalue ge.expressionEnv e m₂ r' v₂ →
      Cop.semBinaryOperation ge.composites op v₁ (typeof l) v₂ (typeof r) m₂ = some v₃ →
      Cop.semCast v₃ tyres (typeof l) m₂ = some v₄ →
      AssignLoc ge.expressionEnv (typeof l) m₂ block ofs bf v₄ t₄ m₃ v' →
      ty = typeof l →
      EvalExpr ge e m .RV (.Eassignop op l r tyres ty) (t₁ ++ t₂ ++ t₃ ++ t₄) m₃ (.Eval v' ty)
  | postincr (e m op l ty t₁ m₁ l' block ofs bf v₁ v₂ v₃ v' m₂ t₂ t₃) :
      EvalExpr ge e m .LV l t₁ m₁ l' →
      EvalLvalue ge.expressionEnv e m₁ l' block ofs bf →
      DerefLoc ge.expressionEnv ty m₁ block ofs bf t₂ v₁ →
      semIncrDecr ge.composites op v₁ ty m₁ = some v₂ →
      Cop.semCast v₂ (incrDecrType ty) ty m₁ = some v₃ →
      AssignLoc ge.expressionEnv ty m₁ block ofs bf v₃ t₃ m₂ v' →
      ty = typeof l →
      EvalExpr ge e m .RV (.Epostincr op l ty) (t₁ ++ t₂ ++ t₃) m₂ (.Eval v₁ ty)
  | comma (e m r₁ r₂ ty t₁ m₁ r₁' v₁ t₂ m₂ r₂') :
      EvalExpr ge e m .RV r₁ t₁ m₁ r₁' →
      EvalRvalue ge.expressionEnv e m₁ r₁' v₁ →
      EvalExpr ge e m₁ .RV r₂ t₂ m₂ r₂' →
      ty = typeof r₂ →
      EvalExpr ge e m .RV (.Ecomma r₁ r₂ ty) (t₁ ++ t₂) m₂ r₂'
  | call (e m rf args ty t₁ m₁ rf' t₂ m₂ args' vf values
      types result cc fd t₃ m₃ value) :
      EvalExpr ge e m .RV rf t₁ m₁ rf' →
      EvalExprlist ge e m₁ args t₂ m₂ args' →
      EvalRvalue ge.expressionEnv e m₂ rf' vf →
      EvalList ge.expressionEnv e m₂ args' types values →
      Cop.classifyFun (typeof rf) = .f types result cc →
      Genv.findFunct ge.globals vf = some fd →
      typeOfFundef fd = .Tfunction types result cc →
      EvalFuncall ge m₂ fd values t₃ m₃ value →
      EvalExpr ge e m .RV (.Ecall rf args ty) (t₁ ++ t₂ ++ t₃) m₃ (.Eval value ty)

/-- The effect phase on an argument list, left to right, concatenating the traces. -/
inductive EvalExprlist (ge : GlobalEnv) :
    Env → Mem → Exprlist → Trace → Mem → Exprlist → Prop where
  | nil (e m) : EvalExprlist ge e m .Enil E0 m .Enil
  | cons (e m a rest t₁ m₁ a' t₂ m₂ rest') :
      EvalExpr ge e m .RV a t₁ m₁ a' →
      EvalExprlist ge e m₁ rest t₂ m₂ rest' →
      EvalExprlist ge e m (.Econs a rest) (t₁ ++ t₂) m₂ (.Econs a' rest')

/-- `ExecStmt ge e m s t m' out`: statement `s` runs in environment `e` from memory `m` to `m'`
with trace `t` and finishes with outcome `out`. A `for` loop first executes its initializer once
(`for_start`) and then loops with an empty initializer. A `switch` selects its cases with
`selectSwitch`. -/
inductive ExecStmt (ge : GlobalEnv) :
    Env → Mem → Stmt → Trace → Mem → Outcome → Prop where
  | skip (e m) : ExecStmt ge e m .Sskip E0 m .normal
  | do (e m a t m' v) :
      EvalExpression ge e m a t m' v →
      ExecStmt ge e m (.Sdo a) t m' .normal
  | seq_normal (e m s₁ s₂ t₁ m₁ t₂ m₂ out) :
      ExecStmt ge e m s₁ t₁ m₁ .normal →
      ExecStmt ge e m₁ s₂ t₂ m₂ out →
      ExecStmt ge e m (.Ssequence s₁ s₂) (t₁ ++ t₂) m₂ out
  | seq_stop (e m s₁ s₂ t₁ m₁ out) :
      ExecStmt ge e m s₁ t₁ m₁ out →
      out ≠ .normal →
      ExecStmt ge e m (.Ssequence s₁ s₂) t₁ m₁ out
  | ifthenelse (e m a s₁ s₂ t₁ m₁ v₁ t₂ m₂ test out) :
      EvalExpression ge e m a t₁ m₁ v₁ →
      Cop.boolVal v₁ (typeof a) m₁ = some test →
      ExecStmt ge e m₁ (if test then s₁ else s₂) t₂ m₂ out →
      ExecStmt ge e m (.Sifthenelse a s₁ s₂) (t₁ ++ t₂) m₂ out
  | return_none (e m) : ExecStmt ge e m (.Sreturn none) E0 m (.return none)
  | return_some (e m a t m' v) :
      EvalExpression ge e m a t m' v →
      ExecStmt ge e m (.Sreturn (some a)) t m' (.return (some (v, typeof a)))
  | break (e m) : ExecStmt ge e m .Sbreak E0 m .break
  | continue (e m) : ExecStmt ge e m .Scontinue E0 m .continue
  | while_false (e m a s t m' v) :
      EvalExpression ge e m a t m' v →
      Cop.boolVal v (typeof a) m' = some false →
      ExecStmt ge e m (.Swhile a s) t m' .normal
  | while_stop (e m a s t₁ m₁ v t₂ m₂ out' out) :
      EvalExpression ge e m a t₁ m₁ v →
      Cop.boolVal v (typeof a) m₁ = some true →
      ExecStmt ge e m₁ s t₂ m₂ out' →
      BreakOrReturn out' out →
      ExecStmt ge e m (.Swhile a s) (t₁ ++ t₂) m₂ out
  | while_loop (e m a s t₁ m₁ v t₂ m₂ out₁ t₃ m₃ out) :
      EvalExpression ge e m a t₁ m₁ v →
      Cop.boolVal v (typeof a) m₁ = some true →
      ExecStmt ge e m₁ s t₂ m₂ out₁ →
      NormalOrContinue out₁ →
      ExecStmt ge e m₂ (.Swhile a s) t₃ m₃ out →
      ExecStmt ge e m (.Swhile a s) (t₁ ++ t₂ ++ t₃) m₃ out
  | dowhile_false (e m s a t₁ m₁ out₁ t₂ m₂ v) :
      ExecStmt ge e m s t₁ m₁ out₁ →
      NormalOrContinue out₁ →
      EvalExpression ge e m₁ a t₂ m₂ v →
      Cop.boolVal v (typeof a) m₂ = some false →
      ExecStmt ge e m (.Sdowhile a s) (t₁ ++ t₂) m₂ .normal
  | dowhile_stop (e m s a t m₁ out₁ out) :
      ExecStmt ge e m s t m₁ out₁ →
      BreakOrReturn out₁ out →
      ExecStmt ge e m (.Sdowhile a s) t m₁ out
  | dowhile_loop (e m s a t₁ m₁ out₁ t₂ m₂ v t₃ m₃ out) :
      ExecStmt ge e m s t₁ m₁ out₁ →
      NormalOrContinue out₁ →
      EvalExpression ge e m₁ a t₂ m₂ v →
      Cop.boolVal v (typeof a) m₂ = some true →
      ExecStmt ge e m₂ (.Sdowhile a s) t₃ m₃ out →
      ExecStmt ge e m (.Sdowhile a s) (t₁ ++ t₂ ++ t₃) m₃ out
  | for_start (e m s init test incr out m₁ m₂ t₁ t₂) :
      ExecStmt ge e m init t₁ m₁ .normal →
      ExecStmt ge e m₁ (.Sfor .Sskip test incr s) t₂ m₂ out →
      ExecStmt ge e m (.Sfor init test incr s) (t₁ ++ t₂) m₂ out
  | for_false (e m s test incr t m' v) :
      EvalExpression ge e m test t m' v →
      Cop.boolVal v (typeof test) m' = some false →
      ExecStmt ge e m (.Sfor .Sskip test incr s) t m' .normal
  | for_stop (e m s test incr t₁ m₁ v t₂ m₂ out₁ out) :
      EvalExpression ge e m test t₁ m₁ v →
      Cop.boolVal v (typeof test) m₁ = some true →
      ExecStmt ge e m₁ s t₂ m₂ out₁ →
      BreakOrReturn out₁ out →
      ExecStmt ge e m (.Sfor .Sskip test incr s) (t₁ ++ t₂) m₂ out
  | for_loop (e m s test incr t₁ m₁ v t₂ m₂ out₁ t₃ m₃ t₄ m₄ out) :
      EvalExpression ge e m test t₁ m₁ v →
      Cop.boolVal v (typeof test) m₁ = some true →
      ExecStmt ge e m₁ s t₂ m₂ out₁ →
      NormalOrContinue out₁ →
      ExecStmt ge e m₂ incr t₃ m₃ .normal →
      ExecStmt ge e m₃ (.Sfor .Sskip test incr s) t₄ m₄ out →
      ExecStmt ge e m (.Sfor .Sskip test incr s) (t₁ ++ t₂ ++ t₃ ++ t₄) m₄ out
  | switch (e m a cases t₁ m₁ v n t₂ m₂ out) :
      EvalExpression ge e m a t₁ m₁ v →
      Cop.semSwitchArg v (typeof a) = some n →
      ExecStmt ge e m₁ (seqOfLabeledStatement (selectSwitch n cases)) t₂ m₂ out →
      ExecStmt ge e m (.Sswitch a cases) (t₁ ++ t₂) m₂ (outcomeSwitch out)

/-- `EvalFuncall ge m fd args t m' v`: calling `fd` with `args` from memory `m` returns `v` in
memory `m'` with trace `t`. An internal function allocates its parameters and locals, binds the
arguments, runs its body, casts the returned value to the return type (`OutcomeResult`) and
frees its locals. An external function is governed by `externalCall`. -/
inductive EvalFuncall (ge : GlobalEnv) :
    Mem → FunDef → List Val → Trace → Mem → Val → Prop where
  | internal (m f args t e m₁ m₂ m₃ out result m₄) :
      (f.fn_params.map Prod.fst ++ f.fn_vars.map Prod.fst).Nodup →
      AllocVariables ge.expressionEnv emptyEnv m (f.fn_params ++ f.fn_vars) e m₁ →
      BindParameters ge.expressionEnv e m₁ f.fn_params args m₂ →
      ExecStmt ge e m₂ f.fn_body t m₃ out →
      OutcomeResult out f.fn_return result m₃ →
      Mem.freeList m₃ (blocksOfEnv ge.composites e) = some m₄ →
      EvalFuncall ge m (.Internal f) args t m₄ result
  | external (m ef types result cc args t value m') :
      externalCall ef (Genv.toSenv ge.globals) args m t value m' →
      EvalFuncall ge m (.External ef types result cc) args t m' value
end

/-- Given a `FunctionEntry` for `f`, an execution of its body with outcome `outcome`, the matching
`OutcomeResult` and a successful free of its locals, the call of `f` evaluates to `value`. This
is the internal-call rule with the entry premises grouped. -/
theorem FunctionEntry.eval_funcall {ge : GlobalEnv} {f : Function} {args : List Val}
    {initial entered afterBody final : Mem} {locals : Env} {trace : Trace}
    {outcome : Outcome} {value : Val}
    (hentry : FunctionEntry ge.expressionEnv f args initial locals entered)
    (hbody : ExecStmt ge locals entered f.fn_body trace afterBody outcome)
    (hresult : OutcomeResult outcome f.fn_return value afterBody)
    (hfree : Mem.freeList afterBody (blocksOfEnv ge.composites locals) = some final) :
    EvalFuncall ge initial (.Internal f) args trace final value := by
  obtain ⟨allocated, halloc, hbind⟩ := hentry.allocated_and_bound
  exact .internal _ _ _ _ _ _ _ _ _ _ _ hentry.names_unique halloc hbind hbody hresult hfree

end Quadrature.CSource.C
