import Quadrature.Compiler.CminorSel.Operations

/-!
# Expression evaluation after instruction selection

Relational and executable evaluation of `Expr`, `ExprList`, and `CondExpr`, after
`backend/CminorSel.v`, restricted to the syntax in `Syntax.lean`.
`EvalExpr ge sp e m le a v` says `a` evaluates to `v` under the let environment `le`,
and `evalExpr` computes that value. `eval_expr_iff` shows the two agree. Let bindings
use de Bruijn indices, and only the selected branch of a conditional is evaluated.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.CminorSel

open CC

mutual
/-- `EvalExpr ge sp e m le a v` says the expression `a` evaluates to `v` with stack pointer `sp`,
local environment `e`, memory `m`, and let environment `le`. -/
inductive EvalExpr (ge : Genv) (stack : Val) (env : Env) (memory : Mem) :
    LetEnv → Expr → Val → Prop where
  | var (locals name value) :
      env.get name = some value → EvalExpr ge stack env memory locals (.Evar name) value
  | operation (locals op args values value) :
      EvalExprList ge stack env memory locals args values →
      evalOperation ge stack op values = some value →
      EvalExpr ge stack env memory locals (.Eop op args) value
  | load (locals chunk address args values pointer value) :
      EvalExprList ge stack env memory locals args values →
      evalAddressing ge stack address values = some pointer →
      Mem.loadv chunk memory pointer = some value →
      EvalExpr ge stack env memory locals (.Eload chunk address args) value
  | condition (locals condition yes no result value) :
      EvalCondExpr ge stack env memory locals condition result →
      EvalExpr ge stack env memory locals (if result then yes else no) value →
      EvalExpr ge stack env memory locals (.Econdition condition yes no) value
  | letValue (locals value body input result) :
      EvalExpr ge stack env memory locals value input →
      EvalExpr ge stack env memory (input :: locals) body result →
      EvalExpr ge stack env memory locals (.Elet value body) result
  | letVar (locals index value) :
      locals[index]? = some value →
      EvalExpr ge stack env memory locals (.Eletvar index) value

/-- `EvalExprList ge sp e m le as vs` evaluates the expression list `as` pointwise to `vs`. -/
inductive EvalExprList (ge : Genv) (stack : Val) (env : Env) (memory : Mem) :
    LetEnv → ExprList → List Val → Prop where
  | nil (locals) : EvalExprList ge stack env memory locals .Enil []
  | cons (locals head tail value values) :
      EvalExpr ge stack env memory locals head value →
      EvalExprList ge stack env memory locals tail values →
      EvalExprList ge stack env memory locals (.Econs head tail) (value :: values)

/-- `EvalCondExpr ge sp e m le c b` says the conditional expression `c` evaluates to the boolean
`b`. -/
inductive EvalCondExpr (ge : Genv) (stack : Val) (env : Env) (memory : Mem) :
    LetEnv → CondExpr → Bool → Prop where
  | condition (locals condition args values result) :
      EvalExprList ge stack env memory locals args values →
      evalCondition condition values = some result →
      EvalCondExpr ge stack env memory locals (.CEcond condition args) result
  | branch (locals condition yes no result value) :
      EvalCondExpr ge stack env memory locals condition result →
      EvalCondExpr ge stack env memory locals (if result then yes else no) value →
      EvalCondExpr ge stack env memory locals (.CEcondition condition yes no) value
  | letValue (locals value body input result) :
      EvalExpr ge stack env memory locals value input →
      EvalCondExpr ge stack env memory (input :: locals) body result →
      EvalCondExpr ge stack env memory locals (.CElet value body) result
end

mutual
/-- `evalExpr ge sp e m le a` computes the value of `a`, or `none` when a variable or let index is
unbound or an operation or load fails. -/
def evalExpr (ge : Genv) (stack : Val) (env : Env) (memory : Mem) :
    LetEnv → Expr → Option Val
  | _, .Evar name => env.get name
  | locals, .Eop op args => do
      let values ← evalExprList ge stack env memory locals args
      evalOperation ge stack op values
  | locals, .Eload chunk address args => do
      let values ← evalExprList ge stack env memory locals args
      let pointer ← evalAddressing ge stack address values
      Mem.loadv chunk memory pointer
  | locals, .Econdition condition yes no => do
      let result ← evalCondExpr ge stack env memory locals condition
      if result then evalExpr ge stack env memory locals yes
      else evalExpr ge stack env memory locals no
  | locals, .Elet value body => do
      let input ← evalExpr ge stack env memory locals value
      evalExpr ge stack env memory (input :: locals) body
  | locals, .Eletvar index => locals[index]?

/-- `evalExprList ge sp e m le as` computes the values of `as` in order, failing if any fails. -/
def evalExprList (ge : Genv) (stack : Val) (env : Env) (memory : Mem) :
    LetEnv → ExprList → Option (List Val)
  | _, .Enil => some []
  | locals, .Econs head tail => do
      let value ← evalExpr ge stack env memory locals head
      let values ← evalExprList ge stack env memory locals tail
      pure (value :: values)

/-- `evalCondExpr ge sp e m le c` computes the boolean value of `c`, or fails. -/
def evalCondExpr (ge : Genv) (stack : Val) (env : Env) (memory : Mem) :
    LetEnv → CondExpr → Option Bool
  | locals, .CEcond condition args => do
      let values ← evalExprList ge stack env memory locals args
      evalCondition condition values
  | locals, .CEcondition condition yes no => do
      let result ← evalCondExpr ge stack env memory locals condition
      if result then evalCondExpr ge stack env memory locals yes
      else evalCondExpr ge stack env memory locals no
  | locals, .CElet value body => do
      let input ← evalExpr ge stack env memory locals value
      evalCondExpr ge stack env memory (input :: locals) body
end

variable {ge : Genv} {stack : Val} {env : Env} {memory : Mem}

mutual
/-- If `EvalExpr ge sp e m le a v` holds, then `evalExpr ge sp e m le a` returns `some v`. -/
theorem eval_expr_complete {locals : LetEnv} {expr : Expr} {value : Val}
    (h : EvalExpr ge stack env memory locals expr value) :
    evalExpr ge stack env memory locals expr = some value := by
  cases h with
  | var _ _ _ h => exact h
  | operation _ _ _ _ _ hargs hop =>
      simp [evalExpr, eval_expr_list_complete hargs, hop]
  | load _ _ _ _ _ _ _ hargs haddress hload =>
      simp [evalExpr, eval_expr_list_complete hargs, haddress, hload]
  | condition _ _ _ _ result _ hcondition hbranch =>
      cases result <;> simpa [evalExpr, eval_cond_expr_complete hcondition] using
        eval_expr_complete hbranch
  | letValue _ _ _ _ _ hvalue hbody =>
      simp [evalExpr, eval_expr_complete hvalue, eval_expr_complete hbody]
  | letVar _ _ _ h => exact h

/-- If `EvalExprList` holds for an expression list, then `evalExprList` returns those values. -/
theorem eval_expr_list_complete {locals : LetEnv} {args : ExprList} {values : List Val}
    (h : EvalExprList ge stack env memory locals args values) :
    evalExprList ge stack env memory locals args = some values := by
  cases h with
  | nil => rfl
  | cons _ _ _ _ _ hhead htail =>
      simp [evalExprList, eval_expr_complete hhead, eval_expr_list_complete htail]

/-- If `EvalCondExpr ge sp e m le c b` holds, then `evalCondExpr ge sp e m le c` returns
`some b`. -/
theorem eval_cond_expr_complete {locals : LetEnv} {condition : CondExpr} {value : Bool}
    (h : EvalCondExpr ge stack env memory locals condition value) :
    evalCondExpr ge stack env memory locals condition = some value := by
  cases h with
  | condition _ _ _ _ _ hargs hop =>
      simp [evalCondExpr, eval_expr_list_complete hargs, hop]
  | branch _ _ _ _ result _ hcondition hbranch =>
      cases result <;> simpa [evalCondExpr, eval_cond_expr_complete hcondition] using
        eval_cond_expr_complete hbranch
  | letValue _ _ _ _ _ hvalue hbody =>
      simp [evalCondExpr, eval_expr_complete hvalue, eval_cond_expr_complete hbody]
end

mutual
/-- If `evalExpr ge sp e m le a` returns `some v`, then `EvalExpr ge sp e m le a v` holds. -/
theorem eval_expr_sound {locals : LetEnv} {expr : Expr} {value : Val}
    (h : evalExpr ge stack env memory locals expr = some value) :
    EvalExpr ge stack env memory locals expr value := by
  cases expr with
  | Evar name => exact .var _ _ _ h
  | Eop op args =>
      simp only [evalExpr, bind, Option.bind_eq_some_iff] at h
      obtain ⟨values, hargs, hop⟩ := h
      exact .operation _ _ _ _ _ (eval_expr_list_sound hargs) hop
  | Eload chunk address args =>
      simp only [evalExpr, bind, Option.bind_eq_some_iff] at h
      obtain ⟨values, hargs, pointer, haddress, hload⟩ := h
      exact .load _ _ _ _ _ _ _ (eval_expr_list_sound hargs) haddress hload
  | Econdition condition yes no =>
      simp only [evalExpr, bind, Option.bind_eq_some_iff] at h
      obtain ⟨result, hcondition, hbranch⟩ := h
      cases result <;>
        exact .condition _ _ _ _ _ _ (eval_cond_expr_sound hcondition)
          (eval_expr_sound hbranch)
  | Elet input body =>
      simp only [evalExpr, bind, Option.bind_eq_some_iff] at h
      obtain ⟨value, hvalue, hbody⟩ := h
      exact .letValue _ _ _ _ _ (eval_expr_sound hvalue) (eval_expr_sound hbody)
  | Eletvar index => exact .letVar _ _ _ h

/-- If `evalExprList` returns `some vs` for an expression list, then `EvalExprList` holds. -/
theorem eval_expr_list_sound {locals : LetEnv} {args : ExprList} {values : List Val}
    (h : evalExprList ge stack env memory locals args = some values) :
    EvalExprList ge stack env memory locals args values := by
  cases args with
  | Enil =>
      cases h
      exact .nil _
  | Econs head tail =>
      simp only [evalExprList, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨value, hhead, rest, htail, rfl⟩ := h
      exact .cons _ _ _ _ _ (eval_expr_sound hhead) (eval_expr_list_sound htail)

/-- If `evalCondExpr ge sp e m le c` returns `some b`, then `EvalCondExpr ge sp e m le c b`
holds. -/
theorem eval_cond_expr_sound {locals : LetEnv} {condition : CondExpr} {value : Bool}
    (h : evalCondExpr ge stack env memory locals condition = some value) :
    EvalCondExpr ge stack env memory locals condition value := by
  cases condition with
  | CEcond condition args =>
      simp only [evalCondExpr, bind, Option.bind_eq_some_iff] at h
      obtain ⟨values, hargs, hop⟩ := h
      exact .condition _ _ _ _ _ (eval_expr_list_sound hargs) hop
  | CEcondition condition yes no =>
      simp only [evalCondExpr, bind, Option.bind_eq_some_iff] at h
      obtain ⟨result, hcondition, hbranch⟩ := h
      cases result <;>
        exact .branch _ _ _ _ _ _ (eval_cond_expr_sound hcondition)
          (eval_cond_expr_sound hbranch)
  | CElet input body =>
      simp only [evalCondExpr, bind, Option.bind_eq_some_iff] at h
      obtain ⟨value, hvalue, hbody⟩ := h
      exact .letValue _ _ _ _ _ (eval_expr_sound hvalue) (eval_cond_expr_sound hbody)
end

variable {locals : LetEnv}

/-- `EvalExpr` holds exactly when `evalExpr` returns that value. -/
theorem eval_expr_iff {expr : Expr} {value : Val} :
    EvalExpr ge stack env memory locals expr value ↔
      evalExpr ge stack env memory locals expr = some value :=
  ⟨eval_expr_complete, eval_expr_sound⟩

/-- `EvalExprList` holds exactly when `evalExprList` returns those values. -/
theorem eval_expr_list_iff {args : ExprList} {values : List Val} :
    EvalExprList ge stack env memory locals args values ↔
      evalExprList ge stack env memory locals args = some values :=
  ⟨eval_expr_list_complete, eval_expr_list_sound⟩

/-- `EvalCondExpr` holds exactly when `evalCondExpr` returns that boolean. -/
theorem eval_cond_expr_iff {condition : CondExpr} {value : Bool} :
    EvalCondExpr ge stack env memory locals condition value ↔
      evalCondExpr ge stack env memory locals condition = some value :=
  ⟨eval_cond_expr_complete, eval_cond_expr_sound⟩

/-- An expression evaluates to at most one value. -/
theorem eval_expr_deterministic {expr : Expr} {value other : Val}
    (h : EvalExpr ge stack env memory locals expr value)
    (hother : EvalExpr ge stack env memory locals expr other) : value = other :=
  Option.some.inj ((eval_expr_complete h).symm.trans (eval_expr_complete hother))

/-- An expression list evaluates to at most one list of values. -/
theorem eval_expr_list_deterministic {args : ExprList} {values other : List Val}
    (h : EvalExprList ge stack env memory locals args values)
    (hother : EvalExprList ge stack env memory locals args other) : values = other :=
  Option.some.inj ((eval_expr_list_complete h).symm.trans (eval_expr_list_complete hother))

/-- A conditional expression evaluates to at most one boolean. -/
theorem eval_cond_expr_deterministic {condition : CondExpr} {value other : Bool}
    (h : EvalCondExpr ge stack env memory locals condition value)
    (hother : EvalCondExpr ge stack env memory locals condition other) : value = other :=
  Option.some.inj ((eval_cond_expr_complete h).symm.trans (eval_cond_expr_complete hother))

end Quadrature.CminorSel
