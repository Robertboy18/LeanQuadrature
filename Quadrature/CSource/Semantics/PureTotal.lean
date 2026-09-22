import Quadrature.CSource.Semantics.PureProgress
import Quadrature.CSource.Semantics.TotalCorrectness

/-!
# Total correctness of pure C expressions

`EvalRvalue.total` connects the existing arithmetic proofs to every reduction
order of the C machine. Every reduction preserves the value, type, and memory,
and decreases the number of syntax operations. The proof excludes both
undefined behavior and infinite expression evaluation.
-/

namespace Quadrature.CSource.C

open CC

/-- Computing a location removes a syntax operation. -/
theorem Lred.work_lt {ge : ExpressionEnv} {locals : Env} {memory final : Mem}
    {expr result : Expr} (h : Lred ge locals expr memory result final) :
    result.work < expr.work := by
  cases h <;> simp [Expr.work]

variable [ExternalCalls]

/-- Reducing a pure value expression removes a syntax operation. -/
theorem Rred.pure_work_lt {ge : GlobalEnv} {locals : Env} {memory final : Mem}
    {expr result : Expr} {trace : Trace} {value : PureResult}
    (hstep : Rred ge expr memory trace result final)
    (heval : PureEval ge.expressionEnv locals memory .RV expr value) :
    result.work < expr.work := by
  cases hstep <;> cases heval with
  | value h => cases h <;> simp [Expr.work]

omit [ExternalCalls] in
/-- A pure expression cannot be a function call ready to enter its body. -/
theorem Callred.not_pure {ge : GlobalEnv} {locals : Env} {memory : Mem}
    {expr : Expr} {function : FunDef} {args : List Val} {type : Ty} {value : PureResult}
    (hcall : Callred ge expr memory function args type) :
    ¬ PureEval ge.expressionEnv locals memory .RV expr value := by
  intro heval
  cases hcall
  cases heval with
  | value h => cases h

namespace SmallStep

/-- Statement control can consume an expression only after it has become a value. -/
theorem StmtStep.expression_value {ge : GlobalEnv} {function : Function} {expr : Expr}
    {cont : Cont} {locals : Env} {memory : Mem} {trace : Trace} {next : State}
    (hstep : StmtStep ge (.expression function expr cont locals memory) trace next) :
    ∃ value type, expr = .Eval value type := by
  cases hstep <;> exact ⟨_, _, rfl⟩

/-- Every machine expression step of a pure expression preserves its meaning and decreases
its remaining work. In particular, no call or undefined-behavior step is possible. -/
theorem ExprStep.pure {ge : GlobalEnv} {function : Function} {expr : Expr} {cont : Cont}
    {locals : Env} {memory : Mem} {trace : Trace} {next : State} {value : Val}
    (hstep : ExprStep ge (.expression function expr cont locals memory) trace next)
    (heval : EvalRvalue ge.expressionEnv locals memory expr value) :
    trace = E0 ∧ ∃ reduced,
      next = .expression function reduced cont locals memory ∧
      typeof reduced = typeof expr ∧ reduced.work < expr.work ∧
      EvalRvalue ge.expressionEnv locals memory reduced value := by
  cases hstep with
  | lred context function arg cont locals memory result final hstep hcontext =>
      obtain ⟨operand, harg, hreplace⟩ :=
        (PureEval.value heval).in_context hcontext
      have htype := hstep.typeof_eq
      have hwork := hstep.work_lt
      have hresult := hstep.pure_eval harg
      cases hstep.memory_eq
      cases hreplace result htype hresult with
      | value hresult =>
          exact ⟨rfl, context result, rfl, hcontext.typeof_eq htype,
            hcontext.work_lt hwork, hresult⟩
  | rred context function arg cont locals memory trace result final hstep hcontext =>
      obtain ⟨operand, harg, hreplace⟩ :=
        (PureEval.value heval).in_context hcontext
      have htype := hstep.typeof_eq
      have hwork := hstep.pure_work_lt harg
      obtain ⟨rfl, hmemory, hresult⟩ := hstep.pure_eval harg
      subst final
      cases hreplace result htype hresult with
      | value hresult =>
          exact ⟨rfl, context result, rfl, hcontext.typeof_eq htype,
            hcontext.work_lt hwork, hresult⟩
  | call context function arg cont locals memory callee args type hcall hcontext =>
      obtain ⟨operand, harg, _⟩ := (PureEval.value heval).in_context hcontext
      exact False.elim (hcall.not_pure harg)
  | stuck context function arg cont locals memory kind hcontext hunsafe =>
      exact False.elim (hunsafe ((PureEval.value heval).not_stuck _ _ _ hcontext rfl))

/-- An already computed value has no expression-reduction step. -/
theorem ExprStep.not_value {ge : GlobalEnv} {function : Function} {value : Val} {type : Ty}
    {cont : Cont} {locals : Env} {memory : Mem} {trace : Trace} {next : State} :
    ¬ ExprStep ge (.expression function (.Eval value type) cont locals memory) trace next := by
  intro h
  obtain ⟨_, reduced, _, _, hwork, _⟩ := h.pure (.value _ _)
  exact Nat.not_lt_zero _ hwork

/-- A pure nonvalue expression can take a machine step. -/
theorem pure_progress {ge : GlobalEnv} {function : Function} {expr : Expr}
    {cont : Cont} {locals : Env} {memory : Mem} {value : Val}
    (heval : EvalRvalue ge.expressionEnv locals memory expr value)
    (hnormal : expr ≠ .Eval value (typeof expr)) :
    ∃ trace next, Step ge (.expression function expr cont locals memory) trace next := by
  have hsafe := (PureEval.value heval).imm_safe
  cases hsafe with
  | value value type memory =>
      cases heval
      exact False.elim (hnormal rfl)
  | lred _ context arg memory result final hstep hcontext =>
      exact ⟨_, _, .inl (.lred _ _ _ _ _ _ _ _ hstep hcontext)⟩
  | rred _ context arg memory trace result final hstep hcontext =>
      exact ⟨_, _, .inl (.rred _ _ _ _ _ _ _ _ _ hstep hcontext)⟩
  | callred _ context arg memory callee args type hcall hcontext =>
      obtain ⟨operand, harg, _⟩ := (PureEval.value heval).in_context hcontext
      exact False.elim (hcall.not_pure harg)

/-- Before a pure expression becomes its value, every machine step is an expression step. -/
theorem pure_step {ge : GlobalEnv} {function : Function} {expr : Expr}
    {cont : Cont} {locals : Env} {memory : Mem} {value : Val} {trace : Trace} {next : State}
    (heval : EvalRvalue ge.expressionEnv locals memory expr value)
    (hnormal : expr ≠ .Eval value (typeof expr))
    (hstep : Step ge (.expression function expr cont locals memory) trace next) :
    ExprStep ge (.expression function expr cont locals memory) trace next := by
  rcases hstep with hstep | hstep
  · exact hstep
  · obtain ⟨value, type, rfl⟩ := hstep.expression_value
    cases heval
    exact False.elim (hnormal rfl)

end SmallStep

/-- Every evaluation order computes the pure expression's value in finitely many silent steps,
without changing memory or consuming the enclosing statement's continuation. -/
theorem EvalRvalue.total {ge : GlobalEnv} {locals : Env} {memory : Mem}
    {expr : Expr} {value : Val} (heval : EvalRvalue ge.expressionEnv locals memory expr value)
    (function : Function) (cont : SmallStep.Cont) :
    SmallStep.Total ge
      (fun state => state = .expression function (.Eval value (typeof expr)) cont locals memory)
      (.expression function expr cont locals memory) := by
  by_cases hnormal : expr = .Eval value (typeof expr)
  · exact .done (congrArg (fun expr =>
      SmallStep.State.expression function expr cont locals memory) hnormal)
  · refine .step (SmallStep.pure_progress heval hnormal) ?_ ?_
    · intro trace next hstep
      exact ((SmallStep.pure_step heval hnormal hstep).pure heval).1
    · intro trace next hstep
      obtain ⟨_, reduced, rfl, htype, hwork, hvalue⟩ :=
        (SmallStep.pure_step heval hnormal hstep).pure heval
      exact (hvalue.total function cont).mono (fun state h => by simpa only [htype] using h)
termination_by expr.work

end Quadrature.CSource.C
