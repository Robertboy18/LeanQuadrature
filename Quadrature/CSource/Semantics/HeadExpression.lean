import Quadrature.CSource.Semantics.Control

/-!
# Expressions with all operands computed

`HeadForm` says that every proper exposed operand is already a value or
location. Such an expression can only take its head reduction.
`SmallStep.Total.head` uses this fact for the intermediate expressions
introduced by C's post-increment rule.
-/

namespace Quadrature.CSource.C

open CC hiding State Cont Step

/-- A computed rvalue or lvalue needs no further expression reduction. -/
inductive Normal : Kind → Expr → Prop where
  | value (value type) : Normal .RV (.Eval value type)
  | location (block offset bitfield type) : Normal .LV (.Eloc block offset bitfield type)

/-- Every position exposed inside a computed operand is also computed. -/
theorem Normal.in_context {input output : Kind} {context : Expr → Expr} {expr : Expr}
    (hcontext : Context input output context) (hnormal : Normal output (context expr)) :
    Normal input expr := by
  cases hcontext <;> cases hnormal <;> constructor

/-- All proper positions exposed by an expression are computed operands. -/
def HeadForm (expr : Expr) : Prop :=
  ∀ kind context arg, Context kind .RV context → expr = context arg →
    (kind = .RV ∧ context = id) ∨ Normal kind arg

variable [ExternalCalls]

/-- A computed operand is immediately safe. -/
theorem Normal.imm_safe {ge : GlobalEnv} {locals : Env} {memory : Mem}
    {kind : Kind} {expr : Expr} (h : Normal kind expr) :
    ImmSafe ge locals kind expr memory := by
  cases h with
  | value => exact .value _ _ _
  | location => exact .location _ _ _ _ _

omit [ExternalCalls] in
/-- A computed lvalue cannot reduce further. -/
theorem Normal.not_lred {ge : ExpressionEnv} {locals : Env} {memory final : Mem}
    {expr result : Expr} (h : Normal .LV expr) :
    ¬ Lred ge locals expr memory result final := by
  cases h
  intro hred
  cases hred

/-- A computed rvalue cannot reduce further. -/
theorem Normal.not_rred {ge : GlobalEnv} {memory final : Mem}
    {expr result : Expr} {trace : Trace} (h : Normal .RV expr) :
    ¬ Rred ge expr memory trace result final := by
  cases h
  intro hred
  cases hred

omit [ExternalCalls] in
/-- A computed rvalue is not a pending function call. -/
theorem Normal.not_callred {ge : GlobalEnv} {memory : Mem}
    {expr : Expr} {function : FunDef} {args : List Val} {type : Ty}
    (h : Normal .RV expr) : ¬ Callred ge expr memory function args type := by
  cases h
  intro hcall
  cases hcall

/-- A head reduction and computed proper operands make every exposed position safe. -/
theorem HeadForm.not_stuck {ge : GlobalEnv} {locals : Env} {memory final : Mem}
    {expr result : Expr} {trace : Trace}
    (hform : HeadForm expr) (hred : Rred ge expr memory trace result final) :
    NotStuck ge locals expr memory := by
  intro kind context arg hcontext heq
  rcases hform _ _ _ hcontext heq with ⟨rfl, rfl⟩ | hnormal
  · subst expr
    exact .rred _ id _ _ _ _ _ hred (.top _)
  · exact hnormal.imm_safe

namespace SmallStep

/-- A head reduction is the only possible machine step when every proper operand is computed
and the head rule has a unique result. -/
theorem head_step_unique {ge : GlobalEnv} {function : Function}
    {cont : Cont} {locals : Env} {memory final : Mem} {expr result : Expr}
    (hform : HeadForm expr)
    (hred : Rred ge expr memory E0 result final)
    (hunique : ∀ trace reduced last, Rred ge expr memory trace reduced last →
      trace = E0 ∧ reduced = result ∧ last = final)
    {trace : Trace} {next : State}
    (hmachine : Step ge (.expression function expr cont locals memory) trace next) :
    trace = E0 ∧ next = .expression function result cont locals final := by
  rcases hmachine with hmachine | hmachine
  · cases hmachine with
    | lred context function arg cont locals memory reduced last hstep hcontext =>
        rcases hform _ _ _ hcontext rfl with ⟨heq, _⟩ | hnormal
        · cases heq
        · exact False.elim (hnormal.not_lred hstep)
    | rred context function arg cont locals memory trace reduced last hstep hcontext =>
        rcases hform _ _ _ hcontext rfl with ⟨_, rfl⟩ | hnormal
        · obtain ⟨rfl, rfl, rfl⟩ := hunique _ _ _ hstep
          exact ⟨rfl, rfl⟩
        · exact False.elim (hnormal.not_rred hstep)
    | call context function arg cont locals memory callee args type hcall hcontext =>
        rcases hform _ _ _ hcontext rfl with ⟨_, rfl⟩ | hnormal
        · cases hcall
          cases hred
        · exact False.elim (hnormal.not_callred hcall)
    | stuck context function arg cont locals memory kind hcontext hunsafe =>
        exact False.elim (hunsafe (hform.not_stuck hred _ _ _ hcontext rfl))
  · obtain ⟨value, type, rfl⟩ := hmachine.expression_value
    cases hred

/-- Prepend the sole head reduction of an expression whose operands are computed. -/
theorem Total.head {ge : GlobalEnv} {post : State → Prop} {function : Function}
    {cont : Cont} {locals : Env} {memory final : Mem} {expr result : Expr}
    (hform : HeadForm expr)
    (hred : Rred ge expr memory E0 result final)
    (hunique : ∀ trace reduced last, Rred ge expr memory trace reduced last →
      trace = E0 ∧ reduced = result ∧ last = final)
    (hnext : Total ge post (.expression function result cont locals final)) :
    Total ge post (.expression function expr cont locals memory) :=
  .single (.inl (.rred id _ _ _ _ _ _ _ _ hred (.top _)))
    (fun _ _ h => head_step_unique hform hred hunique h) hnext

end SmallStep
end Quadrature.CSource.C
