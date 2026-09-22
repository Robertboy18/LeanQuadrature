import Quadrature.CSource.Semantics.HeadExpression

/-!
# Composing a uniquely determined expression reduction

`ExpressionReduction` records one silent expression step and proves that
there are no other successors. Its composition lemmas retain this property
inside sequencing and assignment, where the surrounding operation must wait
for the operand.
-/

namespace Quadrature.CSource.C

open CC hiding State Cont Step
open SmallStep

variable [ExternalCalls]

/-- One silent expression reduction, uniform in the surrounding function and continuation,
is the only permitted transition. -/
structure ExpressionReduction (ge : GlobalEnv) (locals : Env) (memory : Mem)
    (expr result : Expr) (final : Mem) : Prop where
  step : ∀ function cont,
    ExprStep ge (.expression function expr cont locals memory) E0
      (.expression function result cont locals final)
  unique : ∀ function cont trace next,
    ExprStep ge (.expression function expr cont locals memory) trace next →
      trace = E0 ∧ next = .expression function result cont locals final

/-- An expression with a proper reduction is not yet a value. -/
theorem ExpressionReduction.not_value {ge : GlobalEnv} {locals : Env} {memory final : Mem}
    {expr result : Expr} (h : ExpressionReduction ge locals memory expr result final)
    (function : Function) (cont : Cont) (value : Val) (type : Ty) :
    expr ≠ .Eval value type := by
  intro heq
  have hs := h.step function cont
  rw [heq] at hs
  exact hs.not_value

/-- A unique expression reduction is immediately safe. -/
theorem ExpressionReduction.imm_safe {ge : GlobalEnv} {locals : Env} {memory final : Mem}
    {expr result : Expr} (h : ExpressionReduction ge locals memory expr result final)
    (function : Function) (cont : Cont) :
    ImmSafe ge locals .RV expr memory := by
  cases h.step function cont with
  | lred context _ _ _ _ _ _ _ hred hcontext =>
      exact .lred _ context _ _ _ _ hred hcontext
  | rred context _ _ _ _ _ _ _ _ hred hcontext =>
      exact .rred _ context _ _ _ _ _ hred hcontext

/-- Uniqueness excludes the explicit transition to a stuck state at every exposed position. -/
theorem ExpressionReduction.not_stuck {ge : GlobalEnv} {locals : Env} {memory final : Mem}
    {expr result : Expr} (h : ExpressionReduction ge locals memory expr result final)
    (function : Function) (cont : Cont) :
    NotStuck ge locals expr memory := by
  intro kind context arg hcontext heq
  by_contra hunsafe
  have hs : ExprStep ge (.expression function expr cont locals memory) E0 .stuck := by
    rw [heq]
    exact .stuck _ _ _ _ _ _ _ hcontext hunsafe
  have he := (h.unique function cont _ _ hs).2
  cases he

/-- A unique head rule with computed operands supplies a unique expression reduction. -/
theorem ExpressionReduction.head {ge : GlobalEnv} {locals : Env} {memory final : Mem}
    {expr result : Expr} (hform : HeadForm expr)
    (hred : Rred ge expr memory E0 result final)
    (hunique : ∀ trace reduced last, Rred ge expr memory trace reduced last →
      trace = E0 ∧ reduced = result ∧ last = final) :
    ExpressionReduction ge locals memory expr result final :=
  ⟨fun _ _ => .rred id _ _ _ _ _ _ _ _ hred (.top _),
    fun _ _ _ _ h => head_step_unique hform hred hunique (.inl h)⟩

/-- Prepend a unique expression reduction to a total computation. -/
theorem ExpressionReduction.total {ge : GlobalEnv} {locals : Env} {memory final : Mem}
    {expr result : Expr} (h : ExpressionReduction ge locals memory expr result final)
    {post : State → Prop} {function : Function} {cont : Cont}
    (hnext : Total ge post (.expression function result cont locals final)) :
    Total ge post (.expression function expr cont locals memory) := by
  apply Total.single (.inl (h.step function cont)) ?_ hnext
  intro trace next hstep
  rcases hstep with hstep | hstep
  · exact h.unique function cont trace next hstep
  · obtain ⟨value, type, heq⟩ := hstep.expression_value
    exact False.elim (h.not_value function cont value type heq)

end Quadrature.CSource.C
