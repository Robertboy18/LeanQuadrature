import Quadrature.CSource.Semantics.ContextInversion

/-!
# Sequencing deterministic expression steps

A comma expression must finish its left operand before evaluating its right.
An assignment with a computed destination must finish its right operand before
storing. The two lemmas below preserve a unique reduction inside these contexts.
-/

namespace Quadrature.CSource.C

open CC hiding State Cont Step
open SmallStep

variable [ExternalCalls]

/-- A unique reduction fixes its expression result and memory separately. -/
theorem ExpressionReduction.result_eq {ge : GlobalEnv} {locals : Env}
    {memory final last : Mem} {expr result reduced : Expr}
    (h : ExpressionReduction ge locals memory expr result final)
    {function : Function} {cont : Cont} {trace : Trace}
    (hstep : ExprStep ge (.expression function expr cont locals memory) trace
      (.expression function reduced cont locals last)) :
    trace = E0 ∧ reduced = result ∧ last = final := by
  obtain ⟨ht, he⟩ := h.unique function cont trace _ hstep
  simpa only [State.expression.injEq, true_and, and_true] using And.intro ht he

/-- A unique step in the left operand remains unique inside comma sequencing. -/
theorem ExpressionReduction.comma {ge : GlobalEnv} {locals : Env} {memory final : Mem}
    {expr result : Expr} (h : ExpressionReduction ge locals memory expr result final)
    (right : Expr) (type : Ty) :
    ExpressionReduction ge locals memory (.Ecomma expr right type)
      (.Ecomma result right type) final := by
  constructor
  · intro function cont
    cases h.step function cont with
    | lred context _ _ _ _ _ _ _ hred hcontext =>
        exact .lred (fun arg => .Ecomma (context arg) right type) _ _ _ _ _ _ _ hred
          (.comma _ context right type hcontext)
    | rred context _ _ _ _ _ _ _ _ hred hcontext =>
        exact .rred (fun arg => .Ecomma (context arg) right type) _ _ _ _ _ _ _ _ hred
          (.comma _ context right type hcontext)
  · intro function cont trace next hmachine
    generalize hexpr : Expr.Ecomma expr right type = whole at hmachine
    cases hmachine with
    | lred context caller arg cont locals memory reduced last hred hcontext =>
        rcases hcontext.comma_cases hexpr with
          ⟨hk, _, _⟩ | ⟨inner, hi, rfl, he⟩
        · cases hk
        · rw [he] at h
          obtain ⟨_, rfl, rfl⟩ := h.result_eq
            (.lred inner function arg cont locals memory reduced last hred hi)
          exact ⟨rfl, rfl⟩
    | rred context caller arg cont locals memory trace reduced last hred hcontext =>
        rcases hcontext.comma_cases hexpr with
          ⟨_, rfl, rfl⟩ | ⟨inner, hi, rfl, he⟩
        · cases hred with
          | comma value valueType _ _ _ _ =>
              exact False.elim (h.not_value function cont value valueType rfl)
        · rw [he] at h
          obtain ⟨rfl, rfl, rfl⟩ := h.result_eq
            (.rred inner function arg cont locals memory trace reduced last hred hi)
          exact ⟨rfl, rfl⟩
    | call context caller arg cont locals memory callee args callType hcall hcontext =>
        rcases hcontext.comma_cases hexpr with
          ⟨_, rfl, rfl⟩ | ⟨inner, hi, rfl, he⟩
        · cases hcall
        · rw [he] at h
          have hh := (h.unique function cont _ _
            (.call inner function arg cont locals memory callee args callType hcall hi)).2
          cases hh
    | stuck context caller arg cont locals memory kind hcontext hunsafe =>
        rcases hcontext.comma_cases hexpr with
          ⟨rfl, rfl, rfl⟩ | ⟨inner, hi, _, he⟩
        · apply False.elim
          apply hunsafe
          apply (h.imm_safe function cont).value_context (.comma _ id right type (.top _))
          intro value valueType he
          exact False.elim (h.not_value function cont value valueType he)
        · exact False.elim (hunsafe (h.not_stuck function cont _ _ _ hi he))

/-- With a computed destination, a unique right-operand step remains unique inside
assignment. -/
theorem ExpressionReduction.assign_right {ge : GlobalEnv} {locals : Env} {memory final : Mem}
    {expr result : Expr} (h : ExpressionReduction ge locals memory expr result final)
    (block : Block) (offset : Integers.Ptrofs) (bitfield : Bitfield) (type : Ty) :
    ExpressionReduction ge locals memory (.Eassign (.Eloc block offset bitfield type) expr type)
      (.Eassign (.Eloc block offset bitfield type) result type) final := by
  constructor
  · intro function cont
    cases h.step function cont with
    | lred context _ _ _ _ _ _ _ hred hcontext =>
        exact .lred
          (fun arg => .Eassign (.Eloc block offset bitfield type) (context arg) type)
          _ _ _ _ _ _ _ hred (.assign_right _ context _ type hcontext)
    | rred context _ _ _ _ _ _ _ _ hred hcontext =>
        exact .rred
          (fun arg => .Eassign (.Eloc block offset bitfield type) (context arg) type)
          _ _ _ _ _ _ _ _ hred (.assign_right _ context _ type hcontext)
  · intro function cont trace next hmachine
    generalize hexpr : Expr.Eassign (.Eloc block offset bitfield type) expr type = whole
      at hmachine
    cases hmachine with
    | lred context caller arg cont locals memory reduced last hred hcontext =>
        rcases hcontext.assign_cases hexpr with
          ⟨hk, _, _⟩ | ⟨inner, hi, _, he⟩ | ⟨inner, hi, rfl, he⟩
        · cases hk
        · exact False.elim
            (((he ▸ Normal.location block offset bitfield type).in_context hi).not_lred hred)
        · rw [he] at h
          obtain ⟨_, rfl, rfl⟩ := h.result_eq
            (.lred inner function arg cont locals memory reduced last hred hi)
          exact ⟨rfl, rfl⟩
    | rred context caller arg cont locals memory trace reduced last hred hcontext =>
        rcases hcontext.assign_cases hexpr with
          ⟨_, rfl, rfl⟩ | ⟨inner, hi, _, he⟩ | ⟨inner, hi, rfl, he⟩
        · cases hred with
          | assign _ _ _ _ value valueType _ _ _ _ _ _ _ =>
              exact False.elim (h.not_value function cont value valueType rfl)
        · exact False.elim
            (((he ▸ Normal.location block offset bitfield type).in_context hi).not_rred hred)
        · rw [he] at h
          obtain ⟨rfl, rfl, rfl⟩ := h.result_eq
            (.rred inner function arg cont locals memory trace reduced last hred hi)
          exact ⟨rfl, rfl⟩
    | call context caller arg cont locals memory callee args callType hcall hcontext =>
        rcases hcontext.assign_cases hexpr with
          ⟨_, rfl, rfl⟩ | ⟨inner, hi, _, he⟩ | ⟨inner, hi, rfl, he⟩
        · cases hcall
        · exact False.elim
            (((he ▸ Normal.location block offset bitfield type).in_context hi).not_callred hcall)
        · rw [he] at h
          have hh := (h.unique function cont _ _
            (.call inner function arg cont locals memory callee args callType hcall hi)).2
          cases hh
    | stuck context caller arg cont locals memory kind hcontext hunsafe =>
        rcases hcontext.assign_cases hexpr with
          ⟨rfl, rfl, rfl⟩ | ⟨inner, hi, _, he⟩ | ⟨inner, hi, _, he⟩
        · apply False.elim
          apply hunsafe
          apply (h.imm_safe function cont).value_context
            (.assign_right _ id (.Eloc block offset bitfield type) type (.top _))
          intro value valueType he
          exact False.elim (h.not_value function cont value valueType he)
        · exact False.elim
            (hunsafe ((he ▸ Normal.location block offset bitfield type).in_context hi).imm_safe)
        · exact False.elim (hunsafe (h.not_stuck function cont _ _ _ hi he))

end Quadrature.CSource.C
