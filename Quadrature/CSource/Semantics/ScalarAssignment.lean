import Quadrature.CSource.Semantics.ScalarReduction
import Quadrature.CSource.Semantics.Control

/-!
# Initializing a scalar local

A constant assignment resolves its local variable and performs one store.
`assign_constant_total` composes these unique expression reductions with
the statement control steps. It makes no assumption about the local's
previous contents.
-/

namespace Quadrature.CSource.C

open CC hiding State Cont Step
open SmallStep

variable [ExternalCalls]

/-- Resolving the local is the only possible first step when assigning a computed value. -/
theorem ExpressionReduction.assign_local {ge : GlobalEnv} {locals : Env} {memory : Mem}
    {name : Ident} {block : Block} {type : Ty}
    (hlocal : locals.get name = some (block, type)) (value : Val) (valueType : Ty) :
    ExpressionReduction ge locals memory
      (.Eassign (.Evar name type) (.Eval value valueType) type)
      (.Eassign (.Eloc block Integers.Ptrofs.zero .Full type) (.Eval value valueType) type)
      memory := by
  have hl : Lred ge.expressionEnv locals (.Evar name type) memory
      (.Eloc block Integers.Ptrofs.zero .Full type) memory :=
    .var_local _ _ _ _ hlocal
  have hi : ImmSafe ge locals .LV (.Evar name type) memory :=
    .lred _ id _ _ _ _ hl (.top _)
  constructor
  · intro function cont
    exact .lred (fun expr => .Eassign expr (.Eval value valueType) type) _ _ _ _ _ _ _ hl
      (.assign_left _ id _ _ (.top _))
  · intro function cont trace next hmachine
    generalize hexpr : Expr.Eassign (.Evar name type) (.Eval value valueType) type = whole
      at hmachine
    cases hmachine with
    | lred context _ arg _ _ _ reduced last hred hcontext =>
        rcases hcontext.assign_cases hexpr with
          ⟨hk, _, _⟩ | ⟨inner, hc, rfl, he⟩ | ⟨inner, hc, _, he⟩
        · cases hk
        · obtain ⟨_, rfl, rfl⟩ := hc.variable_cases he
          cases hred with
          | var_local _ _ _ actual ha =>
              have heq := Option.some.inj (ha.symm.trans hlocal)
              have hb := Prod.mk.inj heq |>.1
              subst actual
              exact ⟨rfl, rfl⟩
          | var_global _ _ _ _ hn _ => simp [hlocal] at hn
        · exact False.elim
            (((he ▸ Normal.value value valueType).in_context hc).not_lred hred)
    | rred context _ arg _ _ _ trace reduced last hred hcontext =>
        rcases hcontext.assign_cases hexpr with
          ⟨_, rfl, rfl⟩ | ⟨inner, hc, _, he⟩ | ⟨inner, hc, _, he⟩
        · cases hred
        · obtain ⟨hk, _, _⟩ := hc.variable_cases he
          cases hk
        · exact False.elim
            (((he ▸ Normal.value value valueType).in_context hc).not_rred hred)
    | call context _ arg _ _ _ callee args callType hcall hcontext =>
        rcases hcontext.assign_cases hexpr with
          ⟨_, rfl, rfl⟩ | ⟨inner, hc, _, he⟩ | ⟨inner, hc, _, he⟩
        · cases hcall
        · obtain ⟨hk, _, _⟩ := hc.variable_cases he
          cases hk
        · exact False.elim
            (((he ▸ Normal.value value valueType).in_context hc).not_callred hcall)
    | stuck context _ arg _ _ _ kind hcontext hunsafe =>
        rcases hcontext.assign_cases hexpr with
          ⟨rfl, rfl, rfl⟩ | ⟨inner, hc, _, he⟩ | ⟨inner, hc, _, he⟩
        · apply False.elim
          apply hunsafe
          exact .lred _ (fun expr => .Eassign expr (.Eval value valueType) type)
            _ _ _ _ hl (.assign_left _ id _ _ (.top _))
        · obtain ⟨rfl, rfl, rfl⟩ := hc.variable_cases he
          exact False.elim (hunsafe hi)
        · exact False.elim
            (hunsafe ((he ▸ Normal.value value valueType).in_context hc).imm_safe)

/-- Assigning a constant to a nonvolatile scalar local terminates at exactly the given store. -/
theorem assign_constant_total (ge : GlobalEnv) (locals : Env) (memory final : Mem)
    (name : Ident) (block : Block) (type : Ty) (chunk : Chunk) (value : Val)
    (hname : locals.get name = some (block, type))
    (hmode : accessMode type = .By_value chunk) (hv : typeIsVolatile type = false)
    (hcast : Cop.semCast value type type memory = some value)
    (hstore : Mem.store chunk memory block 0 value = some final)
    (function : Function) (cont : Cont) :
    Total ge (fun result => result = .statement function .Sskip cont locals final)
      (.statement function (.Sdo (.Eassign (.Evar name type) (.Eval value type) type))
        cont locals memory) := by
  apply Total.statement (.do_start _ _ _ _ _)
  apply (ExpressionReduction.assign_local hname value type).total
  apply (ExpressionReduction.assign (block := block) (offset := Integers.Ptrofs.zero)
    hmode hv hcast hstore).total
  apply Total.value (.do_finish _ _ _ _ _ _)
  exact .done rfl

end Quadrature.CSource.C
