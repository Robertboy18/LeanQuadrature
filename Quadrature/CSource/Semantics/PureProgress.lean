import Quadrature.CSource.Semantics.Contexts
import Quadrature.CSource.Semantics.PureReduction

/-!
# Progress and safety of pure C expressions

`PureEval.imm_safe` proves that a meaningful pure expression is a value or
can take a reduction step. Applying it to every exposed operand gives
`PureEval.not_stuck`, which excludes the C machine's undefined-behavior
transition regardless of operand order.
-/

namespace Quadrature.CSource.C

open CC

variable [ExternalCalls]

/-- Lift progress through a value context, separately handling an already computed operand. -/
theorem ImmSafe.value_context {ge : GlobalEnv} {locals : Env} {memory : Mem}
    {kind : Kind} {context : Expr → Expr} {expr : Expr}
    (hsafe : ImmSafe ge locals .RV expr memory) (hcontext : Context .RV kind context)
    (hvalue : ∀ value type, expr = .Eval value type →
      ImmSafe ge locals kind (context (.Eval value type)) memory) :
    ImmSafe ge locals kind (context expr) memory := by
  cases hsafe with
  | value value type memory => exact hvalue value type rfl
  | lred _ inner arg memory result final hstep hinner =>
      exact .lred _ (fun arg => context (inner arg)) arg _ _ _ hstep (hcontext.comp hinner)
  | rred _ inner arg memory trace result final hstep hinner =>
      exact .rred _ (fun arg => context (inner arg)) arg _ _ _ _ hstep (hcontext.comp hinner)
  | callred _ inner arg memory function args type hstep hinner =>
      exact .callred _ (fun arg => context (inner arg)) arg _ _ _ _ hstep (hcontext.comp hinner)

/-- Lift progress through a location context, handling an already computed address. -/
theorem ImmSafe.location_context {ge : GlobalEnv} {locals : Env} {memory : Mem}
    {kind : Kind} {context : Expr → Expr} {expr : Expr}
    (hsafe : ImmSafe ge locals .LV expr memory) (hcontext : Context .LV kind context)
    (hloc : ∀ block offset bitfield type, expr = .Eloc block offset bitfield type →
      ImmSafe ge locals kind (context (.Eloc block offset bitfield type)) memory) :
    ImmSafe ge locals kind (context expr) memory := by
  cases hsafe with
  | location block offset bitfield type memory => exact hloc block offset bitfield type rfl
  | lred _ inner arg memory result final hstep hinner =>
      exact .lred _ (fun arg => context (inner arg)) arg _ _ _ hstep (hcontext.comp hinner)
  | rred _ inner arg memory trace result final hstep hinner =>
      exact .rred _ (fun arg => context (inner arg)) arg _ _ _ _ hstep (hcontext.comp hinner)
  | callred _ inner arg memory function args type hstep hinner =>
      exact .callred _ (fun arg => context (inner arg)) arg _ _ _ _ hstep (hcontext.comp hinner)

/-- An expression with a pure meaning is immediately safe in the full C semantics. -/
theorem PureEval.imm_safe {ge : GlobalEnv} {locals : Env} {memory : Mem}
    {kind : Kind} {expr : Expr} {result : PureResult}
    (heval : PureEval ge.expressionEnv locals memory kind expr result) :
    ImmSafe ge locals kind expr memory := by
  induction expr using Expr.rec (motive_2 := fun _ => True) generalizing kind result with
  | Eval =>
      cases heval with
      | value h =>
          cases h
          exact .value _ _ _
      | location h => cases h
  | Eloc =>
      cases heval with
      | value h => cases h
      | location h =>
          cases h
          exact .location _ _ _ _ _
  | Evar name type =>
      cases heval with
      | value h => cases h
      | location h =>
          cases h with
          | var_local _ _ _ hlocal =>
              exact .lred _ id _ _ _ _ (.var_local _ _ _ _ hlocal) (.top _)
          | var_global _ _ _ hlocal hglobal =>
              exact .lred _ id _ _ _ _ (.var_global _ _ _ _ hlocal hglobal) (.top _)
  | Ederef arg type ih =>
      cases heval with
      | value h => cases h
      | location h =>
          cases h with
          | deref _ _ block offset harg =>
              apply (ih (.value harg)).value_context (.deref _ id type (.top _))
              rintro value valueType rfl
              cases harg
              exact .lred _ id _ _ _ _ (.deref _ _ _ _ _) (.top _)
  | Efield arg name type ih =>
      cases heval with
      | value h => cases h
      | location h =>
          cases h with
          | field_struct _ _ _ block offset nameId composite attr delta bitfield harg ht hc hf =>
              apply (ih (.value harg)).value_context (.field _ id name type (.top _))
              rintro value valueType rfl
              cases harg
              change valueType = .Tstruct nameId attr at ht
              subst valueType
              exact .lred _ id _ _ _ _ (.field_struct _ _ _ _ _ _ _ _ _ _ hc hf) (.top _)
          | field_union _ _ _ block offset nameId composite attr delta bitfield harg ht hf hc =>
              apply (ih (.value harg)).value_context (.field _ id name type (.top _))
              rintro value valueType rfl
              cases harg
              change valueType = .Tunion nameId attr at ht
              subst valueType
              exact .lred _ id _ _ _ _ (.field_union _ _ _ _ _ _ _ _ _ _ hc hf) (.top _)
  | Evalof arg type ih =>
      cases heval with
      | location h => cases h
      | value h =>
          cases h with
          | rvalof block offset bitfield _ _ value harg ht _ hd =>
              apply (ih (.location harg)).location_context (.rvalof _ id type (.top _))
              rintro block offset bitfield argType rfl
              cases harg
              change type = argType at ht
              subst argType
              exact .rred _ id _ _ _ _ _ (.rvalof _ _ _ _ _ _ _ hd) (.top _)
  | Eaddrof arg type ih =>
      cases heval with
      | location h => cases h
      | value h =>
          cases h with
          | addrof block offset _ _ harg =>
              apply (ih (.location harg)).location_context (.addrof _ id type (.top _))
              rintro block offset bitfield argType rfl
              cases harg
              exact .rred _ id _ _ _ _ _ (.addrof _ _ _ _ _) (.top _)
  | Eunop op arg type ih =>
      cases heval with
      | location h => cases h
      | value h =>
          cases h with
          | unop _ _ _ argValue value harg hop =>
              apply (ih (.value harg)).value_context (.unop _ id op type (.top _))
              rintro argValue argType rfl
              cases harg
              exact .rred _ id _ _ _ _ _ (.unop _ _ _ _ _ _ hop) (.top _)
  | Ebinop op left right type ihleft ihright =>
      cases heval with
      | location h => cases h
      | value h =>
          cases h with
          | binop _ _ _ _ leftValue rightValue value hleft hright hop =>
              apply (ihleft (.value hleft)).value_context
                (.binop_left _ id op right type (.top _))
              rintro leftValue leftType rfl
              cases hleft
              apply (ihright (.value hright)).value_context
                (.binop_right _ id op (.Eval _ _) type (.top _))
              rintro rightValue rightType rfl
              cases hright
              exact .rred _ id _ _ _ _ _ (.binop _ _ _ _ _ _ _ _ hop) (.top _)
  | Ecast arg type ih =>
      cases heval with
      | location h => cases h
      | value h =>
          cases h with
          | cast _ _ argValue value harg hcast =>
              apply (ih (.value harg)).value_context (.cast _ id type (.top _))
              rintro argValue argType rfl
              cases harg
              exact .rred _ id _ _ _ _ _ (.cast _ _ _ _ _ hcast) (.top _)
  | Esizeof =>
      cases heval with
      | location h => cases h
      | value h =>
          cases h
          exact .rred _ id _ _ _ _ _ (.sizeof _ _ _) (.top _)
  | Ealignof =>
      cases heval with
      | location h => cases h
      | value h =>
          cases h
          exact .rred _ id _ _ _ _ _ (.alignof _ _ _) (.top _)
  | Eseqand | Eseqor | Econdition | Eassign | Eassignop | Epostincr
  | Ecomma | Ecall | Ebuiltin | Eparen =>
      cases heval with
      | value h => cases h
      | location h => cases h
  | Enil | Econs => trivial

/-- Every exposed operand of a meaningful pure expression is safe. -/
theorem PureEval.not_stuck {ge : GlobalEnv} {locals : Env} {memory : Mem}
    {expr : Expr} {result : PureResult}
    (heval : PureEval ge.expressionEnv locals memory .RV expr result) :
    NotStuck ge locals expr memory := by
  intro kind context arg hcontext heq
  rw [heq] at heval
  obtain ⟨operand, harg, _⟩ := heval.in_context hcontext
  exact harg.imm_safe

end Quadrature.CSource.C
