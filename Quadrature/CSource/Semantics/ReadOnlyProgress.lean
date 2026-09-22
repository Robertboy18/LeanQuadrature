import Quadrature.CSource.Semantics.ReadOnlyReduction

/-!
# Progress of expressions with nested calls

`ReadEval.imm_safe` handles calls in either operand and in any argument.
`ReadEval.not_stuck` then establishes the C safety condition at every exposed
position. A call's argument list either consists of convertible values or
contains a valid expression reduction.
-/

namespace Quadrature.CSource.C

open CC

variable [ExternalCalls]

/-- Arguments are ready for a call, or an argument can reduce. -/
inductive ListProgress (ge : GlobalEnv) (locals : Env) (memory : Mem)
    (types : List Ty) (values : List Val) : Exprlist → Prop where
  | ready {args} :
      CastArguments memory args types values → ListProgress ge locals memory types values args
  | lred (context arg result final) :
      Lred ge.expressionEnv locals arg memory result final →
      ContextList .LV context → ListProgress ge locals memory types values (context arg)
  | rred (context arg trace result final) :
      Rred ge arg memory trace result final →
      ContextList .RV context → ListProgress ge locals memory types values (context arg)
  | callred (context arg function args type) :
      Callred ge arg memory function args type →
      ContextList .RV context → ListProgress ge locals memory types values (context arg)

/-- A read-only expression is immediately safe in every memory preserving its base. -/
theorem ReadEval.imm_safe {ge : GlobalEnv} {locals : Env} {base memory : Mem}
    {kind : Kind} {expr : Expr} {result : PureResult}
    (heval : ReadEval ge locals base kind expr result) (hframe : CallMemory base memory) :
    ImmSafe ge locals kind expr memory := by
  induction heval using ReadEval.rec
      (motive_2 := fun args types values _ => ListProgress ge locals memory types values args)
      with
  | value => exact .value _ _ _
  | location => exact .location _ _ _ _ _
  | var_local name type block hlocal =>
      exact .lred _ id _ _ _ _ (.var_local _ _ _ _ hlocal) (.top _)
  | var_global name type block hlocal hglobal =>
      exact .lred _ id _ _ _ _ (.var_global _ _ _ _ hlocal hglobal) (.top _)
  | deref arg type block offset harg ih =>
      apply ih.value_context (.deref _ id type (.top _))
      rintro value valueType rfl
      cases harg
      exact .lred _ id _ _ _ _ (.deref _ _ _ _ _) (.top _)
  | rvalof arg type block offset bitfield value harg ht _ hd ih =>
      apply ih.location_context (.rvalof _ id type (.top _))
      rintro block offset bitfield argType rfl
      cases harg
      change type = argType at ht
      subst argType
      exact .rred _ id _ _ _ _ _ (.rvalof _ _ _ _ _ _ _ (hd _ hframe)) (.top _)
  | addrof arg type block offset harg ih =>
      apply ih.location_context (.addrof _ id type (.top _))
      rintro block offset bitfield argType rfl
      cases harg
      exact .rred _ id _ _ _ _ _ (.addrof _ _ _ _ _) (.top _)
  | unop op arg type value result harg hop ih =>
      apply ih.value_context (.unop _ id op type (.top _))
      rintro argValue argType rfl
      cases harg
      exact .rred _ id _ _ _ _ _ (.unop _ _ _ _ _ _ (hop _ hframe)) (.top _)
  | binop op left right type leftValue rightValue result hleft hright hop ihleft ihright =>
      apply ihleft.value_context (.binop_left _ id op right type (.top _))
      rintro leftValue leftType rfl
      cases hleft
      apply ihright.value_context (.binop_right _ id op (.Eval _ _) type (.top _))
      rintro rightValue rightType rfl
      cases hright
      exact .rred _ id _ _ _ _ _ (.binop _ _ _ _ _ _ _ _ (hop _ hframe)) (.top _)
  | cast arg type value result harg hcast ih =>
      apply ih.value_context (.cast _ id type (.top _))
      rintro argValue argType rfl
      cases harg
      exact .rred _ id _ _ _ _ _ (.cast _ _ _ _ _ (hcast _ hframe)) (.top _)
  | call callee args type pointer parameters returnType cc function values result
      hcallee hargs hfind ht hc hcall ihcallee ihargs =>
      apply ihcallee.value_context (.call_left _ id args type (.top _))
      rintro pointer pointerType rfl
      cases hcallee
      cases ihargs with
      | ready hargs =>
          exact .callred _ id _ _ _ _ _
            (.call _ _ _ _ _ _ _ _ _ _ hfind hargs ht hc) (.top _)
      | lred context arg reduced final hstep hcontext =>
          exact .lred _ (fun arg => .Ecall (.Eval _ _) (context arg) type) arg _ _ _
            hstep (.call_right _ _ _ _ hcontext)
      | rred context arg trace reduced final hstep hcontext =>
          exact .rred _ (fun arg => .Ecall (.Eval _ _) (context arg) type) arg _ _ _ _
            hstep (.call_right _ _ _ _ hcontext)
      | callred context arg callee values type hstep hcontext =>
          exact .callred _ (fun arg => .Ecall (.Eval _ _) (context arg) _) arg _ _ _ _
            hstep (.call_right _ _ _ _ hcontext)
  | nil => exact .ready .nil
  | cons arg rest type types value values cast hfirst hcast hrest ihfirst ihrest =>
      cases ihfirst with
      | value value argType memory =>
          cases hfirst
          cases ihrest with
          | ready hrest =>
              exact .ready (.cons _ _ _ _ _ _ _ (hcast _ hframe) hrest)
          | lred context arg reduced final hstep hcontext =>
              exact .lred (fun arg => .Econs (.Eval _ _) (context arg)) arg _ _
                hstep (.tail _ _ _ hcontext)
          | rred context arg trace reduced final hstep hcontext =>
              exact .rred (fun arg => .Econs (.Eval _ _) (context arg)) arg _ _ _
                hstep (.tail _ _ _ hcontext)
          | callred context arg callee args type hstep hcontext =>
              exact .callred (fun arg => .Econs (.Eval _ _) (context arg)) arg _ _ _
                hstep (.tail _ _ _ hcontext)
      | lred _ context arg memory reduced final hstep hcontext =>
          exact .lred (fun arg => .Econs (context arg) rest) arg _ _
            hstep (.head _ _ _ hcontext)
      | rred _ context arg memory trace reduced final hstep hcontext =>
          exact .rred (fun arg => .Econs (context arg) rest) arg _ _ _
            hstep (.head _ _ _ hcontext)
      | callred _ context arg memory callee args type hstep hcontext =>
          exact .callred (fun arg => .Econs (context arg) rest) arg _ _ _
            hstep (.head _ _ _ hcontext)

/-- Every position exposed by C's evaluation rules remains immediately safe. -/
theorem ReadEval.not_stuck {ge : GlobalEnv} {locals : Env} {base memory : Mem}
    {expr : Expr} {result : PureResult}
    (heval : ReadEval ge locals base .RV expr result) (hframe : CallMemory base memory) :
    NotStuck ge locals expr memory := by
  intro kind context arg hcontext heq
  rw [heq] at heval
  obtain ⟨operand, harg, _⟩ := heval.in_context hcontext
  exact harg.imm_safe hframe

end Quadrature.CSource.C
