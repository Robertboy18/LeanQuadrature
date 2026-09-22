import Quadrature.CSource.Semantics.Reduction
import CCLib.Determinism

/-!
# Pure expressions under every C evaluation order

The strategy's simple-expression judgments describe arithmetic and memory
reads without side effects. `PureEval` packages their two kinds.
`PureEval.in_context` exposes the meaning of any operand that the full C
semantics may choose next, and permits replacing it by another expression
with the same type and meaning.
-/

namespace Quadrature.CSource.C

open CC

/-- The meaning of a value expression or a location expression. -/
inductive PureResult where
  | value (value : Val)
  | location (block : Block) (offset : Integers.Ptrofs) (bitfield : Bitfield)

/-- A kind-indexed wrapper for the existing simple-expression evaluation judgments. -/
inductive PureEval (ge : ExpressionEnv) (locals : Env) (memory : Mem) :
    Kind → Expr → PureResult → Prop where
  | value {expr value} :
      EvalRvalue ge locals memory expr value →
      PureEval ge locals memory .RV expr (.value value)
  | location {expr block offset bitfield} :
      EvalLvalue ge locals memory expr block offset bitfield →
      PureEval ge locals memory .LV expr (.location block offset bitfield)

/-- Evaluating an embedded value returns that value. -/
theorem evalRvalue_value_iff {ge : ExpressionEnv} {locals : Env} {memory : Mem}
    {value result : Val} {type : Ty} :
    EvalRvalue ge locals memory (.Eval value type) result ↔ result = value := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .value _ _

/-- Evaluating an embedded location returns its block, offset, and bitfield. -/
theorem evalLvalue_location_iff {ge : ExpressionEnv} {locals : Env} {memory : Mem}
    {block resultBlock : Block} {offset resultOffset : Integers.Ptrofs}
    {bitfield resultBitfield : Bitfield} {type : Ty} :
    EvalLvalue ge locals memory (.Eloc block offset bitfield type)
      resultBlock resultOffset resultBitfield ↔
      resultBlock = block ∧ resultOffset = offset ∧ resultBitfield = bitfield := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact .loc _ _ _ _

/-- Replacing a context's operand by one of the same type preserves the outer type. -/
theorem Context.typeof_eq {input output : Kind} {context : Expr → Expr}
    (hcontext : Context input output context) {left right : Expr}
    (htype : typeof left = typeof right) :
    typeof (context left) = typeof (context right) := by
  cases hcontext <;> first | exact htype | rfl

/-- Every exposed operand of a pure expression has a meaning. Replacing that operand by an
expression of the same type and meaning preserves the entire expression's meaning. -/
theorem PureEval.in_context {ge : ExpressionEnv} {locals : Env} {memory : Mem}
    {input output : Kind} {context : Expr → Expr}
    (hcontext : Context input output context) {expr : Expr} {result : PureResult}
    (heval : PureEval ge locals memory output (context expr) result) :
    ∃ operand,
      PureEval ge locals memory input expr operand ∧
      ∀ replacement, typeof replacement = typeof expr →
        PureEval ge locals memory input replacement operand →
        PureEval ge locals memory output (context replacement) result := by
  induction hcontext using Context.rec (motive_2 := fun _ _ => True)
      generalizing expr result with
  | top => exact ⟨result, heval, fun _ _ h => h⟩
  | deref context type hcontext ih =>
      cases heval with
      | location h =>
          cases h with
          | deref _ _ block offset harg =>
              obtain ⟨operand, hoperand, hreplace⟩ := ih (.value harg)
              refine ⟨operand, hoperand, ?_⟩
              intro replacement htype hvalue
              cases hreplace replacement htype hvalue with
              | value hvalue => exact .location (.deref _ _ _ _ hvalue)
  | field context name type hcontext ih =>
      cases heval with
      | location h =>
          cases h with
          | field_struct _ _ _ block offset id composite attr delta bitfield harg ht hc hf =>
              obtain ⟨operand, hoperand, hreplace⟩ := ih (.value harg)
              refine ⟨operand, hoperand, ?_⟩
              intro replacement htype hvalue
              cases hreplace replacement htype hvalue with
              | value hvalue =>
                  exact .location (.field_struct _ _ _ _ _ _ _ _ _ _
                    hvalue ((hcontext.typeof_eq htype).trans ht) hc hf)
          | field_union _ _ _ block offset id composite attr delta bitfield harg ht hf hc =>
              obtain ⟨operand, hoperand, hreplace⟩ := ih (.value harg)
              refine ⟨operand, hoperand, ?_⟩
              intro replacement htype hvalue
              cases hreplace replacement htype hvalue with
              | value hvalue =>
                  exact .location (.field_union _ _ _ _ _ _ _ _ _ _
                    hvalue ((hcontext.typeof_eq htype).trans ht) hf hc)
  | rvalof context type hcontext ih =>
      cases heval with
      | value h =>
          cases h with
          | rvalof block offset bitfield _ _ value harg ht hv hd =>
              obtain ⟨operand, hoperand, hreplace⟩ := ih (.location harg)
              refine ⟨operand, hoperand, ?_⟩
              intro replacement htype hvalue
              cases hreplace replacement htype hvalue with
              | location hvalue =>
                  exact .value (.rvalof _ _ _ _ _ _ hvalue
                    (ht.trans (hcontext.typeof_eq htype).symm) hv hd)
  | addrof context type hcontext ih =>
      cases heval with
      | value h =>
          cases h with
          | addrof block offset _ _ harg =>
              obtain ⟨operand, hoperand, hreplace⟩ := ih (.location harg)
              refine ⟨operand, hoperand, ?_⟩
              intro replacement htype hvalue
              cases hreplace replacement htype hvalue with
              | location hvalue => exact .value (.addrof _ _ _ _ hvalue)
  | unop context op type hcontext ih =>
      cases heval with
      | value h =>
          cases h with
          | unop _ _ _ arg value harg hop =>
              obtain ⟨operand, hoperand, hreplace⟩ := ih (.value harg)
              refine ⟨operand, hoperand, ?_⟩
              intro replacement htype hvalue
              cases hreplace replacement htype hvalue with
              | value hvalue =>
                  apply PureEval.value (.unop _ _ _ _ _ hvalue ?_)
                  simpa only [hcontext.typeof_eq htype] using hop
  | binop_left context op right type hcontext ih =>
      cases heval with
      | value h =>
          cases h with
          | binop _ _ _ _ leftValue rightValue value hleft hright hop =>
              obtain ⟨operand, hoperand, hreplace⟩ := ih (.value hleft)
              refine ⟨operand, hoperand, ?_⟩
              intro replacement htype hvalue
              cases hreplace replacement htype hvalue with
              | value hvalue =>
                  apply PureEval.value (.binop _ _ _ _ _ _ _
                    hvalue hright ?_)
                  simpa only [hcontext.typeof_eq htype] using hop
  | binop_right context op left type hcontext ih =>
      cases heval with
      | value h =>
          cases h with
          | binop _ _ _ _ leftValue rightValue value hleft hright hop =>
              obtain ⟨operand, hoperand, hreplace⟩ := ih (.value hright)
              refine ⟨operand, hoperand, ?_⟩
              intro replacement htype hvalue
              cases hreplace replacement htype hvalue with
              | value hvalue =>
                  apply PureEval.value (.binop _ _ _ _ _ _ _
                    hleft hvalue ?_)
                  simpa only [hcontext.typeof_eq htype] using hop
  | cast context type hcontext ih =>
      cases heval with
      | value h =>
          cases h with
          | cast _ _ arg value harg hop =>
              obtain ⟨operand, hoperand, hreplace⟩ := ih (.value harg)
              refine ⟨operand, hoperand, ?_⟩
              intro replacement htype hvalue
              cases hreplace replacement htype hvalue with
              | value hvalue =>
                  apply PureEval.value (.cast _ _ _ _ hvalue ?_)
                  simpa only [hcontext.typeof_eq htype] using hop
  | seqand | seqor | condition | assign_left | assign_right
  | assignop_left | assignop_right | postincr | call_left | call_right
  | builtin | comma | paren =>
      cases heval with
      | value h => cases h
  | head | tail => trivial

/-- A head reduction of a location retains its type. -/
theorem Lred.typeof_eq {ge : ExpressionEnv} {locals : Env} {memory final : Mem}
    {expr result : Expr} (h : Lred ge locals expr memory result final) :
    typeof result = typeof expr := by
  cases h <;> rfl

/-- Location computation does not change memory. -/
theorem Lred.memory_eq {ge : ExpressionEnv} {locals : Env} {memory final : Mem}
    {expr result : Expr} (h : Lred ge locals expr memory result final) :
    final = memory := by
  cases h <;> rfl

/-- A location head reduction preserves the meaning given by simple evaluation. -/
theorem Lred.pure_eval {ge : ExpressionEnv} {locals : Env} {memory final : Mem}
    {expr result : Expr} {value : PureResult}
    (hstep : Lred ge locals expr memory result final)
    (heval : PureEval ge locals memory .LV expr value) :
    PureEval ge locals final .LV result value := by
  cases hstep <;> cases heval with
  | location h =>
      cases h <;> simp_all [evalRvalue_value_iff, typeof]
      all_goals exact .location (.loc _ _ _ _)

variable [ExternalCalls]

/-- A value head reduction retains its type, including the intermediate assignment and
parenthesis forms. -/
theorem Rred.typeof_eq {ge : GlobalEnv} {memory final : Mem} {trace : Trace}
    {expr result : Expr} (h : Rred ge expr memory trace result final) :
    typeof result = typeof expr := by
  cases h <;> first | assumption | rfl

omit [ExternalCalls] in
/-- A nonvolatile read has a unique result and an empty trace. -/
private theorem pure_read_reduction {ge : GlobalEnv} {locals : Env} {memory : Mem}
    {block : Block} {offset : Integers.Ptrofs} {bitfield : Bitfield} {type : Ty}
    {trace : Trace} {value result : Val}
    (hv : typeIsVolatile type = false)
    (hstep : DerefLoc ge.expressionEnv type memory block offset bitfield trace result)
    (heval : DerefLoc ge.expressionEnv type memory block offset bitfield E0 value) :
    trace = E0 ∧ memory = memory ∧
      PureEval ge.expressionEnv locals memory .RV (.Eval result type) (.value value) := by
  obtain ⟨htrace, hread⟩ := (derefLoc_iff hv).mp hstep
  subst trace
  have heq := CC.derefLoc_determ hread ((derefLoc_iff hv).mp heval).2
  cases heq
  exact ⟨rfl, rfl, .value (.value _ _)⟩

/-- A head reduction of a pure expression is silent, leaves memory unchanged, and preserves
the value. -/
theorem Rred.pure_eval {ge : GlobalEnv} {locals : Env} {memory final : Mem}
    {expr result : Expr} {trace : Trace} {value : PureResult}
    (hstep : Rred ge expr memory trace result final)
    (heval : PureEval ge.expressionEnv locals memory .RV expr value) :
    trace = E0 ∧ final = memory ∧ PureEval ge.expressionEnv locals memory .RV result value := by
  cases hstep with
  | rvalof block offset bitfield type memory trace result hread =>
      cases heval with
      | value h =>
          cases h with
          | rvalof _ _ _ _ _ _ hloc _ hv hd =>
              cases hloc
              exact pure_read_reduction hv hread hd
  | addrof =>
      cases heval with
      | value h =>
          cases h with
          | addrof _ _ _ _ hloc =>
              cases hloc
              exact ⟨rfl, rfl, .value (.value _ _)⟩
  | unop op arg argType type memory result hstep =>
      cases heval with
      | value h =>
          cases h with
          | unop _ _ _ _ _ harg hsem =>
              cases harg
              have heq := Option.some.inj (hstep.symm.trans hsem)
              cases heq
              exact ⟨rfl, rfl, .value (.value _ _)⟩
  | binop op left leftType right rightType type memory result hstep =>
      cases heval with
      | value h =>
          cases h with
          | binop _ _ _ _ _ _ _ hleft hright hsem =>
              cases hleft
              cases hright
              have heq := Option.some.inj (hstep.symm.trans hsem)
              cases heq
              exact ⟨rfl, rfl, .value (.value _ _)⟩
  | cast type arg argType memory result hstep =>
      cases heval with
      | value h =>
          cases h with
          | cast _ _ _ _ harg hsem =>
              cases harg
              have heq := Option.some.inj (hstep.symm.trans hsem)
              cases heq
              exact ⟨rfl, rfl, .value (.value _ _)⟩
  | sizeof | alignof =>
      cases heval with
      | value h =>
          cases h
          exact ⟨rfl, rfl, .value (.value _ _)⟩
  | seqand_true | seqand_false | seqor_true | seqor_false | condition
  | assign | assignop | postincr | comma | paren | builtin =>
      cases heval with
      | value h => cases h

end Quadrature.CSource.C
