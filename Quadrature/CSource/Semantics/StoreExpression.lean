import Quadrature.CSource.Semantics.ReadOnlyTotal

/-!
# Scalar assignments with read-only operands

`StoreExpr` describes an assignment whose operands, including any calls,
preserve memory until the final scalar store. Compound assignment first
reads the destination and expands to an ordinary assignment, following
the C reduction rules.
-/

namespace Quadrature.CSource.C

open CC

/-- A nonvolatile scalar assignment has exactly its memory store's result and empty trace. -/
theorem assignLoc_value_iff {ge : ExpressionEnv} {memory final : Mem}
    {block : Block} {offset : Integers.Ptrofs} {type : Ty} {chunk : Chunk}
    {value result : Val} {trace : Trace}
    (hmode : accessMode type = .By_value chunk) (hv : typeIsVolatile type = false) :
    AssignLoc ge type memory block offset .Full value trace final result ↔
      trace = E0 ∧ result = value ∧
        Mem.storev chunk memory (.Vptr block offset) value = some final := by
  constructor
  · intro h
    cases h with
    | value value actualChunk final hactual _ hstore =>
        have heq := AccessMode.By_value.inj (hmode.symm.trans hactual)
        cases heq
        exact ⟨rfl, rfl, hstore⟩
    | volatile value actualChunk trace final _ hvolatile _ =>
        simp [hv] at hvolatile
    | copy source sourceOffset bytes final hcopy _ _ _ _ _ =>
        simp [hmode] at hcopy
  · rintro ⟨rfl, rfl, hstore⟩
    exact .value _ _ _ hmode hv hstore

variable [ExternalCalls]

/-- The operands of a pending scalar store have fixed values until that store executes. -/
inductive StoreExpr (ge : GlobalEnv) (locals : Env) (base : Mem)
    (block : Block) (offset : Integers.Ptrofs) (type : Ty) (value : Val) : Expr → Prop where
  | assign (left right rhs) :
      ReadEval ge locals base .LV left (.location block offset .Full) →
      ReadEval ge locals base .RV right (.value rhs) →
      type = typeof left →
      (∀ memory, CallMemory base memory →
        Cop.semCast rhs (typeof right) type memory = some value) →
      StoreExpr ge locals base block offset type value (.Eassign left right type)
  | compound (op left right operationType old rhs combined) :
      ReadEval ge locals base .LV left (.location block offset .Full) →
      ReadEval ge locals base .RV right (.value rhs) →
      type = typeof left →
      (∀ memory, CallMemory base memory →
        DerefLoc ge.expressionEnv type memory block offset .Full E0 old) →
      (∀ memory, CallMemory base memory →
        Cop.semBinaryOperation ge.composites op old type rhs (typeof right) memory =
          some combined) →
      (∀ memory, CallMemory base memory →
        Cop.semCast combined operationType type memory = some value) →
      StoreExpr ge locals base block offset type value
        (.Eassignop op left right operationType type)

/-- Every pending store expression has the destination's type. -/
theorem StoreExpr.typeof_eq {ge : GlobalEnv} {locals : Env} {base : Mem}
    {block : Block} {offset : Integers.Ptrofs} {type : Ty} {value : Val} {expr : Expr}
    (heval : StoreExpr ge locals base block offset type value expr) :
    typeof expr = type := by
  cases heval <;> rfl

/-- An exposed position is either the assignment itself or a read-only operand. Replacing
such an operand preserves the pending store. -/
theorem StoreExpr.in_context {ge : GlobalEnv} {locals : Env} {base : Mem}
    {block : Block} {offset : Integers.Ptrofs} {type : Ty} {value : Val}
    {input : Kind} {context : Expr → Expr} {expr : Expr}
    (hcontext : Context input .RV context)
    (heval : StoreExpr ge locals base block offset type value (context expr)) :
    (input = .RV ∧ context = id) ∨
      ∃ operand, ReadEval ge locals base input expr operand ∧
        ∀ replacement, typeof replacement = typeof expr →
          ReadEval ge locals base input replacement operand →
          StoreExpr ge locals base block offset type value (context replacement) := by
  cases hcontext with
  | top => exact .inl ⟨rfl, rfl⟩
  | assign_left context right type hcontext =>
      cases heval with
      | assign _ _ rhs hleft hright ht hc =>
          obtain ⟨operand, harg, hreplace⟩ := hleft.in_context hcontext
          exact .inr ⟨operand, harg, fun replacement htype h =>
            .assign _ _ _ (hreplace replacement htype h) hright
              (ht.trans (hcontext.typeof_eq htype).symm) hc⟩
  | assign_right context left type hcontext =>
      cases heval with
      | assign _ _ rhs hleft hright ht hc =>
          obtain ⟨operand, harg, hreplace⟩ := hright.in_context hcontext
          refine .inr ⟨operand, harg, fun replacement htype h =>
            .assign _ _ _ hleft (hreplace replacement htype h) ht ?_⟩
          simpa only [hcontext.typeof_eq htype] using hc
  | assignop_left context op right operationType type hcontext =>
      cases heval with
      | compound _ _ _ _ old rhs combined hleft hright ht hd hop hc =>
          obtain ⟨operand, harg, hreplace⟩ := hleft.in_context hcontext
          exact .inr ⟨operand, harg, fun replacement htype h =>
            .compound _ _ _ _ _ _ _ (hreplace replacement htype h) hright
              (ht.trans (hcontext.typeof_eq htype).symm) hd hop hc⟩
  | assignop_right context op left operationType type hcontext =>
      cases heval with
      | compound _ _ _ _ old rhs combined hleft hright ht hd hop hc =>
          obtain ⟨operand, harg, hreplace⟩ := hright.in_context hcontext
          refine .inr ⟨operand, harg, fun replacement htype h =>
            .compound _ _ _ _ _ _ _ hleft (hreplace replacement htype h) ht hd ?_ hc⟩
          simpa only [hcontext.typeof_eq htype] using hop
  | rvalof | addrof | unop | binop_left | binop_right | cast | seqand | seqor
  | condition | postincr | call_left | call_right | builtin | comma | paren => cases heval

/-- A scalar assignment or compound assignment can reduce whenever its destination remains
writable and its operands have their certified values. -/
theorem StoreExpr.imm_safe {ge : GlobalEnv} {locals : Env} {base memory : Mem}
    {block : Block} {offset : Integers.Ptrofs} {type : Ty} {value : Val}
    {chunk : Chunk} {expr : Expr}
    (heval : StoreExpr ge locals base block offset type value expr)
    (hframe : CallMemory base memory)
    (hmode : accessMode type = .By_value chunk) (hv : typeIsVolatile type = false)
    (hstore : ∃ final, Mem.storev chunk memory (.Vptr block offset) value = some final) :
    ImmSafe ge locals .RV expr memory := by
  cases heval with
  | assign left right rhs hleft hright ht hc =>
      apply (hleft.imm_safe hframe).location_context (.assign_left _ id right type (.top _))
      rintro block offset bitfield leftType rfl
      cases hleft
      change type = leftType at ht
      subst leftType
      apply (hright.imm_safe hframe).value_context
        (.assign_right _ id (.Eloc _ _ _ _) type (.top _))
      rintro rhs rhsType rfl
      cases hright
      obtain ⟨final, hs⟩ := hstore
      exact .rred _ id _ _ _ _ _
        (.assign _ _ _ _ _ _ _ _ _ _ _ (hc _ hframe) (.value _ _ _ hmode hv hs)) (.top _)
  | compound op left right operationType old rhs combined hleft hright ht hd hop hc =>
      apply (hleft.imm_safe hframe).location_context
        (.assignop_left _ id op right operationType type (.top _))
      rintro block offset bitfield leftType rfl
      cases hleft
      change type = leftType at ht
      subst leftType
      apply (hright.imm_safe hframe).value_context
        (.assignop_right _ id op (.Eloc _ _ _ _) operationType type (.top _))
      rintro rhs rhsType rfl
      cases hright
      exact .rred _ id _ _ _ _ _ (.assignop _ _ _ _ _ _ _ _ _ _ _ (hd _ hframe)) (.top _)

/-- Every exposed operand of a pending scalar store is safe. -/
theorem StoreExpr.not_stuck {ge : GlobalEnv} {locals : Env} {base memory : Mem}
    {block : Block} {offset : Integers.Ptrofs} {type : Ty} {value : Val}
    {chunk : Chunk} {expr : Expr}
    (heval : StoreExpr ge locals base block offset type value expr)
    (hframe : CallMemory base memory)
    (hmode : accessMode type = .By_value chunk) (hv : typeIsVolatile type = false)
    (hstore : ∃ final, Mem.storev chunk memory (.Vptr block offset) value = some final) :
    NotStuck ge locals expr memory := by
  intro kind context arg hcontext heq
  rw [heq] at heval
  rcases heval.in_context hcontext with ⟨rfl, rfl⟩ | ⟨operand, harg, _⟩
  · exact heval.imm_safe hframe hmode hv hstore
  · exact harg.imm_safe hframe

/-- A head step either performs the scalar store or expands compound assignment to a smaller
pending store. No other memory effect or trace is possible. -/
theorem StoreExpr.head_step {ge : GlobalEnv} {locals : Env} {base memory final : Mem}
    {block : Block} {offset : Integers.Ptrofs} {type : Ty} {value : Val}
    {chunk : Chunk} {expr result : Expr} {trace : Trace}
    (heval : StoreExpr ge locals base block offset type value expr)
    (hframe : CallMemory base memory)
    (hmode : accessMode type = .By_value chunk) (hv : typeIsVolatile type = false)
    (hstep : Rred ge expr memory trace result final) :
    trace = E0 ∧
      ((result = .Eval value type ∧
          Mem.storev chunk memory (.Vptr block offset) value = some final) ∨
        (final = memory ∧ StoreExpr ge locals base block offset type value result ∧
          result.work < expr.work)) := by
  cases heval with
  | assign left right rhs hleft hright ht hc =>
      cases hstep with
      | assign block offset type bitfield rhs rhsType memory cast trace final result hcast hs =>
          cases hleft
          cases hright
          have heq := Option.some.inj (hcast.symm.trans (hc _ hframe))
          cases heq
          obtain ⟨rfl, rfl, hstore⟩ := (assignLoc_value_iff hmode hv).mp hs
          exact ⟨rfl, .inl ⟨rfl, hstore⟩⟩
  | compound op left right operationType old rhs combined hleft hright ht hd hop hc =>
      cases hstep with
      | assignop op block offset type bitfield rhs rhsType operationType memory trace read hs =>
          cases hleft
          cases hright
          obtain ⟨htrace, hread⟩ := (derefLoc_iff hv).mp hs
          subst trace
          have heq := CC.derefLoc_determ hread ((derefLoc_iff hv).mp (hd _ hframe)).2
          cases heq
          refine ⟨rfl, .inr ⟨rfl, ?_, by simp [Expr.work]⟩⟩
          exact .assign _ _ combined (.location _ _ _ _)
            (.binop _ _ _ _ _ _ _ (.value _ _) (.value _ _) hop) rfl hc

end Quadrature.CSource.C
