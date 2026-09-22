import Quadrature.CSource.Callback.Entry

/-!
# Evaluating the original callback expression

The source expression `0.5 * (1 - x) * cos(x)` keeps the integer literal `1`,
its promotion to `double`, both separately rounded products and the nested
`cos` call. Only `cos` has an execution contract (`SourceCallbackContract`).
`testfun_expression` evaluates the surrounding expression by the strategy
rules to `Binary64.testfun cosine x`.
-/

namespace Quadrature.CSource.C

open CC Binary64.ClightSource FloatLib.Floats.Formats.BinaryInterchange

/-- The left operand `0.5 * (1 - x)` of the callback's product. -/
def testfunFactor : Expr :=
  .Ebinop .Omul (.Eval (.Vfloat Binary64.half) tdouble)
    (.Ebinop .Osub (.Eval (.Vint (Integers.Int.repr 1)) tint)
      (readVar _x tdouble) tdouble) tdouble

/-- The call `cos(x)` through the global `cos` symbol. -/
def testfunCosineCall : Expr :=
  .Ecall (readVar _cos callbackType) (.Econs (readVar _x tdouble) .Enil) tdouble

/-- The callback's return expression `testfunFactor * cos(x)`. -/
def testfunExpression : Expr :=
  .Ebinop .Omul testfunFactor testfunCosineCall tdouble

/-- The elaborated body of `Typed.testfun` is `return testfunExpression;`, by `rfl`. -/
theorem testfun_body_syntax :
    Typed.testfun.fn_body = .Sreturn (some testfunExpression) := rfl

/-- `1 - x` with integer `1` and `double` `x` is `Model.sub one x`: the literal converts to
binary64 one exactly. -/
theorem testfun_subtraction (ce : CompositeEnv) (memory : Mem) (x : Floats.Float) :
    Cop.semBinaryOperation ce .Osub (.Vint (Integers.Int.repr 1)) tint
      (.Vfloat x) tdouble memory = some (.Vfloat (Model.sub Binary64.one x)) := by
  have hone : Floats.Float.ofInt (Integers.Int.repr 1) = Binary64.one := by decide +kernel
  change some (Val.Vfloat (Model.sub (Floats.Float.ofInt (Integers.Int.repr 1)) x)) = _
  rw [hone]

/-- With `x` loaded from `block`, `testfunFactor` evaluates in the pure phase to
`Model.mul half (Model.sub one x)`. -/
theorem testfun_factor_value (ge : ExpressionEnv) (memory : Mem)
    (block : Block) (x : Floats.Float)
    (hload : Mem.load .Mfloat64 memory block 0 = some (.Vfloat x)) :
    EvalRvalue ge (testfunLocals block) memory testfunFactor
      (.Vfloat (Model.mul Binary64.half (Model.sub Binary64.one x))) := by
  apply EvalRvalue.binop (v₁ := .Vfloat Binary64.half)
    (v₂ := .Vfloat (Model.sub Binary64.one x))
  · exact .value _ _
  · apply EvalRvalue.binop (v₁ := .Vint (Integers.Int.repr 1)) (v₂ := .Vfloat x)
    · exact .value _ _
    · exact read_local ge (testfunLocals block) memory _x tdouble block .Mfloat64
        (.Vfloat x) rfl rfl rfl hload
    · exact testfun_subtraction ge.composites memory x
  · rfl

variable [ExternalCalls]

/-- `testfunFactor` has no effects: the effect phase leaves it unchanged. -/
theorem testfun_factor_effects (ge : GlobalEnv) (locals : Env) (memory : Mem) :
    EvalExpr ge locals memory .RV testfunFactor E0 memory testfunFactor := by
  apply EvalExpr.binop (t₁ := E0) (t₂ := E0) (m₁ := memory)
  · exact .value _ _ _ _
  · apply EvalExpr.binop (t₁ := E0) (t₂ := E0) (m₁ := memory)
    · exact .value _ _ _ _
    · exact read_var_effects ge locals memory _x tdouble rfl

/-- With `x` loaded from `block` and a `SourceCallbackContract` for the function at the `cos`
symbol computing `cosine`, the effect phase evaluates `cos(x)` to `Eval (Vfloat (cosine x))` and
satisfies `CallMemory`. -/
theorem testfun_cosine_call (ge : GlobalEnv) (memory : Mem) (block cosBlock : Block)
    (function : FunDef) (cosine : Floats.Float → Floats.Float) (x : Floats.Float)
    (hsymbol : Genv.findSymbol ge.globals _cos = some cosBlock)
    (contract : SourceCallbackContract ge (.Vptr cosBlock Integers.Ptrofs.zero) function cosine)
    (hload : Mem.load .Mfloat64 memory block 0 = some (.Vfloat x)) :
    ∃ final,
      EvalExpr ge (testfunLocals block) memory .RV testfunCosineCall E0 final
        (.Eval (.Vfloat (cosine x)) tdouble) ∧ CallMemory memory final := by
  obtain ⟨final, hcall, hmemory⟩ := contract.execution memory x
  refine ⟨final, ?_, hmemory⟩
  apply EvalExpr.call (t₁ := E0) (t₂ := E0) (t₃ := E0)
    (m₁ := memory) (m₂ := memory) (vf := .Vptr cosBlock Integers.Ptrofs.zero)
    (types := [tdouble]) (result := tdouble) (cc := cc_default) (fd := function)
  · exact read_var_effects ge (testfunLocals block) memory _cos callbackType rfl
  · exact .cons _ _ _ _ E0 _ _ E0 _ _
      (read_var_effects ge (testfunLocals block) memory _x tdouble rfl) (.nil _ _)
  · exact read_global_function ge (testfunLocals block) memory _cos cosBlock
      [tdouble] tdouble cc_default rfl hsymbol
  · exact .cons _ _ _ _ _ _ _
      (read_local ge.expressionEnv (testfunLocals block) memory _x tdouble block .Mfloat64
        (.Vfloat x) rfl rfl rfl hload) rfl .nil
  · rfl
  · exact contract.function_eq
  · exact contract.type_eq
  · exact hcall

/-- Under the hypotheses of `testfun_cosine_call`, `testfunExpression` evaluates to
`Vfloat (Binary64.testfun cosine x)`, for every binary64 `x`, and satisfies `CallMemory`. -/
theorem testfun_expression (ge : GlobalEnv) (memory : Mem) (block cosBlock : Block)
    (function : FunDef) (cosine : Floats.Float → Floats.Float) (x : Floats.Float)
    (hsymbol : Genv.findSymbol ge.globals _cos = some cosBlock)
    (contract : SourceCallbackContract ge (.Vptr cosBlock Integers.Ptrofs.zero) function cosine)
    (hload : Mem.load .Mfloat64 memory block 0 = some (.Vfloat x)) :
    ∃ final,
      EvalExpression ge (testfunLocals block) memory testfunExpression E0 final
        (.Vfloat (Binary64.testfun cosine x)) ∧ CallMemory memory final := by
  obtain ⟨final, hcall, hmemory⟩ :=
    testfun_cosine_call ge memory block cosBlock function cosine x hsymbol contract hload
  refine ⟨final, ?_, hmemory⟩
  apply EvalExpression.intro (a' :=
    .Ebinop .Omul testfunFactor (.Eval (.Vfloat (cosine x)) tdouble) tdouble)
  · apply EvalExpr.binop (t₁ := E0) (t₂ := E0) (m₁ := memory)
    · exact testfun_factor_effects ge (testfunLocals block) memory
    · exact hcall
  · exact EvalRvalue.binop _ _ _ _ _ _ _
      (testfun_factor_value ge.expressionEnv final block x (hmemory.load hload))
      (.value _ _) rfl

end Quadrature.CSource.C
