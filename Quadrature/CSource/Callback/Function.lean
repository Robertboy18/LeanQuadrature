import Quadrature.CSource.Callback.Expression

/-!
# Execution of the original C callback

`testfun_call` proves entry, the callback expression, the return cast and local
freeing for every binary64 argument, assuming only a `SourceCallbackContract`
for the function resolved as `cos`. `testfun_callback_contract` then derives
the callback contract the integrator needs, and
`SourceCallbackContract.of_external` builds the `cos` contract from an
external-call contract, the shape a platform cosine would have to satisfy.
-/

namespace Quadrature.CSource.C

open CC Binary64.ClightSource

variable [ExternalCalls]

/-- When `pointer` resolves to an external function of type `double (double)` whose
`externalCall` on `Vfloat x` returns `Vfloat (f x)` silently and satisfies `CallMemory`, the
pointer satisfies `SourceCallbackContract` for `f`. -/
theorem SourceCallbackContract.of_external (ge : GlobalEnv) (pointer : Val)
    (externalFunction : ExtFun) (f : Floats.Float → Floats.Float)
    (hfunction : Genv.findFunct ge.globals pointer =
      some (.External externalFunction [tdouble] tdouble cc_default))
    (hexternal : ∀ memory x, ∃ final,
      externalCall externalFunction (Genv.toSenv ge.globals) [.Vfloat x]
        memory E0 (.Vfloat (f x)) final ∧ CallMemory memory final) :
    SourceCallbackContract ge pointer
      (.External externalFunction [tdouble] tdouble cc_default) f := by
  refine ⟨hfunction, rfl, ?_⟩
  intro memory x
  obtain ⟨final, hcall, hmemory⟩ := hexternal memory x
  exact ⟨final, .external _ _ _ _ _ _ _ _ _ hcall, hmemory⟩

/-- Given a `SourceCallbackContract` for the function at the `cos` symbol computing `cosine`,
calling `Typed.testfun` on `Vfloat x` returns `Vfloat (Binary64.testfun cosine x)` silently in a
memory satisfying `CallMemory`, for every binary64 `x`. -/
theorem testfun_call (ge : GlobalEnv) (memory : Mem) (cosBlock : Block)
    (function : FunDef) (cosine : Floats.Float → Floats.Float) (x : Floats.Float)
    (hsymbol : Genv.findSymbol ge.globals _cos = some cosBlock)
    (contract : SourceCallbackContract ge (.Vptr cosBlock Integers.Ptrofs.zero) function cosine) :
    ∃ final,
      EvalFuncall ge memory (.Internal Typed.testfun) [.Vfloat x] E0 final
        (.Vfloat (Binary64.testfun cosine x)) ∧ CallMemory memory final := by
  obtain ⟨entered, hentry, hload, hfreeable, hentryMemory⟩ :=
    testfun_entry ge.expressionEnv memory x
  obtain ⟨afterBody, hexpression, hbodyMemory⟩ :=
    testfun_expression ge entered memory.nextblock cosBlock function cosine x
      hsymbol contract hload
  have hbody : ExecStmt ge (testfunLocals memory.nextblock) entered Typed.testfun.fn_body
      E0 afterBody (.return (some (.Vfloat (Binary64.testfun cosine x), tdouble))) := by
    rw [testfun_body_syntax]
    exact .return_some _ _ _ _ _ _ hexpression
  obtain ⟨final, hfree, hmemory⟩ := testfun_free ge.composites memory entered afterBody x
    hload hfreeable hentryMemory hbodyMemory
  exact ⟨final, hentry.eval_funcall hbody ⟨by decide, rfl⟩ hfree, hmemory⟩

/-- When `callback` resolves to `Typed.testfun` and `cos` has a `SourceCallbackContract` for
`cosine`, the callback pointer satisfies `SourceCallbackContract` for
`Binary64.testfun cosine`, which is what `integrator_call` needs. -/
theorem testfun_callback_contract (ge : GlobalEnv) (callback cosBlock : Block)
    (function : FunDef) (cosine : Floats.Float → Floats.Float)
    (hcallback : Genv.findFunct ge.globals (.Vptr callback Integers.Ptrofs.zero) =
      some (.Internal Typed.testfun))
    (hsymbol : Genv.findSymbol ge.globals _cos = some cosBlock)
    (contract : SourceCallbackContract ge (.Vptr cosBlock Integers.Ptrofs.zero) function cosine) :
    SourceCallbackContract ge (.Vptr callback Integers.Ptrofs.zero)
      (.Internal Typed.testfun) (Binary64.testfun cosine) :=
  ⟨hcallback, rfl, fun memory x =>
    testfun_call ge memory cosBlock function cosine x hsymbol contract⟩

end Quadrature.CSource.C

namespace Quadrature.CSource.Typed

open CC Binary64.ClightSource

variable [ExternalCalls]

/-- `C.testfun_call` restated for the function that parsing and elaborating the original C text
of `testfun` produces. -/
theorem testfun_call (ge : C.GlobalEnv) (memory : Mem) (cosBlock : Block)
    (function : C.FunDef) (cosine : Floats.Float → Floats.Float) (x : Floats.Float)
    (hsymbol : Genv.findSymbol ge.globals _cos = some cosBlock)
    (contract : C.SourceCallbackContract ge (.Vptr cosBlock Integers.Ptrofs.zero)
      function cosine) :
    ∃ final,
      SourceFunctionCall CSourceData.source "testfun" ge [.Vfloat x] memory E0 final
        (.Vfloat (Binary64.testfun cosine x)) ∧ C.CallMemory memory final := by
  obtain ⟨final, hcall, hmemory⟩ := C.testfun_call ge memory cosBlock function cosine x
    hsymbol contract
  exact ⟨final, ⟨testfun, testfun_elaboration, hcall⟩, hmemory⟩

end Quadrature.CSource.Typed
