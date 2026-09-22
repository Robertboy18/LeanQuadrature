import Quadrature.CSource.Callback.Function
import Quadrature.CSource.Integrator.Function

/-!
# Execution of the original two-point wrapper

The wrapper `integrate_testfun` takes the address of the original callback and
calls the original integrator with the integer argument `2`. `wrapper_call`
executes both bodies in the strategy semantics. The remaining hypotheses name
the function symbols (`SourceWrapperFunctions`, `SourceTableFunctions`), the
two table cells and the `cos` contract alone.
-/

namespace Quadrature.CSource.C

open CC Binary64.ClightSource

/-- `SourceWrapperFunctions ge`: the symbols `integrate` and `testfun` resolve to blocks whose
function pointers are bound to `Typed.integrate` and `Typed.testfun`. -/
structure SourceWrapperFunctions (ge : GlobalEnv) where
  integrator : Block
  callback : Block
  integrator_symbol : Genv.findSymbol ge.globals _integrate = some integrator
  callback_symbol : Genv.findSymbol ge.globals _testfun = some callback
  integrator_function : Genv.findFunct ge.globals (.Vptr integrator Integers.Ptrofs.zero) =
    some (.Internal Typed.integrate)
  callback_function : Genv.findFunct ge.globals (.Vptr callback Integers.Ptrofs.zero) =
    some (.Internal Typed.testfun)

/-- The wrapper's return expression `integrate(&testfun, 2)`. -/
def wrapperExpression : Expr :=
  .Ecall (readVar _integrate (.Tfunction [tptr callbackType, tint] tdouble cc_default))
    (.Econs (.Eaddrof (.Evar _testfun callbackType) (tptr callbackType))
      (.Econs (.Eval (.Vint (Integers.Int.repr 2)) tint) .Enil)) tdouble

/-- The elaborated body of `Typed.integrateTestfun` is `return wrapperExpression;`, by `rfl`. -/
theorem wrapper_body_syntax :
    Typed.integrateTestfun.fn_body = .Sreturn (some wrapperExpression) := rfl

variable [ExternalCalls]

/-- Given the symbol structures, the two-point table cells and a `cos` contract for `cosine`,
`wrapperExpression` evaluates in the empty local environment to
`Vfloat (integrate (testfun cosine) twoPointTerms)` and satisfies `CallMemory`. -/
theorem wrapper_expression (ge : GlobalEnv) (memory : Mem)
    (tables : SourceTableFunctions ge) (functions : SourceWrapperFunctions ge)
    (cosBlock : Block) (function : FunDef) (cosine : Floats.Float → Floats.Float)
    (cells : Binary64.Clight.TableCells memory tables.nodes tables.weights 2 0
      Binary64.twoPointTerms)
    (hsymbol : Genv.findSymbol ge.globals _cos = some cosBlock)
    (contract : SourceCallbackContract ge (.Vptr cosBlock Integers.Ptrofs.zero) function cosine) :
    ∃ final,
      EvalExpression ge emptyEnv memory wrapperExpression E0 final
        (.Vfloat (Binary64.integrate (Binary64.testfun cosine) Binary64.twoPointTerms)) ∧
      CallMemory memory final := by
  have callbackContract := testfun_callback_contract ge functions.callback cosBlock
    function cosine functions.callback_function hsymbol contract
  obtain ⟨final, hcall, hmemory⟩ := integrator_call ge memory tables functions.callback
    (.Internal Typed.testfun) (Binary64.testfun cosine) Binary64.twoPointTerms
    (by decide) (block_valid_of_load cells.2.1) (block_valid_of_load cells.1)
    callbackContract cells
  refine ⟨final, ?_, hmemory⟩
  apply EvalExpression.intro (a' := .Eval
    (.Vfloat (Binary64.integrate (Binary64.testfun cosine) Binary64.twoPointTerms)) tdouble)
  · apply EvalExpr.call (t₁ := E0) (t₂ := E0) (t₃ := E0)
      (m₁ := memory) (m₂ := memory)
      (vf := .Vptr functions.integrator Integers.Ptrofs.zero)
      (types := [tptr callbackType, tint]) (result := tdouble) (cc := cc_default)
      (fd := .Internal Typed.integrate)
    · exact read_var_effects ge emptyEnv memory _integrate
        (.Tfunction [tptr callbackType, tint] tdouble cc_default) rfl
    · exact .cons _ _ _ _ E0 _ _ E0 _ _
        (.addrof _ _ _ _ _ _ _ (.var _ _ _ _))
        (.cons _ _ _ _ E0 _ _ E0 _ _ (.value _ _ _ _) (.nil _ _))
    · exact read_global_function ge emptyEnv memory _integrate functions.integrator
        [tptr callbackType, tint] tdouble cc_default rfl functions.integrator_symbol
    · exact .cons _ _ _ _ _ _ _
        (.addrof _ _ _ _ (.var_global _ _ _ rfl functions.callback_symbol)) rfl
        (.cons _ _ _ _ _ _ _ (.value _ _) rfl .nil)
    · rfl
    · exact functions.integrator_function
    · rfl
    · exact hcall
  · exact .value _ _

/-- Under the hypotheses of `wrapper_expression`, calling `Typed.integrateTestfun` with no
arguments returns `Vfloat (integrate (testfun cosine) twoPointTerms)` silently in a memory
satisfying `CallMemory`. The wrapper has no locals, so entry and freeing are trivial. -/
theorem wrapper_call (ge : GlobalEnv) (memory : Mem)
    (tables : SourceTableFunctions ge) (functions : SourceWrapperFunctions ge)
    (cosBlock : Block) (function : FunDef) (cosine : Floats.Float → Floats.Float)
    (cells : Binary64.Clight.TableCells memory tables.nodes tables.weights 2 0
      Binary64.twoPointTerms)
    (hsymbol : Genv.findSymbol ge.globals _cos = some cosBlock)
    (contract : SourceCallbackContract ge (.Vptr cosBlock Integers.Ptrofs.zero) function cosine) :
    ∃ final,
      EvalFuncall ge memory (.Internal Typed.integrateTestfun) [] E0 final
        (.Vfloat (Binary64.integrate (Binary64.testfun cosine) Binary64.twoPointTerms)) ∧
      CallMemory memory final := by
  obtain ⟨final, hexpression, hmemory⟩ :=
    wrapper_expression ge memory tables functions cosBlock function cosine
      cells hsymbol contract
  have entry : FunctionEntry ge.expressionEnv Typed.integrateTestfun []
      memory emptyEnv memory :=
    ⟨by simp [Typed.integrateTestfun], memory, .nil _ _, .nil _⟩
  have body : ExecStmt ge emptyEnv memory Typed.integrateTestfun.fn_body E0 final
      (.return (some (.Vfloat
        (Binary64.integrate (Binary64.testfun cosine) Binary64.twoPointTerms), tdouble))) := by
    rw [wrapper_body_syntax]
    exact .return_some _ _ _ _ _ _ hexpression
  exact ⟨final, entry.eval_funcall body ⟨by decide, rfl⟩ rfl, hmemory⟩

end Quadrature.CSource.C

namespace Quadrature.CSource.Typed

open CC Binary64.ClightSource

variable [ExternalCalls]

/-- `wrapper_call` restated for the function that parsing and elaborating the original C text of
`integrate_testfun` produces. -/
theorem integrate_testfun_call (ge : C.GlobalEnv) (memory : Mem)
    (tables : C.SourceTableFunctions ge) (functions : C.SourceWrapperFunctions ge)
    (cosBlock : Block) (function : C.FunDef) (cosine : Floats.Float → Floats.Float)
    (cells : Binary64.Clight.TableCells memory tables.nodes tables.weights 2 0
      Binary64.twoPointTerms)
    (hsymbol : Genv.findSymbol ge.globals _cos = some cosBlock)
    (contract : C.SourceCallbackContract ge (.Vptr cosBlock Integers.Ptrofs.zero)
      function cosine) :
    ∃ final,
      SourceFunctionCall CSourceData.source "integrate_testfun" ge [] memory E0 final
        (.Vfloat (Binary64.integrate (Binary64.testfun cosine) Binary64.twoPointTerms)) ∧
      C.CallMemory memory final := by
  obtain ⟨final, hcall, hmemory⟩ := C.wrapper_call ge memory tables functions cosBlock
    function cosine cells hsymbol contract
  exact ⟨final, ⟨integrateTestfun, integrate_testfun_elaboration, hcall⟩, hmemory⟩

end Quadrature.CSource.Typed
