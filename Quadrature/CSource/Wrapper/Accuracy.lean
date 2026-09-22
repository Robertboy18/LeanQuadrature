import Quadrature.CSource.Wrapper.Function
import Quadrature.Examples.CosineAccuracy

/-!
# Numerical accuracy of the original wrapper in the strategy semantics

`integrate_testfun_accuracy` composes the wrapper execution of
`Quadrature.CSource.Wrapper.Function` with the two-point bound
`two_point_program_accuracy` of `Quadrature.Examples.CosineAccuracy`. Execution of
`cos` (`SourceCallbackContract`) and its accuracy (`CosineContract`) are two
explicit hypotheses, and the table and function environment must satisfy
`SourceTableFunctions` and `SourceWrapperFunctions`.
-/

namespace Quadrature.CSource.Typed

open CC Binary64.ClightSource FloatLib.Floats.Formats.BinaryInterchange

variable [ExternalCalls]

/-- Given the wrapper's execution hypotheses and `CosineContract cosine`, the wrapper parsed from
the original C text returns a finite value and satisfies `CallMemory`. The value is within the
0.00356 bound proved in `Quadrature.Examples.CosineAccuracy` of ∫₋₁¹ ½(1−x)cos x dx. -/
theorem integrate_testfun_accuracy (ge : C.GlobalEnv) (memory : Mem)
    (tables : C.SourceTableFunctions ge) (functions : C.SourceWrapperFunctions ge)
    (cosBlock : Block) (function : C.FunDef) (cosine : Floats.Float → Floats.Float)
    (cells : Binary64.Clight.TableCells memory tables.nodes tables.weights 2 0
      Binary64.twoPointTerms)
    (hsymbol : Genv.findSymbol ge.globals _cos = some cosBlock)
    (contract : C.SourceCallbackContract ge (.Vptr cosBlock Integers.Ptrofs.zero)
      function cosine)
    (haccuracy : Binary64.CosineContract cosine) :
    ∃ final value,
      SourceFunctionCall CSourceData.source "integrate_testfun" ge [] memory E0 final
        (.Vfloat value) ∧ C.CallMemory memory final ∧
      value = Binary64.integrate (Binary64.testfun cosine) Binary64.twoPointTerms ∧
      Model.isFinite value = true ∧
      |Model.toReal value - ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤
        (356 / 100000 : ℝ) := by
  obtain ⟨final, hcall, hmemory⟩ := integrate_testfun_call ge memory tables functions
    cosBlock function cosine cells hsymbol contract
  exact ⟨final, _, hcall, hmemory, rfl, Binary64.two_point_program_accuracy cosine haccuracy⟩

/-- The same bound when `cos` is an external function with an external-call contract for
`cosine`. The contracts for `testfun` and `integrate` are derived, not assumed. -/
theorem integrate_testfun_external_accuracy (ge : C.GlobalEnv) (memory : Mem)
    (tables : C.SourceTableFunctions ge) (functions : C.SourceWrapperFunctions ge)
    (cosBlock : Block) (externalFunction : ExtFun) (cosine : Floats.Float → Floats.Float)
    (cells : Binary64.Clight.TableCells memory tables.nodes tables.weights 2 0
      Binary64.twoPointTerms)
    (hsymbol : Genv.findSymbol ge.globals _cos = some cosBlock)
    (hfunction : Genv.findFunct ge.globals (.Vptr cosBlock Integers.Ptrofs.zero) =
      some (.External externalFunction [tdouble] tdouble cc_default))
    (hexternal : ∀ memory x, ∃ final,
      externalCall externalFunction (Genv.toSenv ge.globals) [.Vfloat x]
        memory E0 (.Vfloat (cosine x)) final ∧ C.CallMemory memory final)
    (haccuracy : Binary64.CosineContract cosine) :
    ∃ final value,
      SourceFunctionCall CSourceData.source "integrate_testfun" ge [] memory E0 final
        (.Vfloat value) ∧ C.CallMemory memory final ∧
      value = Binary64.integrate (Binary64.testfun cosine) Binary64.twoPointTerms ∧
      Model.isFinite value = true ∧
      |Model.toReal value - ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤
        (356 / 100000 : ℝ) :=
  integrate_testfun_accuracy ge memory tables functions cosBlock
    (.External externalFunction [tdouble] tdouble cc_default) cosine cells hsymbol
    (C.SourceCallbackContract.of_external ge (.Vptr cosBlock Integers.Ptrofs.zero)
      externalFunction cosine hfunction hexternal) haccuracy

end Quadrature.CSource.Typed
