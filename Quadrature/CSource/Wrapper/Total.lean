import Quadrature.CSource.Wrapper.Function
import Quadrature.CSource.Integrator.Total

/-!
# Total correctness of the original two-point wrapper

The wrapper's expression takes the address of `testfun` and calls
`integrate` with two nodes. Its complete C execution inherits the
integrator's total correctness and returns through the wrapper's own
function boundary.
-/

namespace Quadrature.CSource.C

open CC hiding State Cont Step
open Binary64.ClightSource SmallStep

variable [ExternalCalls]

/-- Every operand order of the wrapper's call expression produces the specified two-point sum. -/
theorem wrapper_read_eval (ge : GlobalEnv) (memory : Mem)
    (tables : SourceTableFunctions ge) (functions : SourceWrapperFunctions ge)
    (f : Floats.Float → Floats.Float)
    (contract : CallbackCorrect ge (.Vptr functions.callback Integers.Ptrofs.zero)
      (.Internal Typed.testfun) f)
    (cells : Binary64.Clight.TableCells memory tables.nodes tables.weights 2 0
      Binary64.twoPointTerms) :
    ReadEval ge emptyEnv memory .RV wrapperExpression
      (.value (.Vfloat (Binary64.integrate f Binary64.twoPointTerms))) := by
  apply ReadEval.call (pointer := .Vptr functions.integrator Integers.Ptrofs.zero)
    (parameters := [tptr callbackType, tint]) (returnType := tdouble) (cc := cc_default)
    (function := .Internal Typed.integrate)
    (values := [.Vptr functions.callback Integers.Ptrofs.zero, .Vint (Integers.Int.repr 2)])
  · exact .global_function ge _ memory _integrate functions.integrator
      [tptr callbackType, tint] tdouble cc_default rfl functions.integrator_symbol
  · exact .cons _ _ _ _ _ _ _
      (.addrof _ _ _ _ (.var_global _ _ _ rfl functions.callback_symbol)) (fun _ _ => rfl)
      (.cons _ _ _ _ _ _ _ (.value _ _) (fun _ _ => rfl) .nil)
  · exact functions.integrator_function
  · rfl
  · rfl
  · intro current hmemory
    have currentCells := hmemory.table_cells cells
    exact integrator_call_correct ge current tables functions.callback (.Internal Typed.testfun)
      f Binary64.twoPointTerms (by decide) (block_valid_of_load currentCells.2.1)
      (block_valid_of_load currentCells.1) contract currentCells

/-- Every complete wrapper call returns the two-point result and preserves the caller's memory. -/
theorem wrapper_call_correct (ge : GlobalEnv) (memory : Mem)
    (tables : SourceTableFunctions ge) (functions : SourceWrapperFunctions ge)
    (f : Floats.Float → Floats.Float)
    (contract : CallbackCorrect ge (.Vptr functions.callback Integers.Ptrofs.zero)
      (.Internal Typed.testfun) f)
    (cells : Binary64.Clight.TableCells memory tables.nodes tables.weights 2 0
      Binary64.twoPointTerms) :
    CallCorrect ge memory (.Internal Typed.integrateTestfun) []
      (.Vfloat (Binary64.integrate f Binary64.twoPointTerms)) := by
  intro cont hcont
  have entry : FunctionEntry ge.expressionEnv Typed.integrateTestfun []
      memory emptyEnv memory :=
    ⟨by simp [Typed.integrateTestfun], memory, .nil _ _, .nil _⟩
  apply Total.internal (by simp [Typed.integrateTestfun]) entry
  rw [wrapper_body_syntax]
  apply Total.statement (.return_start _ _ _ _ _)
  apply ((wrapper_read_eval ge memory tables functions f contract cells).total
    (.refl _) Typed.integrateTestfun _).bind
  rintro _ ⟨final, rfl, hmemory⟩
  apply Total.value (.return_finish _ _ _ _ _ _ _ _ rfl rfl)
  exact .done ⟨final, by rw [Cont.callCont_eq hcont], hmemory⟩

end Quadrature.CSource.C
