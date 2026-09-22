import Quadrature.CSource.Library.Initialization
import Quadrature.CSource.Wrapper.Total
import Quadrature.Clight.StoredAccuracy

/-!
# Total correctness and accuracy of the initialized C library

`parsed_wrapper_total_accuracy` connects the selected source text and its
initialization to every execution of the original two-point wrapper.
`integral_total_accuracy` covers all ten stored orders. The function calls
use the C small-step semantics with unrestricted operand order and the
verified internal cosine. No callback or table premise remains.
-/

namespace Quadrature.CSource.C.Library

open CC

variable [ExternalCalls]

/-- Initialization and symbol lookup select a function whose every C execution returns `value`
and preserves the memory established by initialization. -/
def InitializedCallCorrect (library : C.Library) (name : Ident)
    (args : List Val) (value : Val) : Prop :=
  ∃ memory block function,
    library.initMem = some memory ∧
    Genv.findSymbol library.globalEnv.globals name = some block ∧
    Genv.findFunct library.globalEnv.globals (.Vptr block Integers.Ptrofs.zero) = some function ∧
    SmallStep.CallCorrect library.globalEnv memory function args value

end Quadrature.CSource.C.Library

namespace Quadrature.CSource.Library

open CC Binary64 Binary64.ClightSource FloatLib.Floats.Formats.BinaryInterchange
open C.SmallStep

variable [ExternalCalls]

/-- The initialized callback uses the internal C cosine and terminates in every operand order. -/
theorem callback_correct :
    C.CallbackCorrect globalEnv (.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero)
      (.Internal Typed.testfun) (testfun Polynomial.cosine) :=
  C.polynomial_callback_correct globalEnv _ _ (wrapperFunctions _).callback_function
    (cosine_symbol _) (cosine_function _)

/-- Every call of the initialized integrator returns its stored binary64 result.
The empty rule returns positive zero, and orders one to ten use the initialized tables. -/
theorem integrate_call_correct (n : Nat) (hn : n ≤ 10) :
    CallCorrect globalEnv initialMemory (.Internal Typed.integrate)
      [.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero, .Vint (Integers.Int.repr n)]
      (.Vfloat (Clight.StoredPolynomial.result n)) := by
  have hnodes : (tableFunctions (.Internal Cosine.function)).nodes < initialMemory.nextblock := by
    rw [initial_nextblock]
    decide
  have hweights :
      (tableFunctions (.Internal Cosine.function)).weights < initialMemory.nextblock := by
    rw [initial_nextblock]
    decide
  have cells : Clight.TableCells initialMemory
      (tableFunctions (.Internal Cosine.function)).nodes
      (tableFunctions (.Internal Cosine.function)).weights
      (Clight.storedTerms n).length 0 (Clight.storedTerms n) := by
    rw [Clight.stored_terms_length n hn]
    exact table_cells (.Internal Cosine.function) n hn
  simpa only [Clight.stored_terms_length n hn, Clight.StoredPolynomial.result] using
    C.integrator_call_correct globalEnv initialMemory (tableFunctions (.Internal Cosine.function))
      (Positive.ofNat 6) (.Internal Typed.testfun) (testfun Polynomial.cosine)
      (Clight.storedTerms n) (by rw [Clight.stored_terms_length n hn]; exact hn)
      hnodes hweights callback_correct cells

/-- Every initialized two-point wrapper call returns its certified binary64 result. -/
theorem wrapper_call_correct :
    CallCorrect globalEnv initialMemory (.Internal Typed.integrateTestfun) []
      (.Vfloat (Clight.StoredPolynomial.result 2)) :=
  C.wrapper_call_correct globalEnv initialMemory (tableFunctions (.Internal Cosine.function))
    (wrapperFunctions (.Internal Cosine.function)) (testfun Polynomial.cosine) callback_correct
    (table_cells (.Internal Cosine.function) 2 (by decide))

/-- Initialization and lookup discharge every premise of the complete integrator call proof. -/
theorem initialized_integrate_correct (n : Nat) (hn : n ≤ 10) :
    polynomialLibrary.InitializedCallCorrect _integrate
      [.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero, .Vint (Integers.Int.repr n)]
      (.Vfloat (Clight.StoredPolynomial.result n)) :=
  ⟨initialMemory, Positive.ofNat 5, .Internal Typed.integrate,
    initialized _, rfl, (wrapperFunctions _).integrator_function, integrate_call_correct n hn⟩

/-- Initialization and lookup discharge every premise of the complete wrapper call proof. -/
theorem initialized_wrapper_correct :
    polynomialLibrary.InitializedCallCorrect _integrate_testfun []
      (.Vfloat (Clight.StoredPolynomial.result 2)) :=
  ⟨initialMemory, Positive.ofNat 7, .Internal Typed.integrateTestfun,
    initialized _, rfl, wrapper_function _, wrapper_call_correct⟩

/-- All ten initialized C integrator calls terminate correctly in every evaluation order.
Their returned binary64 values are finite and satisfy the certified integral-error bounds. -/
theorem integral_total_accuracy (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    polynomialLibrary.InitializedCallCorrect _integrate
      [.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero, .Vint (Integers.Int.repr n)]
      (.Vfloat (Clight.StoredPolynomial.result n)) ∧
    Model.isFinite (Clight.StoredPolynomial.result n) = true ∧
    |Model.toReal (Clight.StoredPolynomial.result n) -
      ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤ Clight.StoredPolynomial.errorBound n :=
  ⟨initialized_integrate_correct n hhi, Clight.StoredPolynomial.integral_accuracy n hlo hhi⟩

/-- The parsed and initialized original wrapper, with the shipped C polynomial, returns
finite bits `0x3fead02c771c35ed` within `0.00356` of the real integral in every C evaluation
order. All calls terminate, and no cosine or table contract remains as a hypothesis. -/
theorem parsed_wrapper_total_accuracy :
    ∃ library value,
      fromSources CSourceData.source Cosine.source = some library ∧
      library.InitializedCallCorrect _integrate_testfun [] (.Vfloat value) ∧
      value = Model.ofNatBits 0x3fead02c771c35ed ∧
      Model.isFinite value = true ∧
      |Model.toReal value - ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤
        (356 : ℝ) / 100000 :=
  ⟨polynomialLibrary, Clight.StoredPolynomial.result 2, from_sources,
    initialized_wrapper_correct,
    Clight.StoredPolynomial.result_value 2 (by decide) (by decide),
    Clight.StoredPolynomial.integral_accuracy 2 (by decide) (by decide)⟩

end Quadrature.CSource.Library
