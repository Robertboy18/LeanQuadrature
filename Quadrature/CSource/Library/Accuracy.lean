import Quadrature.CSource.Library.Initialization
import Quadrature.Clight.StoredAccuracy

/-!
# Accuracy of the initialized C library with an internal cosine

`parsed_wrapper_accuracy` starts with the original C text and `cosine.c`,
initializes their selected library, resolves `integrate_testfun`, and executes
the wrapper to a finite binary64 value within `0.00356` of the real integral.
Neither cosine execution nor table storage is a hypothesis.

`integral_accuracy` gives the corresponding result for all ten stored orders.
These are terminating calls in the typed C strategy semantics described in
`Semantics/Strategy`; the stronger Clight execution results remain separate.
-/

namespace Quadrature.CSource.Library

open CC Binary64 Binary64.ClightSource FloatLib.Floats.Formats.BinaryInterchange

variable [ExternalCalls]

/-- The initialized `cos` pointer satisfies its execution contract by the internal C proof. -/
theorem cosine_contract :
    C.SourceCallbackContract globalEnv (.Vptr (Positive.ofNat 8) Integers.Ptrofs.zero)
      (.Internal Cosine.function) Polynomial.cosine :=
  Cosine.callback_contract globalEnv _ (cosine_function _)

/-- The original `testfun` callback now has a proved execution contract with no external call. -/
theorem callback_contract :
    C.SourceCallbackContract globalEnv (.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero)
      (.Internal Typed.testfun) (testfun Polynomial.cosine) :=
  C.testfun_callback_contract globalEnv _ _ (.Internal Cosine.function) Polynomial.cosine
    (wrapperFunctions _).callback_function (cosine_symbol _) cosine_contract

/-- The parsed original integrator executes from initialized memory on any stored order.
The zero-node case returns positive zero; orders one to ten use the initialized tables. -/
theorem source_integrate_call (n : Nat) (hn : n ≤ 10) :
    ∃ final,
      Typed.SourceFunctionCall CSourceData.source "integrate" globalEnv
        [.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero, .Vint (Integers.Int.repr n)]
        initialMemory E0 final (.Vfloat (Clight.StoredPolynomial.result n)) ∧
      C.CallMemory initialMemory final := by
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
    Typed.integrate_call globalEnv initialMemory (tableFunctions (.Internal Cosine.function))
      (Positive.ofNat 6) (.Internal Typed.testfun) (testfun Polynomial.cosine)
      (Clight.storedTerms n) (by rw [Clight.stored_terms_length n hn]; exact hn)
      hnodes hweights callback_contract cells

/-- The parsed original two-point wrapper executes from initialized memory with the C
polynomial bound at its `cos` symbol. -/
theorem source_wrapper_call :
    ∃ final,
      Typed.SourceFunctionCall CSourceData.source "integrate_testfun" globalEnv []
        initialMemory E0 final (.Vfloat (Clight.StoredPolynomial.result 2)) ∧
      C.CallMemory initialMemory final := by
  have cells : Clight.TableCells initialMemory
      (tableFunctions (.Internal Cosine.function)).nodes
      (tableFunctions (.Internal Cosine.function)).weights 2 0 twoPointTerms :=
    table_cells (.Internal Cosine.function) 2 (by decide)
  exact Typed.integrate_testfun_call globalEnv initialMemory
    (tableFunctions (.Internal Cosine.function)) (wrapperFunctions (.Internal Cosine.function))
    (Positive.ofNat 8) (.Internal Cosine.function) Polynomial.cosine cells
    (cosine_symbol _) cosine_contract

/-- Initialization and symbol lookup lead to the parsed integrator and its exact rounded
result. All function, table and callback premises have been discharged. -/
theorem initialized_integrate_call (n : Nat) (hn : n ≤ 10) :
    ∃ final,
      polynomialLibrary.InitializedCall _integrate
        [.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero, .Vint (Integers.Int.repr n)]
        E0 final (.Vfloat (Clight.StoredPolynomial.result n)) ∧
      C.CallMemory initialMemory final := by
  obtain ⟨final, ⟨function, hsource, hcall⟩, hmemory⟩ := source_integrate_call n hn
  rw [Typed.integrate_elaboration] at hsource
  cases Option.some.inj hsource
  exact ⟨final, ⟨initialMemory, Positive.ofNat 5, .Internal Typed.integrate,
    initialized _, rfl, (wrapperFunctions _).integrator_function, hcall⟩, hmemory⟩

/-- Initialization and lookup of `integrate_testfun` lead to the verified two-point call. -/
theorem initialized_wrapper_call :
    ∃ final,
      polynomialLibrary.InitializedCall _integrate_testfun [] E0 final
        (.Vfloat (Clight.StoredPolynomial.result 2)) ∧
      C.CallMemory initialMemory final := by
  obtain ⟨final, ⟨function, hsource, hcall⟩, hmemory⟩ := source_wrapper_call
  rw [Typed.integrate_testfun_elaboration] at hsource
  cases Option.some.inj hsource
  exact ⟨final, ⟨initialMemory, Positive.ofNat 7, .Internal Typed.integrateTestfun,
    initialized _, rfl, wrapper_function _, hcall⟩, hmemory⟩

/-- Each of the ten initialized C applications returns the certified binary64 result, which is
finite and within its recorded error bound of the real integral. -/
theorem integral_accuracy (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    ∃ final,
      polynomialLibrary.InitializedCall _integrate
        [.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero, .Vint (Integers.Int.repr n)]
        E0 final (.Vfloat (Clight.StoredPolynomial.result n)) ∧
      C.CallMemory initialMemory final ∧
      Model.isFinite (Clight.StoredPolynomial.result n) = true ∧
      |Model.toReal (Clight.StoredPolynomial.result n) -
        ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤ Clight.StoredPolynomial.errorBound n := by
  obtain ⟨final, hcall, hmemory⟩ := initialized_integrate_call n hhi
  exact ⟨final, hcall, hmemory, Clight.StoredPolynomial.integral_accuracy n hlo hhi⟩

/-- The original wrapper, using the shipped C polynomial, returns a finite value within
`0.00356` of the integral. Parsing, library initialization and the complete call are included;
no cosine or memory contract remains as a hypothesis. -/
theorem parsed_wrapper_accuracy :
    ∃ library final value,
      fromSources CSourceData.source Cosine.source = some library ∧
      C.Library.InitializedCall library _integrate_testfun [] E0 final (.Vfloat value) ∧
      C.CallMemory initialMemory final ∧
      value = Model.ofNatBits 0x3fead02c771c35ed ∧
      Model.isFinite value = true ∧
      |Model.toReal value - ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤
        (356 : ℝ) / 100000 := by
  obtain ⟨final, hcall, hmemory⟩ := initialized_wrapper_call
  exact ⟨polynomialLibrary, final, Clight.StoredPolynomial.result 2,
    from_sources, hcall, hmemory,
    Clight.StoredPolynomial.result_value 2 (by decide) (by decide),
    Clight.StoredPolynomial.integral_accuracy 2 (by decide) (by decide)⟩

end Quadrature.CSource.Library
