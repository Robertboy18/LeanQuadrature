import Quadrature.Clight.StoredRules

/-!
# Integral accuracy of all ten stored polynomial applications

`result_value` computes by kernel evaluation the binary64 result of the
integrator on each stored table slice with the internal cosine polynomial
(`Polynomial.cosine`, degree fourteen in `x` from the eight coefficients in
`x²` of `Polynomial.coefficients`). Exact dyadic decoding and the sine
enclosure `Polynomial.sin_one_enclosure` then bound each result's distance
from ∫₋₁¹ ½(1−x)cos x dx = sin 1 (`Example.integral_eq`). The bounds concern
this computation alone and do not rely on identifying each stored rule with an
exact Gaussian rule.
-/

namespace Quadrature.Binary64.Clight.StoredPolynomial

open FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

/-- The FloatLib fold of the polynomial callback over the stored `n`-node rule, in the operation
order of the C loop. -/
def result (n : Nat) : Value :=
  integrate (testfun Polynomial.cosine) (storedTerms n)

/-- The 64-bit encodings of `result n` for `n = 1, ..., 10`, and `0` elsewhere. -/
def resultBits : Nat → Nat
  | 1 => 0x3ff0000000000000
  | 2 => 0x3fead02c771c35ed
  | 3 => 0x3feaed9520c8a014
  | 4 => 0x3feaed5443a06327
  | 5 => 0x3feaed548f3f6f46
  | 6 => 0x3feaed548f08f234
  | 7 => 0x3feaed548f090ce1
  | 8 => 0x3feaed548f090cce
  | 9 => 0x3feaed548f090ccf
  | 10 => 0x3feaed548f090cd4
  | _ => 0

-- Evaluate the ten full quadratures, every callback included, and compare the encodings.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- For `1 ≤ n ≤ 10`, `result n` has the encoding `resultBits n`, by kernel evaluation. -/
theorem result_value (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    result n = Model.ofNatBits (resultBits n) := by
  interval_cases n <;> decide +kernel

/-- For `1 ≤ n ≤ 10`, `result n` is finite. -/
theorem result_finite (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    Model.isFinite (result n) = true := by
  rw [result_value n hlo hhi]
  interval_cases n <;> decide

/-- The exact dyadic value (sign, significand, exponent) of `result n` for `n = 1, ..., 10`. -/
def resultDyadic : Nat → FloatLib.Numerics.Dyadic
  | 1 => ⟨false, 4503599627370496, -52⟩
  | 2 => ⟨false, 7547238789953005, -53⟩
  | 3 => ⟨false, 7579574150406164, -53⟩
  | 4 => ⟨false, 7579295562097447, -53⟩
  | 5 => ⟨false, 7579296830811974, -53⟩
  | 6 => ⟨false, 7579296827241012, -53⟩
  | 7 => ⟨false, 7579296827247841, -53⟩
  | 8 => ⟨false, 7579296827247822, -53⟩
  | 9 => ⟨false, 7579296827247823, -53⟩
  | 10 => ⟨false, 7579296827247828, -53⟩
  | _ => ⟨false, 0, 0⟩

/-- The real number denoted by `resultDyadic n`. -/
noncomputable def resultReal (n : Nat) : ℝ := (resultDyadic n).toReal

/-- The absolute integral-error bound proved for `result n`, for `n = 1, ..., 10`, and `0`
elsewhere. The bound for `n = 8` exceeds that for `n = 7`, see `seven_error_lt_eight`. -/
noncomputable def errorBound : Nat → ℝ
  | 1 => 159 / 1000
  | 2 => 356 / 100000
  | 3 => 31 / 1000000
  | 4 => 15 / 100000000
  | 5 => 4 / 10 ^ 10
  | 6 => 8 / 10 ^ 13
  | 7 => 2 / 10 ^ 15
  | 8 => 4 / 10 ^ 15
  | 9 => 4 / 10 ^ 15
  | 10 => 3 / 10 ^ 15
  | _ => 0

/-- For `1 ≤ n ≤ 10`, decoding `result n` gives exactly `resultDyadic n`. -/
theorem result_decode (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    Model.toDyadic? (result n) = some (resultDyadic n) := by
  rw [result_value n hlo hhi]
  interval_cases n <;> decide

/-- For `1 ≤ n ≤ 10`, the real value of `result n` is `resultReal n`. -/
theorem result_toReal (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    Model.toReal (result n) = resultReal n := by
  rw [Model.toReal_eq, result_decode n hlo hhi]
  rfl

/-- For `1 ≤ n ≤ 10`, `result n` is within `errorBound n` of `sin 1`, by the enclosure of `sin 1`
and exact rational arithmetic on the decoded dyadic. -/
theorem result_accuracy (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    |Model.toReal (result n) - Real.sin 1| ≤ errorBound n := by
  rw [result_toReal n hlo hhi]
  have h := Polynomial.sin_one_enclosure
  interval_cases n <;>
    norm_num [resultReal, resultDyadic, errorBound, Dyadic.toReal,
      Dyadic.signedSignificand, abs_le] <;>
    constructor <;> linarith

/-- For `1 ≤ n ≤ 10`, `result n` is finite and within `errorBound n` of ∫₋₁¹ ½(1−x)cos x dx,
which equals `sin 1` by `Example.integral_eq`. -/
theorem integral_accuracy (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    Model.isFinite (result n) = true ∧
      |Model.toReal (result n) - ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤ errorBound n := by
  rw [Example.integral_eq]
  exact ⟨result_finite n hlo hhi, result_accuracy n hlo hhi⟩

/-- For the four supported orders, `result (orderCount order)` is `Polynomial.result order`. -/
theorem result_supported (order : Polynomial.Order) :
    result (orderCount order) = Polynomial.result order := by
  unfold result Polynomial.result
  rw [stored_terms_supported]

/-- For the four supported orders, `errorBound` agrees with `Polynomial.errorBound`. -/
theorem error_bound_supported (order : Polynomial.Order) :
    errorBound (orderCount order) = Polynomial.errorBound order := by
  cases order <;> rfl

/-- The eight-node result is farther from `sin 1` than the seven-node result: for this rounded
computation, adding a node can increase the error. -/
theorem seven_error_lt_eight :
    |Model.toReal (result 7) - Real.sin 1| <
      |Model.toReal (result 8) - Real.sin 1| := by
  rw [result_toReal 7 (by decide) (by decide), result_toReal 8 (by decide) (by decide)]
  have h := Polynomial.sin_one_enclosure
  norm_num [resultReal, resultDyadic, Dyadic.toReal, Dyadic.signedSignificand]
  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  linarith

end Quadrature.Binary64.Clight.StoredPolynomial

namespace Quadrature.Binary64.Clight

open FloatLib.Floats.Formats.BinaryInterchange ClightSource

/-- For `1 ≤ n ≤ 10`, the `n`-node polynomial call in `polynomialLibrary` runs silently to the
value with encoding `StoredPolynomial.resultBits n`, with `initialMemory` unchanged. -/
theorem stored_polynomial_execution_bits [CC.ExternalCalls]
    (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) (k : CC.Cont) :
    CC.StarE0 (CC.Step2 polynomialLibrary.globalenv)
      (storedLibraryCall (.Vptr testfunBlock (CC.Integers.Ptrofs.repr 0)) n k initialMemory)
      (.Returnstate (.Vfloat (Model.ofNatBits (StoredPolynomial.resultBits n)))
        (CC.callCont k) initialMemory) := by
  rw [← StoredPolynomial.result_value n hlo hhi]
  exact stored_polynomial_execution n hhi k

/-- For `1 ≤ n ≤ 10`, the `n`-node polynomial call runs silently to some finite value within
`StoredPolynomial.errorBound n` of ∫₋₁¹ ½(1−x)cos x dx. -/
theorem stored_polynomial_execution_accuracy [CC.ExternalCalls]
    (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) (k : CC.Cont) :
    ∃ value : Value,
      CC.StarE0 (CC.Step2 polynomialLibrary.globalenv)
        (storedLibraryCall (.Vptr testfunBlock (CC.Integers.Ptrofs.repr 0)) n k initialMemory)
        (.Returnstate (.Vfloat value) (CC.callCont k) initialMemory) ∧
      Model.isFinite value = true ∧
        |Model.toReal value - ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤
          StoredPolynomial.errorBound n :=
  ⟨StoredPolynomial.result n, stored_polynomial_execution n hhi k,
    StoredPolynomial.integral_accuracy n hlo hhi⟩

/-- With deterministic external calls, every value returned by the `n`-node polynomial call in
`polynomialLibrary` is finite and within `StoredPolynomial.errorBound n` of the integral. -/
theorem stored_polynomial_return_accuracy [calls : CC.ExternalCalls]
    [CC.ExternalCallsDeterministic calls]
    (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10)
    (value : Value) (memory : CC.Mem) (trace : CC.Trace)
    (h : CC.Star (CC.Step2 polynomialLibrary.globalenv)
      (storedLibraryCall (.Vptr testfunBlock (CC.Integers.Ptrofs.repr 0)) n .Kstop initialMemory)
      trace (.Returnstate (.Vfloat value) .Kstop memory)) :
    Model.isFinite value = true ∧
      |Model.toReal value - ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤
        StoredPolynomial.errorBound n := by
  have heq := CC.Val.Vfloat.inj
    (stored_polynomial_return_eq n hhi (.Vfloat value) memory trace h)
  rw [heq]
  exact StoredPolynomial.integral_accuracy n hlo hhi

/-- Given a `StoredLibraryContext` for `storedTerms n` and the polynomial callback contract in
any program, every value returned by the `n`-node call is finite and within
`StoredPolynomial.errorBound n` of the integral. -/
theorem stored_library_polynomial_return_accuracy [calls : CC.ExternalCalls]
    [CC.ExternalCallsDeterministic calls] (program : CC.Program) (m : CC.Mem)
    (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10)
    (ctx : StoredLibraryContext program.globalenv m (storedTerms n)) (ptr : CC.Val)
    (contract : LibraryCallbackContract program.globalenv m ptr
      (.Internal f_testfun) (testfun Polynomial.cosine))
    (value : Value) (memory : CC.Mem) (trace : CC.Trace)
    (h : CC.Star (CC.Step2 program.globalenv) (storedLibraryCall ptr n .Kstop m) trace
      (.Returnstate (.Vfloat value) .Kstop memory)) :
    Model.isFinite value = true ∧
      |Model.toReal value - ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤
        StoredPolynomial.errorBound n := by
  have heq := CC.Val.Vfloat.inj (stored_library_return_eq program m (storedTerms n) ctx
    (.Internal f_testfun) (testfun Polynomial.cosine) ptr contract (.Vfloat value) memory trace
    (by simpa only [stored_terms_length n hhi] using h))
  rw [heq]
  exact StoredPolynomial.integral_accuracy n hlo hhi

end Quadrature.Binary64.Clight
