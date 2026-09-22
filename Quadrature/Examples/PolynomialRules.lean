import FloatLib.Numerics.Enclosure.Trigonometric.SinCosProof
import Quadrature.Examples.TwoPointCosine
import Quadrature.Rules.Basic

/-!
# Complete loop results for orders one through four

All ten stored rules have stored-rule certificates in `Rules/Certificates`.
What is special about orders one through four is that the complete loop result
for the polynomial cosine callback is evaluated in the kernel here
(`result_value`), with the ten-order versions in `Clight/StoredAccuracy.lean`.
The polynomial cosine follows the coefficient encodings and Horner order of the
companion Rocq proofs in `compcert/InternalCosine.v`, and the loop uses the
weights stored by the original C program, including its three-point outer
weight. Exact rational decoding of each result and a sine enclosure then give
the integral error bounds.
-/

namespace Quadrature.Binary64.Polynomial

open FloatLib.Floats.Formats.BinaryInterchange

/-- The four orders whose complete loop result is evaluated in the kernel in this file. -/
inductive Order where
  | one | two | three | four
  deriving DecidableEq

/-- Stored binary64 coefficients in ascending polynomial degree. -/
def coefficients : List Value :=
  [4607182418800017408, 13826050856027422720, 4586165620538955093,
   13787419979223755799, 4537941361671905306, 13732177094651715420,
   4477122120089393304, 13666517717442657437].map Model.ofNatBits

/-- Each multiplication and addition is separately rounded, including the final zero. -/
def horner (z : Value) : List Value → Value
  | [] => zero
  | c :: cs => Model.add c (Model.mul z (horner z cs))

/-- The degree-fourteen polynomial is evaluated in the rounded square of the input. -/
def cosine (x : Value) : Value := horner (Model.mul x x) coefficients

/-- The weight and node list of the stored rule of each order, in accumulation order. -/
def terms : Order → List (Value × Value)
  | .one => oneStored.terms
  | .two => twoStored.terms
  | .three => threeStored.terms
  | .four => fourStored.terms

/-- The complete loop result `integrate (testfun cosine) (terms order)` with the polynomial
cosine as the callback's cosine. -/
def result (order : Order) : Value := integrate (testfun cosine) (terms order)

/-- The bit pattern of `result order`, established by `result_value`. -/
def resultBits : Order → Nat
  | .one => 0x3ff0000000000000
  | .two => 0x3fead02c771c35ed
  | .three => 0x3feaed9520c8a014
  | .four => 0x3feaed5443a06327

-- Kernel evaluation of the complete loop, polynomial cosine included, for all four orders.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
/-- `result order` has bit pattern `resultBits order`, by kernel evaluation of the whole loop. -/
theorem result_value (order : Order) :
    result order = Model.ofNatBits (resultBits order) := by
  cases order <;> decide +kernel

/-- Each of the four loop results is a finite binary64 value. -/
theorem result_finite (order : Order) : Model.isFinite (result order) = true := by
  rw [result_value]
  cases order <;> decide

open FloatLib.Numerics

/-- The dyadic decoding of `result order`. -/
def resultDyadic : Order → FloatLib.Numerics.Dyadic
  | .one => ⟨false, 4503599627370496, -52⟩
  | .two => ⟨false, 7547238789953005, -53⟩
  | .three => ⟨false, 7579574150406164, -53⟩
  | .four => ⟨false, 7579295562097447, -53⟩

/-- The exact real value of `result order`, written as a rational. -/
noncomputable def resultReal : Order → ℝ
  | .one => 1
  | .two => 7547238789953005 / 9007199254740992
  | .three => 7579574150406164 / 9007199254740992
  | .four => 7579295562097447 / 9007199254740992

/-- The proved error bound of each order against `sin 1`: `0.159`, `0.00356`, `3.1·10⁻⁵`, and
`1.5·10⁻⁷`. -/
noncomputable def errorBound : Order → ℝ
  | .one => 159 / 1000
  | .two => 356 / 100000
  | .three => 31 / 1000000
  | .four => 15 / 100000000

/-- `result order` decodes to `resultDyadic order`. -/
theorem result_decode (order : Order) :
    Model.toDyadic? (result order) = some (resultDyadic order) := by
  rw [result_value]
  cases order <;> decide

/-- The real value of `result order` is `resultReal order`. -/
theorem result_toReal (order : Order) :
    Model.toReal (result order) = resultReal order := by
  rw [Model.toReal_eq, result_decode]
  cases order <;> norm_num [resultDyadic, resultReal, Dyadic.toReal,
    Dyadic.signedSignificand]

/-- `sin 1` lies in `[0.8414709848078965, 0.8414709848078966]`, from a degree-18 rational
Taylor enclosure. This width of `10⁻¹⁶` resolves the four-point error. -/
theorem sin_one_enclosure :
    (8414709848078965 / 10 ^ 16 : ℝ) ≤ Real.sin 1 ∧
    Real.sin 1 ≤ (8414709848078966 / 10 ^ 16 : ℝ) := by
  have h := Enclosure.contains_sin (1 : ℚ) 18
  have hlo : (8414709848078965 / 10 ^ 16 : ℚ) ≤ (Enclosure.sin 1 18).lo := by
    decide +kernel
  have hhi : (Enclosure.sin 1 18).hi ≤ (8414709848078966 / 10 ^ 16 : ℚ) := by
    decide +kernel
  have hlo' := (Rat.cast_le (K := ℝ)).mpr hlo
  have hhi' := (Rat.cast_le (K := ℝ)).mpr hhi
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one] at h hlo' hhi'
  constructor
  · convert hlo'.trans h.1 using 1; norm_num
  · convert h.2.trans hhi' using 1; norm_num

/-- The real value of `result order` is within `errorBound order` of `sin 1`. Both sides are
explicit rationals apart from the sine enclosure, so `norm_num` and `linarith` finish. -/
theorem result_accuracy (order : Order) :
    |Model.toReal (result order) - Real.sin 1| ≤ errorBound order := by
  rw [result_toReal]
  have h := sin_one_enclosure
  cases order <;> norm_num [resultReal, errorBound, abs_le] <;> constructor <;> linarith

/-- The rounded loop result of each order is finite and within `errorBound order` of the
integral of the integrand over `[-1, 1]`, which is `sin 1`. -/
theorem integral_accuracy (order : Order) :
    Model.isFinite (result order) = true ∧
    |Model.toReal (result order) - ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤
      errorBound order := by
  rw [Example.integral_eq]
  exact ⟨result_finite order, result_accuracy order⟩

end Quadrature.Binary64.Polynomial
