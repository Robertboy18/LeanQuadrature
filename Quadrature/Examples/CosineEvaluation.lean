import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Trig
import FloatLib.Numerics.Enclosure.Trigonometric.SinCosProof
import Quadrature.Examples.CosineAccuracy

/-!
# Certifying the two cosine calls

FloatLib's `Model.cos` is an executable binary64 cosine. The kernel evaluates it
at the two stored two-point nodes, and a rational Taylor enclosure of the exact
cosine certifies the result to within `10⁻¹⁵`. This discharges the
`CosineContract` of `Examples/CosineAccuracy`, so the complete two-point program returns
one specific binary64 value whose error against `sin 1` is at most `0.00356`.
The manuscript claimed error at most `0.00224`, and the computed value's true
error is larger, so the claim is false. The accuracy statement concerns the two
stored nodes, which are the only inputs the program passes to the cosine.
-/

namespace Quadrature.Binary64

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics

/-- The value FloatLib's cosine returns at both stored two-point nodes, bits
`0x3fead02c771c35ed`. -/
def cosineValue : Value := Model.ofNatBits 0x3fead02c771c35ed

-- Kernel evaluation of FloatLib's executable cosine at one binary64 input.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- FloatLib's executable cosine at `rightNode` returns `cosineValue`, by kernel evaluation. -/
theorem cosine_right : Model.cos rightNode = cosineValue := by decide +kernel

-- Kernel evaluation of FloatLib's executable cosine at one binary64 input.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- FloatLib's executable cosine at `leftNode` returns `cosineValue`, by kernel evaluation. -/
theorem cosine_left : Model.cos leftNode = cosineValue := by decide +kernel

/-- `cosineValue` is a finite binary64 value. -/
theorem cosineValue_finite : Model.isFinite cosineValue = true := by decide

/-- `cosineValue` decodes to the dyadic `7547238789953005 · 2⁻⁵³`. -/
theorem cosineValue_decode :
    Model.toDyadic? cosineValue = some ⟨false, 7547238789953005, -53⟩ := by decide

/-- The real value of `cosineValue` is `7547238789953005 / 2⁵³`. -/
theorem cosineValue_toReal :
    Model.toReal cosineValue = (7547238789953005 / 9007199254740992 : ℝ) := by
  rw [Model.toReal_eq, cosineValue_decode]
  norm_num [Dyadic.toReal, Dyadic.signedSignificand]

/-- The executable cosine result is within `10⁻¹⁵` of the exact cosine at `rightNode`. A
degree-18 rational Taylor enclosure of the cosine at the node's exact rational value is
compared with the decoded result by kernel evaluation. -/
theorem cosineValue_error :
    |Model.toReal cosineValue - Real.cos (Model.toReal rightNode)| ≤
      (1 / 10 ^ 15 : ℝ) := by
  let q : ℚ := 1300077228592327 / 2251799813685248
  let v : ℚ := 7547238789953005 / 9007199254740992
  have hc := Enclosure.contains_cos q 18
  have hlo : v - 1 / 10 ^ 15 ≤ (Enclosure.cos q 18).lo := by decide +kernel
  have hhi : (Enclosure.cos q 18).hi ≤ v + 1 / 10 ^ 15 := by decide +kernel
  have hlo' : (v : ℝ) - 1 / 10 ^ 15 ≤ ((Enclosure.cos q 18).lo : ℝ) := by
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_pow,
      Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hlo
  have hhi' : ((Enclosure.cos q 18).hi : ℝ) ≤ (v : ℝ) + 1 / 10 ^ 15 := by
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_pow,
      Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hhi
  rw [cosineValue_toReal, rightNode_toReal, abs_le]
  norm_num [q, v] at hc hlo' hhi'
  constructor <;> linarith [hc.1, hc.2]

/-- FloatLib's `Model.cos` satisfies `CosineContract`: it is finite and within `10⁻¹⁵` of the
exact cosine at both stored nodes. The left node follows from the right one because cosine
is even. -/
theorem cosine_contract : CosineContract Model.cos := by
  intro x hx
  rcases hx with rfl | rfl
  · rw [cosine_left]
    refine ⟨cosineValue_finite, ?_⟩
    rw [leftNode_toReal, Real.cos_neg, ← rightNode_toReal]
    exact cosineValue_error
  · rw [cosine_right]
    exact ⟨cosineValue_finite, cosineValue_error⟩

/-- The complete two-point program with FloatLib's cosine returns `cosineValue`. After the two
cosine calls are rewritten, the kernel evaluates the remaining ten arithmetic operations. -/
theorem certified_program_value :
    integrate (testfun Model.cos) twoPointTerms = cosineValue := by
  simp only [integrate, twoPointTerms, List.map_cons, List.map_nil, testfun,
    cosine_left, cosine_right, List.foldl_cons, List.foldl_nil]
  decide +kernel

/-- The two-point program with FloatLib's cosine is finite and within `0.00356` of the integral
of the integrand over `[-1, 1]`. This bound is corrected from the manuscript's `0.00224`. -/
theorem certified_program_accuracy :
    Model.isFinite (integrate (testfun Model.cos) twoPointTerms) = true ∧
    |Model.toReal (integrate (testfun Model.cos) twoPointTerms) -
      ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤ (356 / 100000 : ℝ) :=
  two_point_program_accuracy Model.cos cosine_contract

/-- Records that the Appel–Bindel manuscript's claimed bound `0.00224` is false for the computed
two-point value, whose proved bound is `0.00356`. The manuscript claimed error at most
`0.00224`, and the computed value's true error against `sin 1` is larger, so the claim is
false. -/
theorem certified_program_draft_bound_false :
    ¬ |Model.toReal (integrate (testfun Model.cos) twoPointTerms) -
      ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤ (224 / 100000 : ℝ) :=
  paper_program_bound_false Model.cos cosine_contract

end Quadrature.Binary64
