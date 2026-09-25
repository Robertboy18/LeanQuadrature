import Quadrature.Binary64.Constants
import PDE.Symbolic.Continuum.Quadrature.Legendre.Basic

/-!
# Binary64 constants for the one-, three-, and four-point rules

These bit patterns are the entries of the original C program's tables for the
one-, three-, and four-point rules, together with the literal of the Rocq model
for the three-point outer weight. The exact rational decoding below shows that
the C literal `0.555555555555556` and the model literal `0.5555555555555556`
have different encodings, with no floating-point computation inside the proof.
-/

namespace Quadrature.Binary64

open FloatLib.Floats.Formats.BinaryInterchange
open PDE.Symbolic.Continuum

/-- The binary64 value `2.0`, the weight of the one-point rule. -/
def two : Value := Model.ofNatBits 0x4000000000000000
/-- The positive outer node `√(3/5)` of the three-point rule, bits `0x3fe8c97ef43f7248`. -/
def threeNode64 : Value := Model.ofNatBits 0x3fe8c97ef43f7248
/-- The positive inner node of the four-point rule, bits `0x3fd5c23fd9dd3dfc`. -/
def fourInner64 : Value := Model.ofNatBits 0x3fd5c23fd9dd3dfc
/-- The positive outer node of the four-point rule, bits `0x3feb8e6dbcf63985`. -/
def fourOuter64 : Value := Model.ofNatBits 0x3feb8e6dbcf63985
/-- The outer weight of the three-point rule as the original C program stores it: the literal
`0.555555555555556`, bits `0x3fe1c71c71c71c76`. -/
def threeOuterWeight : Value := Model.ofNatBits 0x3fe1c71c71c71c76
/-- The middle weight `8/9` of the three-point rule, bits `0x3fec71c71c71c71d`. -/
def threeMiddleWeight : Value := Model.ofNatBits 0x3fec71c71c71c71d
/-- The inner weight `(18 + √30)/36` of the four-point rule, bits `0x3fe4de5f840c24cb`. -/
def fourInnerWeight : Value := Model.ofNatBits 0x3fe4de5f840c24cb
/-- The outer weight `(18 − √30)/36` of the four-point rule, bits `0x3fd64340f7e7b66b`. -/
def fourOuterWeight : Value := Model.ofNatBits 0x3fd64340f7e7b66b
/-- The Rocq model's literal `0.5555555555555556` for the three-point outer weight, bits
`0x3fe1c71c71c71c72`. The C literal `0.555555555555556` has bits `0x3fe1c71c71c71c76`, which is
`19/(9·2⁵²) ≈ 4.69·10⁻¹⁶` from `5/9`. -/
def modelThreeOuterWeight : Value := Model.ofNatBits 0x3fe1c71c71c71c72
/-- The negative outer node of the three-point rule, the negation of `threeNode64`. -/
def negativeThreeNode64 : Value := Model.ofNatBits 0xbfe8c97ef43f7248
/-- The negative inner node of the four-point rule, the negation of `fourInner64`. -/
def negativeFourInner64 : Value := Model.ofNatBits 0xbfd5c23fd9dd3dfc
/-- The negative outer node of the four-point rule, the negation of `fourOuter64`. -/
def negativeFourOuter64 : Value := Model.ofNatBits 0xbfeb8e6dbcf63985

/-- The eight positive constants are finite binary64 values. -/
theorem additional_constants_finite :
    Model.isFinite two = true ∧
    Model.isFinite threeNode64 = true ∧
    Model.isFinite fourInner64 = true ∧
    Model.isFinite fourOuter64 = true ∧
    Model.isFinite threeOuterWeight = true ∧
    Model.isFinite threeMiddleWeight = true ∧
    Model.isFinite fourInnerWeight = true ∧
    Model.isFinite fourOuterWeight = true := by decide

/-- The three negated nodes are finite binary64 values. -/
theorem negative_constants_finite :
    Model.isFinite negativeThreeNode64 = true ∧
    Model.isFinite negativeFourInner64 = true ∧
    Model.isFinite negativeFourOuter64 = true := by decide

/-- The real value of `two` is 2. -/
theorem two_toReal : Model.toReal two = 2 := by
  have h : Model.toDyadic? two = some ⟨false, 4503599627370496, -51⟩ := by decide
  rw [Model.toReal_eq, h]
  norm_num [FloatLib.Numerics.Dyadic.toReal, FloatLib.Numerics.Dyadic.signedSignificand]

/-- The real value of `one` is 1. -/
theorem one_toReal : Model.toReal one = 1 := by
  have h : Model.toDyadic? one = some ⟨false, 4503599627370496, -52⟩ := by decide
  rw [Model.toReal_eq, h]
  norm_num [FloatLib.Numerics.Dyadic.toReal, FloatLib.Numerics.Dyadic.signedSignificand]

/-- The real value of `half` is 1/2. -/
theorem half_toReal : Model.toReal half = (1 / 2 : ℝ) := by
  have h : Model.toDyadic? half = some ⟨false, 4503599627370496, -53⟩ := by decide
  rw [Model.toReal_eq, h]
  norm_num [FloatLib.Numerics.Dyadic.toReal, FloatLib.Numerics.Dyadic.signedSignificand]

/-- The real value of `threeNode64` is `872118317739593 / 2⁵⁰`. -/
theorem threeNode64_toReal :
    Model.toReal threeNode64 = (872118317739593 / 1125899906842624 : ℝ) := by
  have h : Model.toDyadic? threeNode64 = some ⟨false, 6976946541916744, -53⟩ := by decide
  rw [Model.toReal_eq, h]
  norm_num [FloatLib.Numerics.Dyadic.toReal, FloatLib.Numerics.Dyadic.signedSignificand]

/-- The real value of `fourInner64` is `1531138501201791 / 2⁵²`. -/
theorem fourInner64_toReal :
    Model.toReal fourInner64 = (1531138501201791 / 4503599627370496 : ℝ) := by
  have h : Model.toDyadic? fourInner64 = some ⟨false, 6124554004807164, -54⟩ := by decide
  rw [Model.toReal_eq, h]
  norm_num [FloatLib.Numerics.Dyadic.toReal, FloatLib.Numerics.Dyadic.signedSignificand]

/-- The real value of `fourOuter64` is `7756426344020357 / 2⁵³`. -/
theorem fourOuter64_toReal :
    Model.toReal fourOuter64 = (7756426344020357 / 9007199254740992 : ℝ) := by
  have h : Model.toDyadic? fourOuter64 = some ⟨false, 7756426344020357, -53⟩ := by decide
  rw [Model.toReal_eq, h]
  norm_num [FloatLib.Numerics.Dyadic.toReal, FloatLib.Numerics.Dyadic.signedSignificand]

/-- The real value of `negativeThreeNode64` is the negation of that of `threeNode64`. -/
theorem negativeThreeNode64_toReal :
    Model.toReal negativeThreeNode64 = -Model.toReal threeNode64 := by
  have h : Model.toDyadic? negativeThreeNode64 = some ⟨true, 6976946541916744, -53⟩ :=
    by decide
  rw [threeNode64_toReal, Model.toReal_eq, h]
  norm_num [FloatLib.Numerics.Dyadic.toReal, FloatLib.Numerics.Dyadic.signedSignificand]

/-- The real value of `negativeFourInner64` is the negation of that of `fourInner64`. -/
theorem negativeFourInner64_toReal :
    Model.toReal negativeFourInner64 = -Model.toReal fourInner64 := by
  have h : Model.toDyadic? negativeFourInner64 = some ⟨true, 6124554004807164, -54⟩ :=
    by decide
  rw [fourInner64_toReal, Model.toReal_eq, h]
  norm_num [FloatLib.Numerics.Dyadic.toReal, FloatLib.Numerics.Dyadic.signedSignificand]

/-- The real value of `negativeFourOuter64` is the negation of that of `fourOuter64`. -/
theorem negativeFourOuter64_toReal :
    Model.toReal negativeFourOuter64 = -Model.toReal fourOuter64 := by
  have h : Model.toDyadic? negativeFourOuter64 = some ⟨true, 7756426344020357, -53⟩ :=
    by decide
  rw [fourOuter64_toReal, Model.toReal_eq, h]
  norm_num [FloatLib.Numerics.Dyadic.toReal, FloatLib.Numerics.Dyadic.signedSignificand]

/-- The real value of `threeOuterWeight` is `2501999792983611 / 2⁵²`. -/
theorem threeOuterWeight_toReal :
    Model.toReal threeOuterWeight = (2501999792983611 / 4503599627370496 : ℝ) := by
  have h : Model.toDyadic? threeOuterWeight = some ⟨false, 5003999585967222, -53⟩ := by decide
  rw [Model.toReal_eq, h]
  norm_num [FloatLib.Numerics.Dyadic.toReal, FloatLib.Numerics.Dyadic.signedSignificand]

/-- The real value of `threeMiddleWeight` is `8006399337547549 / 2⁵³`. -/
theorem threeMiddleWeight_toReal :
    Model.toReal threeMiddleWeight = (8006399337547549 / 9007199254740992 : ℝ) := by
  have h : Model.toDyadic? threeMiddleWeight = some ⟨false, 8006399337547549, -53⟩ := by decide
  rw [Model.toReal_eq, h]
  norm_num [FloatLib.Numerics.Dyadic.toReal, FloatLib.Numerics.Dyadic.signedSignificand]

/-- The real value of `fourInnerWeight` is `5874001352860875 / 2⁵³`. -/
theorem fourInnerWeight_toReal :
    Model.toReal fourInnerWeight = (5874001352860875 / 9007199254740992 : ℝ) := by
  have h : Model.toDyadic? fourInnerWeight = some ⟨false, 5874001352860875, -53⟩ := by decide
  rw [Model.toReal_eq, h]
  norm_num [FloatLib.Numerics.Dyadic.toReal, FloatLib.Numerics.Dyadic.signedSignificand]

/-- The real value of `fourOuterWeight` is `6266395803760235 / 2⁵⁴`. -/
theorem fourOuterWeight_toReal :
    Model.toReal fourOuterWeight = (6266395803760235 / 18014398509481984 : ℝ) := by
  have h : Model.toDyadic? fourOuterWeight = some ⟨false, 6266395803760235, -54⟩ := by decide
  rw [Model.toReal_eq, h]
  norm_num [FloatLib.Numerics.Dyadic.toReal, FloatLib.Numerics.Dyadic.signedSignificand]

/-- The stored three-point outer node is within `10⁻¹⁶` of `√(3/5)`. The proof squares, using
`Legendre.threeNode_sq`. -/
theorem threeNode64_error :
    |Model.toReal threeNode64 - Legendre.threeNode| ≤ (1 / 10 ^ 16 : ℝ) := by
  rw [threeNode64_toReal, abs_le]
  constructor <;> nlinarith [Legendre.threeNode_sq, Legendre.threeNode_mem.1]

/-- `√30` lies in `[5.477225575051661134, 5.477225575051661135]`, an interval of width `10⁻¹⁸`
that suffices for the four-point node and weight bounds. -/
theorem fourRadical_tight :
    (5477225575051661134 / 10 ^ 18 : ℝ) ≤ Legendre.fourRadical ∧
    Legendre.fourRadical ≤ (5477225575051661135 / 10 ^ 18 : ℝ) := by
  constructor <;> nlinarith [Legendre.fourRadical_sq, Legendre.fourRadical_bounds.1]

/-- The stored four-point inner node is within `10⁻¹⁶` of `Legendre.fourInner`. -/
theorem fourInner64_error :
    |Model.toReal fourInner64 - Legendre.fourInner| ≤ (1 / 10 ^ 16 : ℝ) := by
  rw [fourInner64_toReal, abs_le]
  constructor <;> nlinarith [Legendre.fourInner_sq, Legendre.fourInner_mem.1,
    fourRadical_tight.1, fourRadical_tight.2]

/-- The stored four-point outer node is within `10⁻¹⁶` of `Legendre.fourOuter`. -/
theorem fourOuter64_error :
    |Model.toReal fourOuter64 - Legendre.fourOuter| ≤ (1 / 10 ^ 16 : ℝ) := by
  rw [fourOuter64_toReal, abs_le]
  constructor <;> nlinarith [Legendre.fourOuter_sq, Legendre.fourOuter_mem.1,
    fourRadical_tight.1, fourRadical_tight.2]

/-- The stored negative three-point node is within `10⁻¹⁶` of `-√(3/5)`, by symmetry. -/
theorem negativeThreeNode64_error :
    |Model.toReal negativeThreeNode64 - -Legendre.threeNode| ≤ (1 / 10 ^ 16 : ℝ) := by
  simpa only [negativeThreeNode64_toReal, neg_sub_neg, abs_sub_comm]
    using threeNode64_error

/-- The stored negative four-point inner node is within `10⁻¹⁶` of `-Legendre.fourInner`. -/
theorem negativeFourInner64_error :
    |Model.toReal negativeFourInner64 - -Legendre.fourInner| ≤ (1 / 10 ^ 16 : ℝ) := by
  simpa only [negativeFourInner64_toReal, neg_sub_neg, abs_sub_comm]
    using fourInner64_error

/-- The stored negative four-point outer node is within `10⁻¹⁶` of `-Legendre.fourOuter`. -/
theorem negativeFourOuter64_error :
    |Model.toReal negativeFourOuter64 - -Legendre.fourOuter| ≤ (1 / 10 ^ 16 : ℝ) := by
  simpa only [negativeFourOuter64_toReal, neg_sub_neg, abs_sub_comm]
    using fourOuter64_error

/-- The stored three-point outer weight is within `5·10⁻¹⁶` of `5/9`. Its distance is
`19/(9·2⁵²) ≈ 4.69·10⁻¹⁶`, so a tolerance of `10⁻¹⁶` would fail. -/
theorem threeOuterWeight_error :
    |Model.toReal threeOuterWeight - 5 / 9| ≤ (5 / 10 ^ 16 : ℝ) := by
  rw [threeOuterWeight_toReal]
  norm_num

/-- The stored three-point middle weight is within `10⁻¹⁶` of `8/9`. -/
theorem threeMiddleWeight_error :
    |Model.toReal threeMiddleWeight - 8 / 9| ≤ (1 / 10 ^ 16 : ℝ) := by
  rw [threeMiddleWeight_toReal]
  norm_num

/-- The stored four-point inner weight is within `10⁻¹⁶` of `(18 + √30)/36`. -/
theorem fourInnerWeight_error :
    |Model.toReal fourInnerWeight - (18 + Legendre.fourRadical) / 36| ≤
      (1 / 10 ^ 16 : ℝ) := by
  rw [fourInnerWeight_toReal, abs_le]
  constructor <;> linarith [fourRadical_tight.1, fourRadical_tight.2]

/-- The stored four-point outer weight is within `10⁻¹⁶` of `(18 − √30)/36`. -/
theorem fourOuterWeight_error :
    |Model.toReal fourOuterWeight - (18 - Legendre.fourRadical) / 36| ≤
      (1 / 10 ^ 16 : ℝ) := by
  rw [fourOuterWeight_toReal, abs_le]
  constructor <;> linarith [fourRadical_tight.1, fourRadical_tight.2]

/-- Records that the Appel–Bindel manuscript's absolute weight tolerance `2⁻⁵³ ≈ 1.11·10⁻¹⁶`
fails for the stored three-point outer weight, whose distance from `5/9` is
`19/(9·2⁵²) ≈ 4.69·10⁻¹⁶` and whose proved tolerance is `5·10⁻¹⁶`. That tolerance is one ULP at
`5/9`, so a correctly rounded literal would have met it. -/
theorem threeOuterWeight_exceeds_draft_tolerance :
    ¬ |Model.toReal threeOuterWeight - 5 / 9| ≤ (1 / 2 ^ 53 : ℝ) := by
  rw [threeOuterWeight_toReal]
  norm_num

/-- Records that the C literal `0.555555555555556` (bits `0x3fe1c71c71c71c76`) and the Rocq
model literal `0.5555555555555556` (bits `0x3fe1c71c71c71c72`) are different binary64 values. -/
theorem threeOuterWeight_ne_model : threeOuterWeight ≠ modelThreeOuterWeight := by decide

end Quadrature.Binary64
