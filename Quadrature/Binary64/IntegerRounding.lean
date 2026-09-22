import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.RoundingSemantics.RoundedReal

/-!
# Integer specifications of binary rounding

Quotient, remainder, parity, and exponent alignment give an executable
specification for rounding a signed dyadic to a binary format. The theorems
identify this specification with FloatLib's real rounding function
`Model.roundAt`, including zero and underflow. Exact addition, multiplication,
and equality of coefficient-exponent pairs are defined here as well.
-/

namespace Quadrature.IntegerRounding

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics
open FloatLib.Floats.Formats.Flocq

/-- For a nonzero natural `m`, FloatLib's `floorLog2 m 1` is `Nat.log2 m`. -/
theorem floorLog2_one (mantissa : Nat) (hm : mantissa ≠ 0) :
    RationalBinary.floorLog2 mantissa 1 = (mantissa.log2 : Int) := by
  have hl : 2 ^ mantissa.log2 ≤ mantissa := (Nat.le_log2 hm).mp le_rfl
  have hu : mantissa < 2 ^ (mantissa.log2 + 1) :=
    (Nat.log2_lt hm).mp (Nat.lt_succ_self _)
  simp [RationalBinary.floorLog2, RationalBinary.lessThanPowerOfTwo,
    RationalBinary.atLeastPowerOfTwo, show Nat.log2 1 = 0 from rfl,
    Nat.shiftLeft_eq, not_lt.mpr hl]
  change decide (2 ^ (mantissa.log2 + 1) ≤ mantissa) = false
  simp [not_le.mpr hu]

/-- Nearest-even integer division: the Euclidean quotient, raised by one when the remainder
exceeds half the divisor, and rounded to the even neighbour on a tie. -/
def quotientEven (numerator denominator : Int) : Int :=
  let quotient := numerator / denominator
  let remainder := numerator % denominator
  if 2 * remainder < denominator then quotient
  else if denominator < 2 * remainder then quotient + 1
  else if quotient % 2 = 0 then quotient else quotient + 1

/-- `quotientEven` on natural inputs agrees with FloatLib's `roundQuotientEven`. -/
theorem quotientEven_natCast (numerator denominator : Nat) :
    quotientEven numerator denominator =
      (roundQuotientEven numerator denominator : Int) := by
  simp [quotientEven, roundQuotientEven, ← Int.natCast_ediv, ← Int.natCast_emod,
    -Int.natCast_mod]
  split_ifs <;> omega

/-- Move a binary scale into an integer numerator or positive denominator. -/
def scale (mantissa shift : Int) : Int × Int :=
  if 0 ≤ shift then (mantissa * 2 ^ shift.toNat, 1)
  else (mantissa, 2 ^ (-shift).toNat)

/-- `scale` on a natural mantissa agrees with FloatLib's `scaleByPowerOfTwo`. -/
theorem scale_natCast (mantissa : Nat) (shift : Int) :
    scale mantissa shift =
      (((RationalBinary.scaleByPowerOfTwo mantissa 1 shift).1 : Int),
       ((RationalBinary.scaleByPowerOfTwo mantissa 1 shift).2 : Int)) := by
  cases shift with
  | ofNat shift =>
      simp [scale, RationalBinary.scaleByPowerOfTwo, Nat.shiftLeft_eq]
  | negSucc shift =>
      simp [scale, RationalBinary.scaleByPowerOfTwo, Nat.shiftLeft_eq, Int.negSucc_eq]
      omega

/-- Round the positive dyadic `mantissa · 2^exponent` to the format with integer arithmetic
only: choose the target exponent with `fexpOf`, rescale, and take the nearest-even quotient. -/
def roundUnsigned (fmt : FloatFormat) (mantissa : Nat) (exponent : Int) : Int × Int :=
  let target := Model.fexpOf fmt ((mantissa.log2 : Int) + exponent + 1)
  let scaled := scale mantissa (exponent - target)
  (quotientEven scaled.1 scaled.2, target)

/-- `roundUnsigned` unfolds to FloatLib's scaling and nearest-even quotient functions. -/
theorem roundUnsigned_eq_floatlib (fmt : FloatFormat) (mantissa : Nat) (exponent : Int) :
    roundUnsigned fmt mantissa exponent =
      let target := Model.fexpOf fmt ((mantissa.log2 : Int) + exponent + 1)
      let scaled := RationalBinary.scaleByPowerOfTwo mantissa 1 (exponent - target)
      ((roundQuotientEven scaled.1 scaled.2 : Int), target) := by
  simp only [roundUnsigned, scale_natCast, quotientEven_natCast]

/-- The real value `c · 2^e` of a coefficient-exponent pair `(c, e)`. -/
noncomputable def toReal (value : Int × Int) : ℝ :=
  (value.1 : ℝ) * (2 : ℝ) ^ value.2

/-- For a nonzero mantissa, `Model.roundAt` of `mantissa · 2^exponent` is the real value of
`roundUnsigned`. -/
theorem roundUnsigned_real (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hm : mantissa ≠ 0) :
    Model.roundAt fmt ((mantissa : ℝ) * (2 : ℝ) ^ exponent) =
      toReal (roundUnsigned fmt mantissa exponent) := by
  have h := Model.roundAt_scaledRat_eq fmt false mantissa 1 exponent hm (by decide)
  rw [floorLog2_one mantissa hm] at h
  rw [roundUnsigned_eq_floatlib]
  simpa [toReal, Model.signedScaledRatToReal,
    Model.scaledRatToReal, bpow, binaryRadix, Radix.toReal] using h

/-- The binary64 exponent function is `max (magnitude − 53) (−1074)`, by unfolding. -/
theorem binary64_exponent (magnitude : Int) :
    Model.fexpOf FloatFormat.binary64 magnitude = max (magnitude - 53) (-1074) := by
  rfl

/-- Round a signed pair: zero is canonicalized to `(0, 0)`, otherwise the magnitude is rounded
and the sign restored. Callers keep the sign of a zero in a separate Boolean. -/
def roundSigned (fmt : FloatFormat) (value : Int × Int) : Int × Int :=
  if value.1 = 0 then (0, 0)
  else
    let result := roundUnsigned fmt value.1.natAbs value.2
    (if value.1 < 0 then -result.1 else result.1, result.2)

/-- `Model.roundAt` of the real value of a signed pair is the real value of `roundSigned`. -/
theorem roundSigned_real (fmt : FloatFormat) (value : Int × Int) :
    Model.roundAt fmt (toReal value) = toReal (roundSigned fmt value) := by
  rcases value with ⟨mantissa, exponent⟩
  by_cases hm : mantissa = 0
  · simp [roundSigned, toReal, hm]
  have hn : mantissa.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hm
  have hr := roundUnsigned_real fmt mantissa.natAbs exponent hn
  by_cases hs : mantissa < 0
  · have ha : (mantissa.natAbs : Int) = -mantissa := by
      rw [Int.natCast_natAbs, abs_of_neg hs]
    have har : (mantissa.natAbs : ℝ) = -(mantissa : ℝ) := by
      simpa only [Int.cast_natCast, Int.cast_neg] using
        congrArg (fun z : Int ↦ (z : ℝ)) ha
    simpa [roundSigned, toReal, hm, hs, har, neg_mul, Model.roundAt_neg] using
      congrArg Neg.neg hr
  · have ha : (mantissa.natAbs : Int) = mantissa := by
      rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]
    have har : (mantissa.natAbs : ℝ) = (mantissa : ℝ) := by
      simpa only [Int.cast_natCast] using congrArg (fun z : Int ↦ (z : ℝ)) ha
    simpa [roundSigned, toReal, hm, hs, har] using hr

/-- Move a signed coefficient to a no-larger exponent without rounding. -/
def align (mantissa exponent target : Int) : Int :=
  mantissa * 2 ^ (exponent - target).toNat

/-- Alignment to a smaller or equal exponent preserves the real value. -/
theorem align_real (mantissa exponent target : Int) (ht : target ≤ exponent) :
    (align mantissa exponent target : ℝ) * (2 : ℝ) ^ target =
      (mantissa : ℝ) * (2 : ℝ) ^ exponent := by
  have he : ((exponent - target).toNat : Int) = exponent - target :=
    Int.toNat_of_nonneg (by omega)
  simp only [align, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  rw [← zpow_natCast, he, mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 2
  omega

/-- Exact addition of two pairs after aligning both to the smaller exponent. -/
def add (x y : Int × Int) : Int × Int :=
  let exponent := min x.2 y.2
  (align x.1 x.2 exponent + align y.1 y.2 exponent, exponent)

/-- Exact multiplication of two pairs: multiply the coefficients and add the exponents. -/
def mul (x y : Int × Int) : Int × Int :=
  (x.1 * y.1, x.2 + y.2)

/-- `add` is exact: its real value is the sum of the real values. -/
theorem add_real (x y : Int × Int) : toReal (add x y) = toReal x + toReal y := by
  simp only [add, toReal, Int.cast_add, add_mul]
  rw [align_real _ _ _ (min_le_left _ _), align_real _ _ _ (min_le_right _ _)]

/-- `mul` is exact: its real value is the product of the real values. -/
theorem mul_real (x y : Int × Int) : toReal (mul x y) = toReal x * toReal y := by
  simp only [mul, toReal, Int.cast_mul, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-- Two pairs are `Equal` when their coefficients agree after alignment to the smaller exponent.
This is an integer-only statement of equality of real values. -/
def Equal (x y : Int × Int) : Prop :=
  align x.1 x.2 (min x.2 y.2) = align y.1 y.2 (min x.2 y.2)

/-- `Equal x y` holds exactly when the real values of x and y agree. -/
theorem equal_iff_real (x y : Int × Int) : Equal x y ↔ toReal x = toReal y := by
  have hx := align_real x.1 x.2 (min x.2 y.2) (min_le_left _ _)
  have hy := align_real y.1 y.2 (min x.2 y.2) (min_le_right _ _)
  unfold toReal
  rw [← hx, ← hy, mul_left_inj' (zpow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))]
  exact_mod_cast (Iff.rfl : Equal x y ↔ Equal x y)

/-- The real value of a pair is zero exactly when its coefficient is zero. -/
theorem toReal_eq_zero (value : Int × Int) : toReal value = 0 ↔ value.1 = 0 := by
  simp [toReal, zpow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)]

/-- The real value of a pair is negative exactly when its coefficient is negative. -/
theorem toReal_neg (value : Int × Int) : toReal value < 0 ↔ value.1 < 0 := by
  unfold toReal
  have hp : (0 : ℝ) < 2 ^ value.2 := zpow_pos (by norm_num) _
  constructor
  · intro h
    have hr : (value.1 : ℝ) < 0 := by nlinarith
    exact_mod_cast hr
  · intro h
    have hr : (value.1 : ℝ) < 0 := by exact_mod_cast h
    exact mul_neg_of_neg_of_pos hr hp

end Quadrature.IntegerRounding
