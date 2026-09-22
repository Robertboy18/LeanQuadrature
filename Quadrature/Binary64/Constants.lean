import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
import FloatLib.Floats.Formats.BinaryInterchange.Model.RealSemantics
import Quadrature.Examples.TwoPointCosine

/-!
# Binary64 constants from the original C program

`leftNode` and `rightNode` are the bit patterns `0xbfe279a74590331c` and
`0x3fe279a74590331c` that the original C program stores in its two-point table
for the nodes `∓1/√3`. The theorems below decode them with FloatLib to the
dyadics `∓1300077228592327 / 2⁵¹` and prove that each lies within `10⁻¹⁶` of the
exact node. `one`, `half`, and `zero` are the other constants that the callback
and the loop use.
-/

namespace Quadrature.Binary64

open FloatLib.Floats.Formats.BinaryInterchange

/-- FloatLib's binary64 model, the type of every floating-point value in this development. -/
abbrev Value := Model FloatFormat.binary64

/-- The stored two-point node for `-1/√3`, bit pattern `0xbfe279a74590331c`. -/
def leftNode : Value := Model.ofNatBits 0xbfe279a74590331c
/-- The stored two-point node for `+1/√3`, bit pattern `0x3fe279a74590331c`. -/
def rightNode : Value := Model.ofNatBits 0x3fe279a74590331c
/-- The binary64 value `1.0`, used as both two-point weights and in the callback's `1 - x`. -/
def one : Value := Model.ofNatBits 0x3ff0000000000000
/-- The binary64 value `0.5`, the leading factor of the callback. -/
def half : Value := Model.ofNatBits 0x3fe0000000000000
/-- Positive zero, the initial accumulator of the loop. -/
def zero : Value := Model.ofNatBits 0

/-- `rightNode` is a finite binary64 value. -/
theorem rightNode_finite : Model.isFinite rightNode = true := by decide
/-- `leftNode` is a finite binary64 value. -/
theorem leftNode_finite : Model.isFinite leftNode = true := by decide
/-- `one` is a finite binary64 value. -/
theorem one_finite : Model.isFinite one = true := by decide
/-- `half` is a finite binary64 value. -/
theorem half_finite : Model.isFinite half = true := by decide
/-- `zero` is a finite binary64 value. -/
theorem zero_finite : Model.isFinite zero = true := by decide

/-- `rightNode` decodes to the positive dyadic `5200308914369308 · 2⁻⁵³`. -/
theorem rightNode_decode :
    Model.toDyadic? rightNode = some ⟨false, 5200308914369308, -53⟩ := by decide

/-- `leftNode` decodes to the negative dyadic `-5200308914369308 · 2⁻⁵³`. -/
theorem leftNode_decode :
    Model.toDyadic? leftNode = some ⟨true, 5200308914369308, -53⟩ := by decide

/-- The real value of `rightNode` is `1300077228592327 / 2⁵¹`. -/
theorem rightNode_toReal :
    Model.toReal rightNode = (1300077228592327 / 2251799813685248 : ℝ) := by
  rw [Model.toReal_eq, rightNode_decode]
  norm_num [FloatLib.Numerics.Dyadic.toReal, FloatLib.Numerics.Dyadic.signedSignificand]

/-- The real value of `leftNode` is `-1300077228592327 / 2⁵¹`. -/
theorem leftNode_toReal :
    Model.toReal leftNode = -(1300077228592327 / 2251799813685248 : ℝ) := by
  rw [Model.toReal_eq, leftNode_decode]
  norm_num [FloatLib.Numerics.Dyadic.toReal, FloatLib.Numerics.Dyadic.signedSignificand]

/-- The stored right node is within `10⁻¹⁶` of `1/√3`. The proof squares both sides of the
rational bounds and closes with `nlinarith`. -/
theorem rightNode_error :
    |Model.toReal rightNode - 1 / Real.sqrt 3| ≤ (1 / 10 ^ 16 : ℝ) := by
  rw [rightNode_toReal, abs_le]
  have hs : (1 / Real.sqrt (3 : ℝ)) ^ 2 = 1 / 3 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hp : 0 ≤ 1 / Real.sqrt (3 : ℝ) := by positivity
  constructor <;> nlinarith

/-- The stored left node is within `10⁻¹⁶` of `-1/√3`, by symmetry from `rightNode_error`. -/
theorem leftNode_error :
    |Model.toReal leftNode - -(1 / Real.sqrt 3)| ≤ (1 / 10 ^ 16 : ℝ) := by
  rw [leftNode_toReal, ← rightNode_toReal, neg_sub_neg, abs_sub_comm]
  exact rightNode_error

end Quadrature.Binary64
