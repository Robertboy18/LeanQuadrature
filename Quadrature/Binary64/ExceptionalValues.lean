import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog

/-!
# Exceptional binary64 results

FloatLib returns the following six results, each by kernel evaluation: the sum
and the product of `quietNaN` and `signalingNaN` are `0x7ff8000000000002`, the
sum of opposite infinities and the product of infinity and zero are the
canonical NaN `0x7ff8000000000000`, `0/0` is `0x7ff8000000000000`, and
`1 − quietNaN` is `0xfff8000000000001`. For the same inputs CompCert makes
different NaN payload and sign choices, and those values are certified in the
companion Rocq proofs in `compcert/ExceptionalValues.v`.
-/

namespace Quadrature.Binary64.ExceptionalValues

open FloatLib.Floats.Formats.BinaryInterchange

/-- FloatLib's binary64 model. -/
abbrev Value := Model FloatFormat.binary64

/-- A quiet NaN with payload 1, bits `0x7ff8000000000001`. -/
def quietNaN : Value := Model.ofNatBits 0x7ff8000000000001
/-- A signaling NaN with payload 2, bits `0x7ff0000000000002`. -/
def signalingNaN : Value := Model.ofNatBits 0x7ff0000000000002
/-- Positive infinity, bits `0x7ff0000000000000`. -/
def positiveInfinity : Value := Model.ofNatBits 0x7ff0000000000000
/-- Negative infinity, bits `0xfff0000000000000`. -/
def negativeInfinity : Value := Model.ofNatBits 0xfff0000000000000
/-- Positive zero, all bits clear. -/
def positiveZero : Value := Model.ofNatBits 0
/-- The binary64 value `1.0`, bits `0x3ff0000000000000`. -/
def positiveOne : Value := Model.ofNatBits 0x3ff0000000000000

/-- Adding a quiet NaN to a signaling NaN returns the quieted payload of the signaling right
operand, `0x7ff8000000000002`. -/
theorem mixed_nan_add :
    Model.toNatBits (Model.add quietNaN signalingNaN) = 0x7ff8000000000002 := by
  decide +kernel

/-- Multiplying a quiet NaN by a signaling NaN uses the same signaling-first selection and
returns `0x7ff8000000000002`. -/
theorem mixed_nan_mul :
    Model.toNatBits (Model.mul quietNaN signalingNaN) = 0x7ff8000000000002 := by
  decide +kernel

/-- Adding opposite infinities produces the positive canonical NaN `0x7ff8000000000000`. -/
theorem opposite_infinities_add :
    Model.toNatBits (Model.add positiveInfinity negativeInfinity) = 0x7ff8000000000000 := by
  decide +kernel

/-- The invalid product of infinity and zero produces the positive canonical NaN
`0x7ff8000000000000`. -/
theorem infinity_zero_mul :
    Model.toNatBits (Model.mul positiveInfinity positiveZero) = 0x7ff8000000000000 := by
  decide +kernel

/-- Dividing zero by zero produces the positive canonical NaN `0x7ff8000000000000`, so finite
operands alone do not exclude an invalid operation. -/
theorem zero_div_zero :
    Model.toNatBits (Model.div positiveZero positiveZero) = 0x7ff8000000000000 := by
  decide +kernel

/-- Subtracting a quiet NaN from `1.0` returns `0xfff8000000000001`: the right operand is negated
before its NaN is propagated, so the sign bit flips. -/
theorem finite_sub_nan :
    Model.toNatBits (Model.sub positiveOne quietNaN) = 0xfff8000000000001 := by
  decide +kernel

end Quadrature.Binary64.ExceptionalValues
