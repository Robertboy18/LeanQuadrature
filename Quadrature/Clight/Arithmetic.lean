import CCLib.Cop
import Quadrature.Binary64.Constants

/-!
# FloatLib operations in the adapted Clight semantics

In this port `CC.Floats.Float` is definitionally FloatLib's binary64 `Model`,
so Clight's `double` operators `+ - * /` are `Model.add`, `Model.sub`,
`Model.mul` and `Model.div`. The four `_semantics` lemmas are `rfl` and record
that. The remaining lemmas are concrete checks, by `decide`, of comparison,
absolute value and conversion to 64-bit integers. They cover exceptional
values and the limits of the signed and unsigned ranges, computed without
native floating point.
-/

namespace Quadrature.Binary64.Clight

open FloatLib.Floats.Formats.BinaryInterchange

/-- Clight `double` addition is `Model.add`, by `rfl`. -/
theorem add_semantics (ce : CC.CompositeEnv) (m : CC.Mem) (x y : Value) :
    CC.Cop.semBinaryOperation ce .Oadd (.Vfloat x) CC.tdouble (.Vfloat y) CC.tdouble m =
      some (.Vfloat (Model.add x y)) := rfl

/-- Clight `double` multiplication is `Model.mul`, by `rfl`. -/
theorem mul_semantics (ce : CC.CompositeEnv) (m : CC.Mem) (x y : Value) :
    CC.Cop.semBinaryOperation ce .Omul (.Vfloat x) CC.tdouble (.Vfloat y) CC.tdouble m =
      some (.Vfloat (Model.mul x y)) := rfl

/-- Clight `double` subtraction is `Model.sub`, by `rfl`. -/
theorem sub_semantics (ce : CC.CompositeEnv) (m : CC.Mem) (x y : Value) :
    CC.Cop.semBinaryOperation ce .Osub (.Vfloat x) CC.tdouble (.Vfloat y) CC.tdouble m =
      some (.Vfloat (Model.sub x y)) := rfl

/-- Clight `double` division is `Model.div`, by `rfl`. -/
theorem div_semantics (ce : CC.CompositeEnv) (m : CC.Mem) (x y : Value) :
    CC.Cop.semBinaryOperation ce .Odiv (.Vfloat x) CC.tdouble (.Vfloat y) CC.tdouble m =
      some (.Vfloat (Model.div x y)) := rfl

/-- `+0.0 == -0.0` holds under Clight's `double` comparison. -/
theorem signed_zero_equal :
    CC.Floats.Float.cmp .Ceq (Model.ofNatBits 0) (Model.ofNatBits 0x8000000000000000) =
      true := by decide

/-- The absolute value of `-0.0` is `+0.0`, sign bit included. -/
theorem abs_negative_zero :
    CC.Floats.Float.abs (Model.ofNatBits 0x8000000000000000) = Model.ofNatBits 0 := by
  decide

/-- A NaN compares unequal to itself under `!=`. -/
theorem nan_not_equal :
    CC.Floats.Float.cmp .Cne (Model.ofNatBits 0x7ff8000000000001)
      (Model.ofNatBits 0x7ff8000000000001) = true := by decide

/-- A NaN is not less than zero: ordered comparisons with a NaN are false. -/
theorem nan_not_less :
    CC.Floats.Float.cmp .Clt (Model.ofNatBits 0x7ff8000000000001)
      (Model.ofNatBits 0) = false := by decide

/-- Converting a NaN to a signed 64-bit integer fails. -/
theorem nan_to_long_none :
    CC.Floats.Float.toLong (Model.ofNatBits 0x7ff8000000000001) = none := by decide

/-- Converting `+∞` to a signed 64-bit integer fails. -/
theorem infinity_to_long_none :
    CC.Floats.Float.toLong (Model.ofNatBits 0x7ff0000000000000) = none := by decide

/-- `2^63` is outside the range of signed 64-bit integers, so the conversion fails. -/
theorem two_pow_63_to_long_none :
    CC.Floats.Float.toLong (Model.ofNatBits 0x43e0000000000000) = none := by decide

/-- `2^63` converts to the unsigned 64-bit integer `9223372036854775808`. -/
theorem two_pow_63_to_longu :
    CC.Floats.Float.toLongu (Model.ofNatBits 0x43e0000000000000) =
      some (CC.Integers.Int64.repr 9223372036854775808) := by decide

/-- `2^64` is outside the unsigned 64-bit range, so the conversion fails. -/
theorem two_pow_64_to_longu_none :
    CC.Floats.Float.toLongu (Model.ofNatBits 0x43f0000000000000) = none := by decide

/-- `-1.0` converts to no unsigned 64-bit integer. -/
theorem negative_one_to_longu_none :
    CC.Floats.Float.toLongu (Model.ofNatBits 0xbff0000000000000) = none := by decide

/-- `-0.5` converts to unsigned zero: the range check applies to the truncated integer. -/
theorem negative_half_to_longu :
    CC.Floats.Float.toLongu (Model.ofNatBits 0xbfe0000000000000) =
      some (CC.Integers.Int64.repr 0) := by decide

end Quadrature.Binary64.Clight
