import Quadrature.Binary64.FiniteRepresentation
import Quadrature.Binary64.IntegerRounding

/-!
# Integer semantics of finite FloatLib quadrature

Under the range budget the loop result is the unique finite binary64 value whose
observation equals an integer recurrence. The recurrence works on a signed
coefficient, an exponent, and a sign bit, and it rounds with the integer
algorithm of `IntegerRounding`. Consequently the specification of the loop
result, including its zero sign, mentions only integers and Booleans.
-/

namespace Quadrature.Binary64.FiniteInteger

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics

/-- The signed significand and exponent of a finite value, with nonfinite inputs decoding to
`(0, 0)`. -/
def decode {fmt : FloatFormat} (x : Model fmt) : Int × Int :=
  match Model.toDyadic? x with
  | some d => (d.signedSignificand, d.exponent)
  | none => (0, 0)

/-- The real value of `decode x` under `IntegerRounding.toReal` is `Model.toReal x`. -/
theorem decode_real {fmt : FloatFormat} (x : Model fmt) :
    IntegerRounding.toReal (decode x) = Model.toReal x := by
  cases h : Model.toDyadic? x <;>
    simp [decode, Model.toReal_eq, h, IntegerRounding.toReal,
      FloatLib.Numerics.Dyadic.toReal]

/-- A coefficient-exponent pair together with the sign bit, which a zero coefficient cannot
record. -/
abbrev State := (Int × Int) × Bool

/-- The integer state of a binary64 value: its decoded pair and its sign bit. -/
def encode {fmt : FloatFormat} (x : Model fmt) : State :=
  (decode x, Model.signBit x)

/-- The observation of an integer state: its real value paired with its sign bit. -/
noncomputable def stateReal (x : State) : ℝ × Bool :=
  (IntegerRounding.toReal x.1, x.2)

/-- `stateReal ∘ encode` is the observation `FiniteRepresentation.observe`. -/
theorem encode_real {fmt : FloatFormat} (x : Model fmt) :
    stateReal (encode x) = FiniteRepresentation.observe x := by
  simp [stateReal, encode, FiniteRepresentation.observe, decode_real]

/-- The sign bit of a rounded sum: for an exact zero the AND of the input signs, otherwise the
sign of the exact sum. -/
def addSign (sx sy : Bool) (sum : Int × Int) : Bool :=
  if sum.1 = 0 then sx && sy else decide (sum.1 < 0)

/-- `addSign` agrees with the real-valued sign rule of `FiniteRepresentation.roundedAdd`. -/
theorem addSign_real (sx sy : Bool) (sum : Int × Int) :
    addSign sx sy sum =
      if IntegerRounding.toReal sum = 0 then sx && sy
      else decide (IntegerRounding.toReal sum < 0) := by
  simp only [addSign, IntegerRounding.toReal_eq_zero, IntegerRounding.toReal_neg]

/-- Integer addition of two states: round the exact sum with `roundSigned` and attach
`addSign`. -/
def add (fmt : FloatFormat) (x y : State) : State :=
  let exact := IntegerRounding.add x.1 y.1
  (IntegerRounding.roundSigned fmt exact, addSign x.2 y.2 exact)

/-- Integer multiplication of two states: round the exact product and XOR the sign bits. -/
def mul (fmt : FloatFormat) (x y : State) : State :=
  (IntegerRounding.roundSigned fmt (IntegerRounding.mul x.1 y.1), Bool.xor x.2 y.2)

/-- `add` refines `FiniteRepresentation.roundedAdd` through `stateReal`. -/
theorem add_real (fmt : FloatFormat) (x y : State) :
    stateReal (add fmt x y) =
      FiniteRepresentation.roundedAdd fmt (stateReal x) (stateReal y) := by
  simp only [add, stateReal, FiniteRepresentation.roundedAdd,
    ← IntegerRounding.roundSigned_real, addSign_real, IntegerRounding.add_real]
  congr 1

/-- `mul` refines `FiniteRepresentation.roundedMul` through `stateReal`. -/
theorem mul_real (fmt : FloatFormat) (x y : State) :
    stateReal (mul fmt x y) =
      FiniteRepresentation.roundedMul fmt (stateReal x) (stateReal y) := by
  simp only [mul, stateReal, FiniteRepresentation.roundedMul,
    ← IntegerRounding.roundSigned_real, IntegerRounding.mul_real]

/-- `x` is finite, has the sign bit of `value`, and decodes to a pair equal to `value.1` after
exponent alignment. This is the integer specification of a result, zero sign included. -/
def Represents {fmt : FloatFormat} (x : Model fmt) (value : State) : Prop :=
  Model.isFinite x = true ∧ Model.signBit x = value.2 ∧
    IntegerRounding.Equal (decode x) value.1

/-- `Represents x value` is finiteness of `x` together with `observe x = stateReal value`. -/
theorem represents_iff_observe {fmt : FloatFormat} (x : Model fmt) (value : State) :
    Represents x value ↔
      Model.isFinite x = true ∧ FiniteRepresentation.observe x = stateReal value := by
  simp only [Represents, FiniteRepresentation.observe, stateReal,
    IntegerRounding.equal_iff_real, decode_real, Prod.mk.injEq]
  tauto

/-- Two finite values represented by the same integer state are equal, since the observation is
injective on finite values. -/
theorem represents_unique {fmt : FloatFormat} {x y : Model fmt} {value : State}
    (hx : Represents x value) (hy : Represents y value) : x = y := by
  rw [represents_iff_observe] at hx hy
  exact FiniteRepresentation.observe_injective hx.1 hy.1 (hx.2.trans hy.2.symm)

/-- If x and y are finite and |x + y| ≤ maxFinite then `Model.add x y = z` holds exactly when
`z` represents the integer sum of the two encodings. -/
theorem add_eq_iff {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x y z : Model fmt) (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hb : |Model.toReal x + Model.toReal y| ≤ Model.toReal (Model.posMaxFinite fmt)) :
    Model.add x y = z ↔ Represents z (add fmt (encode x) (encode y)) := by
  rw [represents_iff_observe, add_real, encode_real, encode_real]
  exact FiniteRepresentation.add_eq_iff hfmt x y z hx hy hb

/-- If x and y are finite and |x · y| ≤ maxFinite then `Model.mul x y = z` holds exactly when
`z` represents the integer product of the two encodings. -/
theorem mul_eq_iff {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x y z : Model fmt) (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hb : |Model.toReal x * Model.toReal y| ≤ Model.toReal (Model.posMaxFinite fmt)) :
    Model.mul x y = z ↔ Represents z (mul fmt (encode x) (encode y)) := by
  rw [represents_iff_observe, mul_real, encode_real, encode_real]
  exact FiniteRepresentation.mul_eq_iff hfmt x y z hx hy hb

/-- The integer recurrence of the loop: fold `add` of `mul (encode weight) (encode (f node))`
over the terms, starting from `initial`. -/
def sum (fmt : FloatFormat) (f : Model fmt → Model fmt)
    (terms : List (Model fmt × Model fmt)) (initial : State) : State :=
  terms.foldl (fun acc t ↦ add fmt acc (mul fmt (encode t.1) (encode (f t.2)))) initial

/-- `stateReal` of the integer recurrence is the observed real recurrence of
`FiniteRepresentation`, by induction over the terms. -/
theorem sum_real (fmt : FloatFormat) (f : Model fmt → Model fmt)
    (terms : List (Model fmt × Model fmt)) (initial : State) :
    stateReal (sum fmt f terms initial) =
      (terms.map fun t ↦ FiniteRepresentation.roundedMul fmt
        (FiniteRepresentation.observe t.1) (FiniteRepresentation.observe (f t.2))).foldl
          (FiniteRepresentation.roundedAdd fmt) (stateReal initial) := by
  induction terms generalizing initial with
  | nil => rfl
  | cons t ts ih =>
      simp only [sum, List.foldl_cons, List.map_cons]
      change stateReal (sum fmt f ts
        (add fmt initial (mul fmt (encode t.1) (encode (f t.2))))) = _
      rw [ih, add_real, mul_real, encode_real, encode_real]

/-- Under the range budget `integrate f terms = z` holds exactly when `z` represents the integer
recurrence started at `((0, 0), false)`, that is, at positive zero. -/
theorem integrate_eq_iff (f : Value → Value) (terms : List (Value × Value)) (radius : ℝ)
    (hmax : radius ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64))
    (hfinite : ∀ t ∈ terms,
      Model.isFinite t.1 = true ∧ Model.isFinite (f t.2) = true)
    (hbudget :
      (terms.map fun t ↦ |Model.toReal t.1 * Model.toReal (f t.2)|).sum +
        2 * terms.length * Model.epsilonAt FloatFormat.binary64 radius ≤ radius)
    (z : Value) :
    integrate f terms = z ↔
      Represents z (sum FloatFormat.binary64 f terms ((0, 0), false)) := by
  rw [represents_iff_observe, sum_real]
  simpa [stateReal, IntegerRounding.toReal] using
    FiniteRepresentation.integrate_eq_iff f terms radius hmax hfinite hbudget z

end Quadrature.Binary64.FiniteInteger
