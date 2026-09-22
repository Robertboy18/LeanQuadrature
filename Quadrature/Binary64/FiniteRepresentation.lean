import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Representation
import Quadrature.Binary64.FiniteExecution

/-!
# Finite values, signed zeros, and the quadrature recurrence

The observation of a finite binary64 value is the pair (real value, sign bit).
Real decoding alone identifies the two zeros, and the sign bit restores the
distinction, so the observation is injective on finite values. Addition and
multiplication then have complete specifications in terms of nearest-even real
rounding and sign rules, including the sign of an exact zero sum and of a
product that underflows to zero.

Under the range budget every operation of the loop is finite, so the observed
recurrence determines the complete binary64 result, signed zeros included.
-/

namespace Quadrature.Binary64

open FloatLib.Floats.Formats.BinaryInterchange

namespace FiniteRepresentation

/-- Two finite values with the same real value and the same sign bit are equal. The only real
value shared by distinct encodings is zero, and the sign bit separates the two zeros. -/
theorem eq_of_real_sign {fmt : FloatFormat} {x y : Model fmt}
    (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hr : Model.toReal x = Model.toReal y)
    (hs : Model.signBit x = Model.signBit y) : x = y := by
  by_cases hz : Model.toReal x = 0
  · obtain ⟨dx, hdx⟩ := Model.exists_toDyadic?_of_isFinite hx
    obtain ⟨dy, hdy⟩ := Model.exists_toDyadic?_of_isFinite hy
    have hx0 : dx.significand = 0 := (Model.Dyadic.toReal_eq_zero_iff dx).mp
      (by simpa [Model.toReal_eq, hdx] using hz)
    have hy0 : dy.significand = 0 := (Model.Dyadic.toReal_eq_zero_iff dy).mp
      (by simpa [Model.toReal_eq, hdy] using hr.symm.trans hz)
    have hzx := Model.toDyadic?_eq_zero_of_isZero_eq_true x
      (Model.isZero_eq_true_of_toDyadic?_some_of_mant_eq_zero hdx hx0)
    have hzy := Model.toDyadic?_eq_zero_of_isZero_eq_true y
      (Model.isZero_eq_true_of_toDyadic?_some_of_mant_eq_zero hdy hy0)
    rw [hs] at hzx
    exact Model.eq_of_toDyadic?_eq_some hzx hzy
  · exact Model.eq_of_toReal_eq_of_nonzero hx hy hr hz

private theorem signBit_ofModel_finite (fmt : FloatFormat)
    (sign : Float.Model.UnpackedFloat.Sign) (mantissa : Nat) (exponent : Int)
    (hm : 0 < mantissa) :
    Model.signBit (Model.ofModel fmt (.finite sign mantissa exponent hm)) =
      Model.modelSignBit sign := by
  rw [← Model.modelSignBit_ofBitVec_unpackSign]
  unfold Model.toModelBits Model.ofModel Model.ofModelBits
    Float.Model.UnpackedFloat.pack
  dsimp only
  split_ifs <;>
    simp only [Float.Model.UnpackedFloat.packedInfinity,
      Model.unpackSign_packComponents] <;>
    cases sign <;> rfl

/-- Rounding a dyadic to an IEEE format preserves its sign, including when the result is zero or
infinite. -/
theorem signBit_roundDyadic {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (d : FloatLib.Numerics.Dyadic) :
    Model.signBit (Model.roundDyadic fmt d) = d.negative := by
  simp only [Model.roundDyadic, hfmt, ite_true, Model.ieeeRoundDyadic]
  unfold Float.Model.UnpackedFloat.round Float.Model.UnpackedFloat.roundWithAccuracy
  dsimp only
  split_ifs
  · simp only [Model.signBit_ofModel_zero]
    cases d.negative <;> rfl
  · rw [signBit_ofModel_finite]
    cases d.negative <;> rfl

private theorem dyadic_negative_of_nonzero (d : FloatLib.Numerics.Dyadic)
    (h : d.toReal ≠ 0) : d.negative = decide (d.toReal < 0) := by
  have hm : (0 : ℝ) < d.significand := by
    exact_mod_cast Nat.pos_of_ne_zero ((Model.Dyadic.toReal_eq_zero_iff d).not.mp h)
  have hp : 0 < (2 : ℝ) ^ d.exponent := zpow_pos (by norm_num) _
  cases hs : d.negative <;>
    simp [FloatLib.Numerics.Dyadic.toReal,
      FloatLib.Numerics.Dyadic.signedSignificand, hs, neg_mul,
      not_lt.mpr (mul_pos hm hp).le, mul_pos hm hp]

private theorem dyadic_add_negative_of_zero (x y : FloatLib.Numerics.Dyadic)
    (h : (Model.addDyadic x y).significand = 0) :
    (Model.addDyadic x y).negative = (x.negative && y.negative) := by
  unfold Model.addDyadic FloatLib.Numerics.Dyadic.add
    FloatLib.Numerics.Dyadic.addFields at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ <;> simp_all

/-- The sign of a sum of finite values is the AND of the input signs when the exact sum is zero,
and the sign of the exact sum otherwise. -/
theorem signBit_add {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x y : Model fmt) (hx : Model.isFinite x = true) (hy : Model.isFinite y = true) :
    Model.signBit (Model.add x y) =
      if Model.toReal x + Model.toReal y = 0 then
        Model.signBit x && Model.signBit y
      else decide (Model.toReal x + Model.toReal y < 0) := by
  obtain ⟨dx, hdx⟩ := Model.exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := Model.exists_toDyadic?_of_isFinite hy
  have hadd : Model.add x y = Model.roundDyadic fmt (Model.addDyadic dx dy) := by
    simp [Model.Proof.add_eq_spec, Model.Spec.add, hdx, hdy]
  have hr : (Model.addDyadic dx dy).toReal = Model.toReal x + Model.toReal y := by
    simp [Model.Dyadic.toReal_addDyadic, Model.toReal_eq, hdx, hdy]
  rw [hadd, signBit_roundDyadic hfmt]
  split_ifs with hz
  · rw [dyadic_add_negative_of_zero dx dy
      ((Model.Dyadic.toReal_eq_zero_iff _).mp (hr.trans hz)),
      Model.sign_eq_signBit_of_toDyadic?_some hdx,
      Model.sign_eq_signBit_of_toDyadic?_some hdy]
  · rw [dyadic_negative_of_nonzero _ (by simpa [hr] using hz), hr]

/-- The sign of a product of finite values is the XOR of the input signs, including when the
product is zero. -/
theorem signBit_mul {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x y : Model fmt) (hx : Model.isFinite x = true) (hy : Model.isFinite y = true) :
    Model.signBit (Model.mul x y) = Bool.xor (Model.signBit x) (Model.signBit y) := by
  obtain ⟨dx, hdx⟩ := Model.exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := Model.exists_toDyadic?_of_isFinite hy
  rw [Model.Proof.mul_eq_spec]
  simp only [Model.Spec.mul, hdx, hdy]
  split_ifs
  · rw [Model.signBit_zero,
      FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt]
    simp only [Bool.and_true, Model.sign_eq_signBit_of_toDyadic?_some hdx,
      Model.sign_eq_signBit_of_toDyadic?_some hdy]
  · rw [signBit_roundDyadic hfmt]
    simp only [Model.sign_eq_signBit_of_toDyadic?_some hdx,
      Model.sign_eq_signBit_of_toDyadic?_some hdy]

/-- The observation of a binary64 value: its real value paired with its sign bit. -/
noncomputable def observe {fmt : FloatFormat} (x : Model fmt) : ℝ × Bool :=
  (Model.toReal x, Model.signBit x)

/-- Addition on observations: nearest-even rounding of the exact sum, with the IEEE sign rule
for an exact zero. -/
noncomputable def roundedAdd (fmt : FloatFormat) (x y : ℝ × Bool) : ℝ × Bool :=
  (Model.roundAt fmt (x.1 + y.1),
    if x.1 + y.1 = 0 then x.2 && y.2 else decide (x.1 + y.1 < 0))

/-- Multiplication on observations: nearest-even rounding of the exact product, with the XOR
sign rule, which survives underflow to zero. -/
noncomputable def roundedMul (fmt : FloatFormat) (x y : ℝ × Bool) : ℝ × Bool :=
  (Model.roundAt fmt (x.1 * y.1), Bool.xor x.2 y.2)

/-- Finite values with equal observations are equal. -/
theorem observe_injective {fmt : FloatFormat} {x y : Model fmt}
    (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (h : observe x = observe y) : x = y :=
  eq_of_real_sign hx hy (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- If x, y, and their sum are finite then observing `Model.add x y` gives `roundedAdd` of the
two observations. -/
theorem observe_add {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x y : Model fmt) (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hfin : Model.isFinite (Model.add x y) = true) :
    observe (Model.add x y) = roundedAdd fmt (observe x) (observe y) :=
  Prod.ext (Model.toReal_add_eq_roundAt x y hfmt hx hy hfin) (signBit_add hfmt x y hx hy)

/-- If x, y, and their product are finite then observing `Model.mul x y` gives `roundedMul` of
the two observations. -/
theorem observe_mul {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x y : Model fmt) (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hfin : Model.isFinite (Model.mul x y) = true) :
    observe (Model.mul x y) = roundedMul fmt (observe x) (observe y) :=
  Prod.ext (Model.toReal_mul_eq_roundAt x y hfmt hx hy hfin) (signBit_mul hfmt x y hx hy)

/-- If x and y are finite and |x + y| ≤ maxFinite then `Model.add x y = z` holds exactly when z
is finite and observes to `roundedAdd (observe x) (observe y)`. -/
theorem add_eq_iff {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x y z : Model fmt) (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hb : |Model.toReal x + Model.toReal y| ≤ Model.toReal (Model.posMaxFinite fmt)) :
    Model.add x y = z ↔
      Model.isFinite z = true ∧ observe z = roundedAdd fmt (observe x) (observe y) := by
  have hf := Model.isFinite_add_of_abs_toReal_add_le_posMaxFinite x y hfmt hx hy hb
  have ho := observe_add hfmt x y hx hy hf
  constructor
  · rintro rfl
    exact ⟨hf, ho⟩
  · rintro ⟨hz, he⟩
    exact observe_injective hf hz (ho.trans he.symm)

/-- If x and y are finite and |x · y| ≤ maxFinite then `Model.mul x y = z` holds exactly when z
is finite and observes to `roundedMul (observe x) (observe y)`. -/
theorem mul_eq_iff {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x y z : Model fmt) (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hb : |Model.toReal x * Model.toReal y| ≤ Model.toReal (Model.posMaxFinite fmt)) :
    Model.mul x y = z ↔
      Model.isFinite z = true ∧ observe z = roundedMul fmt (observe x) (observe y) := by
  have hf := Model.isFinite_mul_of_abs_mul_le_posMaxFinite x y hfmt hx hy
    (by simpa only [abs_mul] using hb)
  have ho := observe_mul hfmt x y hx hy hf
  constructor
  · rintro rfl
    exact ⟨hf, ho⟩
  · rintro ⟨hz, he⟩
    exact observe_injective hf hz (ho.trans he.symm)

private theorem observe_tree {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (tree : FloatLib.Numerics.ReductionTree (Model fmt))
    (hf : Model.ReductionTree.FiniteEval tree) :
    observe (tree.eval Model.add id) = tree.eval (roundedAdd fmt) observe := by
  induction tree with
  | leaf x => rfl
  | node l r ihl ihr =>
    rw [FloatLib.Numerics.ReductionTree.eval, observe_add hfmt _ _
      hf.1.isFinite_eval hf.2.1.isFinite_eval hf.2.2, ihl hf.1, ihr hf.2.1]
    rfl

/-- Under the range budget, `observe (integrate f terms)` equals the fold of `roundedAdd` over
the `roundedMul` of the observed weights and callback values, starting from (+0, false). -/
theorem observe_integrate_from_budget (f : Value → Value)
    (terms : List (Value × Value)) (radius : ℝ)
    (hmax : radius ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64))
    (hfinite : ∀ t ∈ terms,
      Model.isFinite t.1 = true ∧ Model.isFinite (f t.2) = true)
    (hbudget :
      (terms.map fun t => |Model.toReal t.1 * Model.toReal (f t.2)|).sum +
        2 * terms.length * Model.epsilonAt FloatFormat.binary64 radius ≤ radius) :
    observe (integrate f terms) =
      (terms.map fun t =>
        roundedMul FloatFormat.binary64 (observe t.1) (observe (f t.2))).foldl
          (roundedAdd FloatFormat.binary64) (0, false) := by
  have ht := observe_tree (by decide) (integrationTree f terms)
    (integrationTree_finite_from_budget f terms radius hmax hfinite hbudget)
  rw [integrationTree_eval] at ht
  rw [ht, integrationTree, accumulationTree_eval_with]
  simp only [FloatLib.Numerics.ReductionTree.eval, observe, zero_toReal,
    List.map_map, Function.comp_def]
  change (terms.map fun t => observe (Model.mul t.1 (f t.2))).foldl
      (roundedAdd FloatFormat.binary64) (0, false) = _
  congr 1
  apply List.map_congr_left
  intro t ht
  exact observe_mul (by decide) _ _ (hfinite t ht).1 (hfinite t ht).2
    (weighted_product_finite_from_budget f terms radius hmax hfinite hbudget t ht)

/-- Under the range budget `integrate f terms = z` holds exactly when z is finite and its
observation equals the observed recurrence from (+0, false). -/
theorem integrate_eq_iff (f : Value → Value)
    (terms : List (Value × Value)) (radius : ℝ)
    (hmax : radius ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64))
    (hfinite : ∀ t ∈ terms,
      Model.isFinite t.1 = true ∧ Model.isFinite (f t.2) = true)
    (hbudget :
      (terms.map fun t => |Model.toReal t.1 * Model.toReal (f t.2)|).sum +
        2 * terms.length * Model.epsilonAt FloatFormat.binary64 radius ≤ radius)
    (z : Value) :
    integrate f terms = z ↔
      Model.isFinite z = true ∧ observe z =
        (terms.map fun t =>
          roundedMul FloatFormat.binary64 (observe t.1) (observe (f t.2))).foldl
            (roundedAdd FloatFormat.binary64) (0, false) := by
  have hf := (integrate_error_from_budget f terms radius hmax hfinite hbudget).1
  have ho := observe_integrate_from_budget f terms radius hmax hfinite hbudget
  constructor
  · rintro rfl
    exact ⟨hf, ho⟩
  · rintro ⟨hz, he⟩
    exact observe_injective hf hz (ho.trans he.symm)

end FiniteRepresentation
end Quadrature.Binary64
