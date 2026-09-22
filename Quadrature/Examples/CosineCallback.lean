import Quadrature.Binary64.BoundedRoundoff
import Quadrature.Examples.TwoPointCosine

/-!
# The example callback and node perturbation

The callback of the original C program computes `0.5 * (1 - x) * cos(x)` with one
subtraction and two multiplications. This file bounds the real integrand and its
sensitivity to node displacement, then proves that the three operations are
finite and that the callback result is within `5·10⁻¹⁵` of the ideal integrand.
The cosine hypothesis is stated at the binary64 input `x` that the callback
passes to the cosine, so no separate rounding of the argument is needed.
-/

namespace Quadrature.Binary64

open FloatLib.Floats.Formats.BinaryInterchange

/-- If |x| ≤ 1 then |integrand x| ≤ 1, since |(1 - x)/2| ≤ 1 and |cos x| ≤ 1. -/
theorem integrand_abs_le_one {x : ℝ} (hx : |x| ≤ 1) :
    |Example.integrand x| ≤ 1 := by
  have hx' := abs_le.mp hx
  have hw : |(1 / 2 : ℝ) * (1 - x)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  rw [Example.integrand, abs_mul]
  exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one x) (abs_nonneg _)).trans
    (by simpa using hw)

/-- If |x| ≤ 1 and |x − y| ≤ δ then the integrand values at x and y differ by at most 2δ.
Cosine is 1-Lipschitz and the linear factor moves by δ/2. -/
theorem integrand_node_error {x y δ : ℝ} (hx : |x| ≤ 1) (hxy : |x - y| ≤ δ) :
    |Example.integrand x - Example.integrand y| ≤ 2 * δ := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hxy
  have hw : |(1 / 2 : ℝ) * (1 - x)| ≤ 1 := by
    have hx' := abs_le.mp hx
    rw [abs_le]
    constructor <;> linarith
  have hwd : |(1 / 2 : ℝ) * (1 - x) - (1 / 2) * (1 - y)| ≤ δ / 2 := by
    have he : (1 / 2 : ℝ) * (1 - x) - (1 / 2) * (1 - y) = -(x - y) / 2 := by ring
    rw [he, abs_div, abs_neg]
    norm_num
    linarith
  have h := weighted_sample_error hwd ((Real.abs_cos_sub_cos_le x y).trans hxy)
  change |Example.integrand x - Example.integrand y| ≤
    |(1 / 2 : ℝ) * (1 - x)| * δ + δ / 2 * |Real.cos y| at h
  have ht := mul_le_mul_of_nonneg_right hw hδ
  have hc := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one y) (by positivity : 0 ≤ δ / 2)
  nlinarith

/-- If x is finite with |x| ≤ 1 and `cosine x` is finite and within `10⁻¹⁵` of cos x, then
`testfun cosine x` is finite and within `5·10⁻¹⁵` of `integrand x`. Finiteness of the
subtraction and both multiplications is a conclusion, from the radius-8 lemmas. -/
theorem testfun_error (cosine : Value → Value) (x : Value)
    (hx : Model.isFinite x = true) (hbound : |Model.toReal x| ≤ 1)
    (hcfinite : Model.isFinite (cosine x) = true)
    (hcerror : |Model.toReal (cosine x) - Real.cos (Model.toReal x)| ≤
      (1 / 10 ^ 15 : ℝ)) :
    Model.isFinite (testfun cosine x) = true ∧
    |Model.toReal (testfun cosine x) - Example.integrand (Model.toReal x)| ≤
      (5 / 10 ^ 15 : ℝ) := by
  have hx' := abs_le.mp hbound
  have hsub := sub_small one x (by decide) hx (by
    rw [one_toReal, abs_le]
    constructor <;> linarith)
  rw [one_toReal] at hsub
  have hsabs : |Model.toReal (Model.sub one x)| ≤ 3 := by
    have h := abs_le.mp hsub.2
    rw [abs_le]
    constructor <;> linarith
  have hhalf := mul_small half (Model.sub one x) (by decide) hsub.1 (by
    rw [half_toReal, abs_mul]
    norm_num
    linarith)
  rw [half_toReal] at hhalf
  have hhabs : |Model.toReal (Model.mul half (Model.sub one x))| ≤ 2 := by
    have hh := abs_le.mp hhalf.2
    have hs := abs_le.mp hsabs
    rw [abs_le]
    constructor <;> linarith
  have hcabs : |Model.toReal (cosine x)| ≤ 2 := by
    have htri := abs_add_le
      (Model.toReal (cosine x) - Real.cos (Model.toReal x)) (Real.cos (Model.toReal x))
    rw [sub_add_cancel] at htri
    linarith [Real.abs_cos_le_one (Model.toReal x)]
  have hmul := mul_small (Model.mul half (Model.sub one x)) (cosine x)
    hhalf.1 hcfinite (by
      rw [abs_mul]
      nlinarith [abs_nonneg (Model.toReal (Model.mul half (Model.sub one x))),
        abs_nonneg (Model.toReal (cosine x))])
  refine ⟨hmul.1, ?_⟩
  have hherror :
      |Model.toReal (Model.mul half (Model.sub one x)) -
        (1 / 2 : ℝ) * (1 - Model.toReal x)| ≤ (2 / 10 ^ 15 : ℝ) := by
    have h₁ := abs_le.mp hhalf.2
    have h₂ := abs_le.mp hsub.2
    rw [abs_le]
    constructor <;> linarith
  have h := rounded_weighted_sample_error hherror hcerror hmul.2
  change |Model.toReal (testfun cosine x) - Example.integrand (Model.toReal x)| ≤
    1 / 10 ^ 15 + |Model.toReal (Model.mul half (Model.sub one x))| * (1 / 10 ^ 15) +
      (2 / 10 ^ 15) * |Real.cos (Model.toReal x)| at h
  nlinarith [Real.abs_cos_le_one (Model.toReal x)]

end Quadrature.Binary64
