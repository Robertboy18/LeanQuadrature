import Quadrature.Examples.CosineCallback

/-!
# Accuracy of the two-point binary64 program

The only hypothesis is `CosineContract`: the cosine call is finite and within
`10⁻¹⁵` of the exact cosine at the two stored nodes. Node displacement, the
callback arithmetic, multiplication by the unit weights, and both loop additions
are bounded with the radius-8 lemmas, and finiteness of each operation is
proved. The program result is within `0.00356` of `sin 1`, and the Appel–Bindel
manuscript's bound `0.00224` is refuted for every cosine satisfying the contract.
-/

namespace Quadrature.Binary64

open FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory

/-- The cosine call is finite and within `10⁻¹⁵` of `Real.cos` at the two inputs `leftNode` and
`rightNode`, the only arguments the two-point program passes to it. -/
def CosineContract (cosine : Value → Value) : Prop :=
  ∀ x, x = leftNode ∨ x = rightNode →
    Model.isFinite (cosine x) = true ∧
    |Model.toReal (cosine x) - Real.cos (Model.toReal x)| ≤ (1 / 10 ^ 15 : ℝ)

/-- If a stored node is within `10⁻¹⁶` of the ideal node and the cosine is finite and accurate
to `10⁻¹⁵` there, then `testfun` is finite and within `6·10⁻¹⁵` of the ideal integrand
value. -/
theorem testfun_at_node (cosine : Value → Value) {node : Value} {ideal : ℝ}
    (hnode : Model.isFinite node = true) (hbound : |Model.toReal node| ≤ 1)
    (hdisplacement : |Model.toReal node - ideal| ≤ (1 / 10 ^ 16 : ℝ))
    (hcfinite : Model.isFinite (cosine node) = true)
    (hcerror : |Model.toReal (cosine node) - Real.cos (Model.toReal node)| ≤
      (1 / 10 ^ 15 : ℝ)) :
    Model.isFinite (testfun cosine node) = true ∧
    |Model.toReal (testfun cosine node) - Example.integrand ideal| ≤
      (6 / 10 ^ 15 : ℝ) := by
  have hf := testfun_error cosine node hnode hbound hcfinite hcerror
  refine ⟨hf.1, ?_⟩
  have hn := integrand_node_error hbound hdisplacement
  have ht := abs_sub_le (Model.toReal (testfun cosine node))
    (Example.integrand (Model.toReal node)) (Example.integrand ideal)
  linarith

/-- If y is finite and within `6·10⁻¹⁵` of an ideal of magnitude at most 1, then `one * y` is
finite, within `7·10⁻¹⁵` of the ideal, and of magnitude at most 2. -/
theorem unit_weight_sample (y : Value) (ideal : ℝ)
    (hy : Model.isFinite y = true) (hi : |ideal| ≤ 1)
    (he : |Model.toReal y - ideal| ≤ (6 / 10 ^ 15 : ℝ)) :
    Model.isFinite (Model.mul one y) = true ∧
    |Model.toReal (Model.mul one y) - ideal| ≤ (7 / 10 ^ 15 : ℝ) ∧
    |Model.toReal (Model.mul one y)| ≤ 2 := by
  have hyb : |Model.toReal y| ≤ 2 := by
    have he' := abs_le.mp he
    have hi' := abs_le.mp hi
    rw [abs_le]
    constructor <;> linarith
  have hm := mul_small one y one_finite hy (by
    rw [one_toReal, one_mul]
    linarith)
  rw [one_toReal, one_mul] at hm
  have hb : |Model.toReal (Model.mul one y) - ideal| ≤ (7 / 10 ^ 15 : ℝ) := by
    have ht := abs_sub_le (Model.toReal (Model.mul one y)) (Model.toReal y) ideal
    linarith [hm.2]
  refine ⟨hm.1, hb, ?_⟩
  have he' := abs_le.mp hb
  have hi' := abs_le.mp hi
  rw [abs_le]
  constructor <;> linarith

/-- If both callback values are finite and within `6·10⁻¹⁵` of ideals of magnitude at most 1,
the two-point loop is finite and within `2·10⁻¹⁴` of the ideal sum. The two multiplications
and the two additions, including the one with the initial zero, are each bounded. -/
theorem two_point_accumulation (f : Value → Value) (u v : ℝ)
    (hl : Model.isFinite (f leftNode) = true)
    (hr : Model.isFinite (f rightNode) = true)
    (hu : |u| ≤ 1) (hv : |v| ≤ 1)
    (hel : |Model.toReal (f leftNode) - u| ≤ (6 / 10 ^ 15 : ℝ))
    (her : |Model.toReal (f rightNode) - v| ≤ (6 / 10 ^ 15 : ℝ)) :
    Model.isFinite (integrate f twoPointTerms) = true ∧
    |Model.toReal (integrate f twoPointTerms) - (u + v)| ≤ (2 / 10 ^ 14 : ℝ) := by
  have hpl := unit_weight_sample (f leftNode) u hl hu hel
  have hpr := unit_weight_sample (f rightNode) v hr hv her
  have ha := add_small zero (Model.mul one (f leftNode)) zero_finite hpl.1 (by
    rw [zero_toReal, zero_add]
    linarith [hpl.2.2])
  rw [zero_toReal, zero_add] at ha
  have hab : |Model.toReal (Model.add zero (Model.mul one (f leftNode)))| ≤ 3 := by
    have h₁ := abs_le.mp ha.2
    have h₂ := abs_le.mp hpl.2.2
    rw [abs_le]
    constructor <;> linarith
  have hs := add_small (Model.add zero (Model.mul one (f leftNode)))
    (Model.mul one (f rightNode)) ha.1 hpr.1 (by
      exact (abs_add_le _ _).trans (by linarith [hpr.2.2]))
  change Model.isFinite (integrate f twoPointTerms) = true ∧
    |Model.toReal (integrate f twoPointTerms) -
      (Model.toReal (Model.add zero (Model.mul one (f leftNode))) +
        Model.toReal (Model.mul one (f rightNode)))| ≤ (1 / 10 ^ 15 : ℝ) at hs
  refine ⟨hs.1, ?_⟩
  have h₁ := abs_le.mp hs.2
  have h₂ := abs_le.mp ha.2
  have h₃ := abs_le.mp hpl.2.1
  have h₄ := abs_le.mp hpr.2.1
  rw [abs_le]
  constructor <;> linarith

/-- Under `CosineContract` the two-point program is finite and within `2·10⁻¹⁴` of the exact
two-point sum, which is `cos(1/√3)`. -/
theorem two_point_roundoff (cosine : Value → Value) (hc : CosineContract cosine) :
    Model.isFinite (integrate (testfun cosine) twoPointTerms) = true ∧
    |Model.toReal (integrate (testfun cosine) twoPointTerms) -
      Real.cos (1 / Real.sqrt 3)| ≤ (2 / 10 ^ 14 : ℝ) := by
  have hcl := hc leftNode (Or.inl rfl)
  have hcr := hc rightNode (Or.inr rfl)
  have hl := testfun_at_node cosine leftNode_finite
    (by rw [leftNode_toReal]; norm_num) leftNode_error hcl.1 hcl.2
  have hr := testfun_at_node cosine rightNode_finite
    (by rw [rightNode_toReal]; norm_num) rightNode_error hcr.1 hcr.2
  have hn : |(1 / Real.sqrt (3 : ℝ))| ≤ 1 := by
    have hsq : (1 / Real.sqrt (3 : ℝ)) ^ 2 = (1 / 3 : ℝ) := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    rw [abs_le]
    constructor <;> nlinarith
  have h := two_point_accumulation (testfun cosine)
    (Example.integrand (-(1 / Real.sqrt 3))) (Example.integrand (1 / Real.sqrt 3))
    hl.1 hr.1 (integrand_abs_le_one (by simpa using hn)) (integrand_abs_le_one hn)
    hl.2 hr.2
  rwa [Example.two_point_eq] at h

/-- Under `CosineContract` the two-point program is finite and within `0.00356` of the integral
of the integrand over `[-1, 1]`. The bound is corrected from the manuscript's `0.00224`, since
`|cos(1/√3) − sin 1|` is about `0.003560`. -/
theorem two_point_program_accuracy (cosine : Value → Value) (hc : CosineContract cosine) :
    Model.isFinite (integrate (testfun cosine) twoPointTerms) = true ∧
    |Model.toReal (integrate (testfun cosine) twoPointTerms) -
      ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤ (356 / 100000 : ℝ) := by
  have h := two_point_roundoff cosine hc
  refine ⟨h.1, ?_⟩
  rw [Example.integral_eq]
  have he : |Real.cos (1 / Real.sqrt 3) - Real.sin 1| ≤ (35596 / 10000000 : ℝ) := by
    rw [abs_le]
    constructor <;>
      linarith [Example.sin_one_upper, Example.cos_node_lower,
        Example.sin_one_lower, Example.cos_node_upper]
  have ht := abs_sub_le (Model.toReal (integrate (testfun cosine) twoPointTerms))
    (Real.cos (1 / Real.sqrt 3)) (Real.sin 1)
  linarith [h.2]

/-- Under `CosineContract` the program's error exceeds the Appel–Bindel manuscript's bound
`0.00224`. The exact two-point sum `cos(1/√3)` is already more than `0.00224` from `sin 1`, and
rounding moves the computed value by at most `2·10⁻¹⁴`. -/
theorem paper_program_bound_false (cosine : Value → Value) (hc : CosineContract cosine) :
    ¬ |Model.toReal (integrate (testfun cosine) twoPointTerms) -
      ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤ (224 / 100000 : ℝ) := by
  rw [Example.integral_eq]
  have hr := abs_le.mp (two_point_roundoff cosine hc).2
  intro h
  have h' := abs_le.mp h
  linarith [Example.sin_one_lower, Example.cos_node_upper]

end Quadrature.Binary64
