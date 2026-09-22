import Mathlib.Topology.ContinuousMap.Weierstrass
import Quadrature.Analysis.Gaussian

/-!
# Weighted Gaussian rules and convergence

`GaussianRule a b w hw n` packages `n` nodes and weights with the facts that the nodes are
distinct and lie in `(a, b)`, the weights are positive, and the rule is exact against `w`
through degree `2n - 1`. `gaussianRule` builds one from `exists_gaussian_quadrature`.
Exactness on constants makes the total mass of the rule equal to `∫ w`, so a polynomial
within `δ` of `f` uniformly controls both the rule and the integral with the same constant,
independently of `n`. Weierstrass approximation then gives `gaussian_rules_converge`.
-/

namespace Quadrature

open Polynomial MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- A Gaussian rule on `[a, b]` for the weight `w`: `n` distinct nodes in `(a, b)`, positive
weights, and exactness against `w` for every polynomial of degree below `2n`. -/
structure GaussianRule (a b : ℝ) (w : ℝ → ℝ)
    (hw : ContinuousOn w (uIcc a b)) (n : ℕ) where
  nodes : Fin n → ℝ
  weights : Fin n → ℝ
  injective : Function.Injective nodes
  interior : ∀ i, nodes i ∈ Ioo a b
  positive : ∀ i, 0 < weights i
  exact : ∀ p : ℝ[X], p.natDegree < 2 * n →
    ∑ i, weights i * p.eval (nodes i) = polynomialIntegral a b w hw p

/-- The Gaussian rule supplied by `exists_gaussian_quadrature`: nodes at the roots of the
monic orthogonal polynomial `p_n`, weights the Christoffel numbers. -/
def gaussianRule {a b : ℝ} (hab : a < b) (w : ℝ → ℝ)
    (hw : ContinuousOn w (uIcc a b)) (hwpos : ∀ x ∈ Icc a b, 0 < w x)
    (n : ℕ) (hn : 0 < n) : GaussianRule a b w hw n :=
  let h := exists_gaussian_quadrature hab w hw hwpos n hn
  { nodes := h.choose
    weights := interpolatoryWeight (polynomialIntegral a b w hw) h.choose
    injective := h.choose_spec.1
    interior := h.choose_spec.2.1
    positive := h.choose_spec.2.2.1
    exact := h.choose_spec.2.2.2 }

namespace GaussianRule

variable {a b : ℝ} {w : ℝ → ℝ} {hw : ContinuousOn w (uIcc a b)} {n : ℕ}

/-- The rule applied to a real function `f`: the sum over the nodes of the weight times the
value of `f` at that node. -/
def value (rule : GaussianRule a b w hw n) (f : ℝ → ℝ) : ℝ :=
  ∑ i, rule.weights i * f (rule.nodes i)

/-- The weights of a Gaussian rule sum to `∫_a^b w`, since the rule is exact on the constant
`1`. -/
theorem sum_weights (rule : GaussianRule a b w hw n) (hn : 0 < n) :
    ∑ i, rule.weights i = polynomialIntegral a b w hw 1 := by
  simpa using rule.exact 1 (by simp; omega)

/-- Each weight of a Gaussian rule is at most `∫_a^b w`, the sum of all the positive
weights. -/
theorem weight_le_mass (rule : GaussianRule a b w hw n) (hn : 0 < n) (i : Fin n) :
    rule.weights i ≤ polynomialIntegral a b w hw 1 := by
  rw [← rule.sum_weights hn]
  exact Finset.single_le_sum (fun j _ => (rule.positive j).le) (Finset.mem_univ i)

/-- If `|f - g| ≤ δ` on `[a, b]` then the rule values of `f` and `g` differ by at most
`(∫ w) δ`. Positivity of the weights and `sum_weights`. -/
theorem abs_value_sub_le (rule : GaussianRule a b w hw n) (hn : 0 < n)
    {f g : ℝ → ℝ} {δ : ℝ}
    (hfg : ∀ x ∈ Icc a b, |f x - g x| ≤ δ) :
    |rule.value f - rule.value g| ≤ polynomialIntegral a b w hw 1 * δ := by
  rw [value, value, ← Finset.sum_sub_distrib]
  calc
    |∑ i, (rule.weights i * f (rule.nodes i) - rule.weights i * g (rule.nodes i))| ≤
        ∑ i, |rule.weights i * f (rule.nodes i) - rule.weights i * g (rule.nodes i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, rule.weights i * δ := by
      apply Finset.sum_le_sum
      intro i _
      rw [← mul_sub, abs_mul, abs_of_pos (rule.positive i)]
      exact mul_le_mul_of_nonneg_left
        (hfg _ ⟨(rule.interior i).1.le, (rule.interior i).2.le⟩)
        (rule.positive i).le
    _ = _ := by rw [← Finset.sum_mul, rule.sum_weights hn]

/-- If a polynomial `p` of degree below `2n` is within `δ` of `f` on `[a, b]`, the rule value
of `f` is within `2 (∫ w) δ` of `∫ f w`. The rule is exact on `p`, and each of the rule and
the weighted integral moves by at most `(∫ w) δ` between `p` and `f`. -/
theorem error_le_of_polynomial_approx (rule : GaussianRule a b w hw n)
    (hn : 0 < n) (hab : a < b) (hwpos : ∀ x ∈ Icc a b, 0 < w x)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) (p : ℝ[X])
    (hp : p.natDegree < 2 * n) {δ : ℝ}
    (happrox : ∀ x ∈ Icc a b, |p.eval x - f x| ≤ δ) :
    |rule.value f - ∫ x in a..b, f x * w x| ≤
      2 * polynomialIntegral a b w hw 1 * δ := by
  have hw' : ContinuousOn w (Icc a b) := by simpa [uIcc_of_le hab.le] using hw
  have hfw : IntervalIntegrable (fun x => f x * w x) volume a b :=
    (hf.mul hw').intervalIntegrable_of_Icc hab.le
  have hpw : IntervalIntegrable (fun x => p.eval x * w x) volume a b :=
    (p.continuous.continuousOn.mul hw').intervalIntegrable_of_Icc hab.le
  have hdiff := hpw.sub hfw
  have hi :
      |polynomialIntegral a b w hw p - ∫ x in a..b, f x * w x| ≤
        polynomialIntegral a b w hw 1 * δ := by
    change |(∫ x in a..b, p.eval x * w x) - ∫ x in a..b, f x * w x| ≤ _
    rw [← intervalIntegral.integral_sub hpw hfw]
    have hnorm := intervalIntegral.norm_integral_le_integral_norm
      (a := a) (b := b) (μ := volume) hab.le
      (f := fun x => p.eval x * w x - f x * w x)
    have hle : (∫ x in a..b, ‖p.eval x * w x - f x * w x‖) ≤
        ∫ x in a..b, δ * w x := by
      apply intervalIntegral.integral_mono_on hab.le hdiff.norm
        ((continuousOn_const.mul hw').intervalIntegrable_of_Icc hab.le)
      intro x hx
      rw [← sub_mul, Real.norm_eq_abs, abs_mul, abs_of_pos (hwpos x hx)]
      exact mul_le_mul_of_nonneg_right (happrox x hx) (hwpos x hx).le
    have he : (∫ x in a..b, δ * w x) = polynomialIntegral a b w hw 1 * δ := by
      simp [polynomialIntegral, intervalIntegral.integral_const_mul, mul_comm]
    rw [he] at hle
    rw [Real.norm_eq_abs] at hnorm
    exact hnorm.trans hle
  have hs := rule.abs_value_sub_le hn happrox
  have he : rule.value p.eval = polynomialIntegral a b w hw p := rule.exact p hp
  rw [he, abs_sub_comm] at hs
  have ht := abs_sub_le (rule.value f) (polynomialIntegral a b w hw p)
    (∫ x in a..b, f x * w x)
  linarith

end GaussianRule

/-- For continuous `f` and a continuous strictly positive weight on `[a, b]`, the Gaussian
rules with `n + 1` nodes converge to `∫ f w` as `n → ∞`. Weierstrass approximation supplies
the polynomial for `error_le_of_polynomial_approx`. -/
theorem gaussian_rules_converge {a b : ℝ} (hab : a < b) (w : ℝ → ℝ)
    (hw : ContinuousOn w (uIcc a b)) (hwpos : ∀ x ∈ Icc a b, 0 < w x)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
    Filter.Tendsto
      (fun n => (gaussianRule hab w hw hwpos (n + 1) (by omega)).value f)
      Filter.atTop (nhds (∫ x in a..b, f x * w x)) := by
  have hm : 0 < polynomialIntegral a b w hw 1 := by
    simpa using polynomialIntegral_square_pos hab w hw hwpos 1 one_ne_zero
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ := ε / (4 * polynomialIntegral a b w hw 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b f hf δ hδ
  refine ⟨p.natDegree, fun n hn => ?_⟩
  have hbound := GaussianRule.error_le_of_polynomial_approx
    (gaussianRule hab w hw hwpos (n + 1) (by omega)) (by omega) hab hwpos hf p (by omega)
      (fun x hx => (hp x hx).le)
  have hcalc : 2 * polynomialIntegral a b w hw 1 * δ = ε / 2 := by
    dsimp [δ]
    field_simp [ne_of_gt hm]
    ring
  rw [hcalc] at hbound
  rw [Real.dist_eq]
  linarith

end
end Quadrature
