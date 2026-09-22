import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass
import PDE.Symbolic.Continuum.Quadrature.Approximation

/-!
# Convergence from positivity and polynomial exactness

This file works with LeanPDE's `QuadratureRule`, a list of weight and node pairs on `[0, 1]`
transported to `[a, b]` by `valueOn`. The weight variation of a rule is `∑ |wᵢ|`, the
operator norm of the rule on bounded functions. For a rule with nonnegative weights that is
exact on constants the weight variation is one, so a polynomial within `ε` of `f` uniformly
controls the rule and the integral with a constant independent of the number of nodes, and
Weierstrass approximation gives convergence.
-/

namespace Quadrature

open MeasureTheory PDE.Symbolic.Continuum

noncomputable section

/-- A rule exact through degree `d` on `[0, 1]` integrates every polynomial of degree at most
`d` exactly on every interval `[a, b]`, since the affine pullback of `p` has the same
degree. -/
theorem valueOn_eq_integral_polynomial {rule : QuadratureRule} {d : ℕ}
    (hexact : rule.ExactUpTo d) (p : Polynomial ℝ) (hp : p.natDegree ≤ d)
    (a b : ℝ) :
    rule.valueOn p.eval a b = ∫ x in a..b, p.eval x := by
  apply rule.valueOn_eq_integral_of_exactFor
  let q := p.comp (Polynomial.C a + Polynomial.C (b - a) * Polynomial.X)
  have hq : q.natDegree ≤ d :=
    (affinePullback_natDegree_le p a b).trans hp
  simpa [q, Polynomial.eval_comp, mul_comm] using
    QuadratureRule.exactFor_polynomial hexact q hq

/-- A rule with nonnegative weights that is exact on constants has weight variation
`∑ |wᵢ| = 1`: the weights sum to one and none is negative. -/
theorem weightVariation_eq_one {rule : QuadratureRule}
    (hpositive : ∀ term ∈ rule.terms, 0 ≤ term.1)
    (hexact : rule.ExactUpTo 0) :
    rule.weightVariation = 1 := by
  have h := hexact 0 (by omega)
  simp only [QuadratureRule.moment, QuadratureRule.normalizedValue, weightedSum,
    pow_zero, Nat.cast_zero, zero_add, div_one, List.map_map, Function.comp_def,
    mul_one] at h
  rw [QuadratureRule.weightVariation]
  convert h using 1
  congr 1
  apply List.map_congr_left
  intro term hterm
  exact abs_of_nonneg (hpositive term hterm)

/-- If `p` is within `ε` of `f` uniformly on `[a, b]` and the rule integrates `p` exactly
there, the quadrature error of `f` is at most `(b - a) (V + 1) ε`, with `V` the weight
variation of the rule. -/
theorem error_le_of_polynomial_approx {rule : QuadratureRule} {a b ε : ℝ}
    (hab : a ≤ b) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    (p : Polynomial ℝ)
    (happrox : ∀ x ∈ Set.Icc a b, |p.eval x - f x| ≤ ε)
    (hexact : rule.valueOn p.eval a b = ∫ x in a..b, p.eval x) :
    |rule.valueOn f a b - ∫ x in a..b, f x| ≤
      (b - a) * (rule.weightVariation + 1) * ε := by
  have hs := rule.abs_valueOn_sub_le (f := p.eval) (g := f) (eps := ε)
    (a := a) (b := b) (by
    intro x hx
    simpa [Set.uIcc_of_le hab, Real.norm_eq_abs] using happrox x
      (by simpa [Set.uIcc_of_le hab] using hx))
  have hi : |(∫ x in a..b, p.eval x) - ∫ x in a..b, f x| ≤ ε * (b - a) := by
    rw [← intervalIntegral.integral_sub (p.continuous.intervalIntegrable a b)
      (hf.intervalIntegrable_of_Icc hab)]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (f := fun x => p.eval x - f x) (C := ε) (by
        intro x hx
        rw [Real.norm_eq_abs]
        apply happrox x
        have hx' : x ∈ Set.Ioc a b := by simpa [Set.uIoc_of_le hab] using hx
        exact ⟨hx'.1.le, hx'.2⟩)
    simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using h
  rw [abs_sub_comm, hexact, abs_of_nonneg (sub_nonneg.mpr hab)] at hs
  have ht := abs_sub_le (rule.valueOn f a b) (∫ x in a..b, p.eval x)
    (∫ x in a..b, f x)
  nlinarith

/-- Rules with nonnegative weights, the `n`th exact through degree `n`, converge to `∫_a^b f`
for every continuous `f` on `[a, b]`. Weierstrass approximation supplies the polynomial, so
continuity of `f` suffices. -/
theorem positive_rules_converge (rules : ℕ → QuadratureRule)
    (hpositive : ∀ n term, term ∈ (rules n).terms → 0 ≤ term.1)
    (hexact : ∀ n, (rules n).ExactUpTo n)
    {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) :
    Filter.Tendsto (fun n => (rules n).valueOn f a b) Filter.atTop
      (nhds (∫ x in a..b, f x)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ := ε / (4 * (b - a))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b f hf δ hδ
  refine ⟨p.natDegree, fun n hn => ?_⟩
  have hw : (rules n).weightVariation = 1 :=
    weightVariation_eq_one (hpositive n) (fun k hk => hexact n k (by omega))
  have hbound := error_le_of_polynomial_approx hab.le hf p
    (fun x hx => (hp x hx).le)
    (valueOn_eq_integral_polynomial (hexact n) p hn a b)
  rw [hw] at hbound
  rw [Real.dist_eq]
  have hcalc : (b - a) * (1 + 1) * δ = ε / 2 := by
    dsimp [δ]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  rw [hcalc] at hbound
  linarith

end
end Quadrature
