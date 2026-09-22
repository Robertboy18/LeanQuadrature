import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# A missing hypothesis in the Rocq development's integral positivity lemma

The lemma `Rintegral_gt_0` in `quadrature.v` of the Rocq development assumes continuity,
nonnegativity, and a nonzero value somewhere on the closed interval `[a, b]`, and concludes
that the integral is positive. It omits the hypothesis `a < b`. The constant function `1` on
`[0, 0]` satisfies every assumption and has integral zero, so the lemma as stated is false,
although its use on a nondegenerate interval is unaffected. Our
`polynomialIntegral_square_pos` assumes `a < b`.
-/

namespace Quadrature

open MeasureTheory Set

/-- The constant `1` on `[0, 0]` is continuous, nonnegative and nonzero, yet its integral over
`[0, 0]` is not positive. This refutes `Rintegral_gt_0` as stated. -/
theorem singleton_interval_positivity_counterexample :
    ContinuousOn (fun _ : ℝ ↦ (1 : ℝ)) (Icc (0 : ℝ) 0) ∧
      (∀ x ∈ Icc (0 : ℝ) 0, 0 ≤ (1 : ℝ)) ∧
      (¬ ∀ x ∈ Icc (0 : ℝ) 0, (1 : ℝ) = 0) ∧
      ¬ 0 < ∫ _x in Icc (0 : ℝ) 0, (1 : ℝ) := by
  refine ⟨continuousOn_const, fun _ _ ↦ zero_le_one, ?_, ?_⟩
  · intro h
    exact one_ne_zero (h 0 (by simp))
  · simp

end Quadrature
