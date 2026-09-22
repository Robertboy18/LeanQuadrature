import PDE.Symbolic.Continuum.TrigonometricTaylorBounds

/-!
# Alternating Taylor bounds for sine and cosine

For `x ≥ 0` the Taylor polynomials of `sin` and `cos` alternate around the function: the
degree-7 polynomial lies below `sin x`, the degree-8 polynomial above `cos x`, and the
degree-9 polynomial above `sin x`. Each bound follows from the previous one, since the
difference is monotone on `[0, ∞)`, starting from LeanPDE's `Real.taylor_six_le_cos`.
`Example` uses `sin_le_taylor_nine` at `x = 1` to bound `sin 1` from above, alongside
LeanPDE's cosine polynomials at `x = 1/√3`, to settle the cosine example there.
-/

namespace Quadrature

open Real

/-- For `x ≥ 0`, `x - x³/6 + x⁵/120 - x⁷/5040 ≤ sin x`. The difference is monotone on
`[0, ∞)` because its derivative is `cos x` minus the degree-6 polynomial, which is
nonnegative by `taylor_six_le_cos`. -/
theorem taylor_seven_le_sin {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ sin x := by
  let f : ℝ → ℝ := fun t ↦ sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040)
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t _
    have hd : deriv f t = cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720) := by
      simp (disch := fun_prop) [f]
      ring
    rw [hd]
    linarith [taylor_six_le_cos t]
  have h := hm (by simp) hx hx
  simpa [f] using h

/-- For `x ≥ 0`, `cos x ≤ 1 - x²/2 + x⁴/24 - x⁶/720 + x⁸/40320`. Integrate
`taylor_seven_le_sin` from `0`. -/
theorem cos_le_taylor_eight {x : ℝ} (hx : 0 ≤ x) :
    cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 := by
  let f : ℝ → ℝ := fun t ↦
    1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - cos t
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    have ht' : 0 ≤ t := by simpa using interior_subset ht
    have hd : deriv f t = sin t - (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040) := by
      simp (disch := fun_prop) [f]
      ring
    rw [hd]
    linarith [taylor_seven_le_sin ht']
  have h := hm (by simp) hx hx
  simpa [f] using h

/-- For `x ≥ 0`, `sin x ≤ x - x³/6 + x⁵/120 - x⁷/5040 + x⁹/362880`. Integrate
`cos_le_taylor_eight` from `0`. At `x = 1` this gives `sin 1 ≤ 0.8414711` in
`Example.sin_one_upper`. -/
theorem sin_le_taylor_nine {x : ℝ} (hx : 0 ≤ x) :
    sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 := by
  let f : ℝ → ℝ := fun t ↦
    t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 - sin t
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    have ht' : 0 ≤ t := by simpa using interior_subset ht
    have hd : deriv f t =
        1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 - cos t := by
      simp (disch := fun_prop) [f]
      ring
    rw [hd]
    linarith [cos_le_taylor_eight ht']
  have h := hm (by simp) hx hx
  simpa [f] using h

end Quadrature
