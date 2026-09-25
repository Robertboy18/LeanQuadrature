import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import PDE.Symbolic.CEGA
import PDE.Symbolic.IntegrationTactic
import PDE.Symbolic.Continuum.TrigonometricTaylorBounds

/-!
# The cosine example: refuted and replaced error bounds

For `integrand x = (1 - x) cos x / 2` on `[-1, 1]` the integral is `sin 1 ≈ 0.84147`. The
two-point Gauss–Legendre rule gives `cos (1/√3) ≈ 0.83791`, so its error is
`|sin 1 - cos (1/√3)| ≈ 0.00356`. The Appel–Bindel manuscript states the exact-real error
bound `0.00223` for this example, and `0.00224` as the corollary for the C program. The exact
rule exceeds both budgets; `corrected_two_point_bound` proves the real bound `0.00356`.
The one-point rule
gives `1`, so its error is `1 - sin 1 ≈ 0.1585`: the manuscript's `0.02` is false and
`corrected_one_point_bound` proves `0.159`. Finally `x ^ 4` has two-point error `8/45`
while its sixth derivative vanishes identically, so no two-point error bound can be
proportional to a bound on the sixth derivative (`sixth_derivative_bound_impossible`).
These are statements about the exact real rules. Rounding is handled in `Rules/Accuracy`, and
the C programs in `CSource` and the Clight modules.
-/

open MeasureTheory

namespace Quadrature.Example

noncomputable section

/-- The cosine example of the manuscript, `(1 - x) cos x / 2`. -/
def integrand (x : ℝ) : ℝ := (1 / 2) * (1 - x) * Real.cos x

/-- `∫_{-1}^1 integrand = sin 1`. The odd part `-x cos x / 2` integrates to zero, leaving
`∫_{-1}^1 cos x / 2`. -/
theorem integral_eq :
    (∫ x in (-1 : ℝ)..1, integrand x) = Real.sin 1 := by
  unfold integrand
  cas [integrate]

/-- The one-point rule on `[-1, 1]` gives `2 * integrand 0 = 1`. -/
theorem one_point_eq : 2 * integrand 0 = 1 := by
  norm_num [integrand]

/-- The two-point rule gives `cos (1/√3)`, the odd part cancelling by symmetry. -/
theorem two_point_eq :
    integrand (-(1 / Real.sqrt 3)) + integrand (1 / Real.sqrt 3) =
      Real.cos (1 / Real.sqrt 3) := by
  simp only [integrand, Real.cos_neg]
  ring

private theorem gauss_node_sq : (1 / Real.sqrt (3 : ℝ)) ^ 2 = 1 / 3 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- `0.8414 ≤ sin 1`, a rational lower bound by interval enclosure. -/
theorem sin_one_lower : (8414 / 10000 : ℝ) ≤ Real.sin 1 := by
  have h (x : ℝ) (h0 : 1 ≤ x) (h1 : x ≤ 1) :
      (8414 / 10000 : ℝ) ≤ Real.sin x := by
    cega (prec := 20) [enclose x in [1, 1]] (sin x)
  exact h 1 le_rfl le_rfl

/-- `cos (1/√3) ≤ 0.838`, from LeanPDE's degree-4 upper Taylor polynomial for `cos` evaluated
at `x ^ 2 = 1/3`. -/
theorem cos_node_upper : Real.cos (1 / Real.sqrt 3) ≤ (838 / 1000 : ℝ) := by
  have hf : (1 / Real.sqrt (3 : ℝ)) ^ 4 = 1 / 9 := by
    calc
      _ = ((1 / Real.sqrt (3 : ℝ)) ^ 2) ^ 2 := by ring
      _ = 1 / 9 := by rw [gauss_node_sq]; norm_num
  have h := PDE.Symbolic.Continuum.cos_le_taylor_four (1 / Real.sqrt 3)
  rw [gauss_node_sq, hf] at h
  linarith

/-- The exact two-point error exceeds `0.00224`, the error budget the manuscript states for
the C program. From `sin 1 ≥ 0.8414` and `cos (1/√3) ≤ 0.838` the error is at least
`0.0034`. -/
theorem paper_two_point_bound_false :
    ¬ |(∫ x in (-1 : ℝ)..1, integrand x) -
      (integrand (-(1 / Real.sqrt 3)) + integrand (1 / Real.sqrt 3))| ≤
      (224 / 100000 : ℝ) := by
  rw [integral_eq, two_point_eq]
  have h := le_abs_self (Real.sin 1 - Real.cos (1 / Real.sqrt 3))
  have hs := sin_one_lower
  have hc := cos_node_upper
  linarith

/-- The exact two-point error also exceeds `0.00223`, the exact-real bound the manuscript
states. -/
theorem paper_two_point_analytic_bound_false :
    ¬ |(∫ x in (-1 : ℝ)..1, integrand x) -
      (integrand (-(1 / Real.sqrt 3)) + integrand (1 / Real.sqrt 3))| ≤
      (223 / 100000 : ℝ) := by
  intro h
  exact paper_two_point_bound_false (h.trans (by norm_num))

/-- `sin 1 ≤ 0.8414711`, from the degree-9 Taylor polynomial `sin_le_taylor_nine`. -/
theorem sin_one_upper : Real.sin 1 ≤ (8414711 / 10000000 : ℝ) := by
  have h := PDE.Symbolic.Continuum.sin_le_taylor_nine (x := 1) (by norm_num)
  norm_num at h ⊢
  linarith

/-- The one-point error `1 - sin 1 ≈ 0.1585` exceeds the manuscript's bound `0.02`. -/
theorem paper_one_point_bound_false :
    ¬ |(∫ x in (-1 : ℝ)..1, integrand x) - 2 * integrand 0| ≤ (2 / 100 : ℝ) := by
  rw [integral_eq, one_point_eq]
  intro h
  have hl := (abs_le.mp h).1
  linarith [sin_one_upper]

/-- The one-point error is at most `0.159`, replacing the manuscript's `0.02`. -/
theorem corrected_one_point_bound :
    |(∫ x in (-1 : ℝ)..1, integrand x) - 2 * integrand 0| ≤ (159 / 1000 : ℝ) := by
  rw [integral_eq, one_point_eq, abs_le]
  constructor
  · linarith [sin_one_lower]
  · linarith [sin_one_upper]

/-- `0.8379115 ≤ cos (1/√3)`, from LeanPDE's degree-6 lower Taylor polynomial for `cos`
evaluated at `x ^ 2 = 1/3`. -/
theorem cos_node_lower : (8379115 / 10000000 : ℝ) ≤ Real.cos (1 / Real.sqrt 3) := by
  have hf : (1 / Real.sqrt (3 : ℝ)) ^ 4 = 1 / 9 := by
    calc
      _ = ((1 / Real.sqrt (3 : ℝ)) ^ 2) ^ 2 := by ring
      _ = 1 / 9 := by rw [gauss_node_sq]; norm_num
  have hsi : (1 / Real.sqrt (3 : ℝ)) ^ 6 = 1 / 27 := by
    calc
      _ = ((1 / Real.sqrt (3 : ℝ)) ^ 2) ^ 3 := by ring
      _ = 1 / 27 := by rw [gauss_node_sq]; norm_num
  have h := PDE.Symbolic.Continuum.taylor_six_le_cos (1 / Real.sqrt 3)
  rw [gauss_node_sq, hf, hsi] at h
  linarith

/-- The two-point error is at most `0.00356`, replacing the manuscript's `0.00223`. Both
`sin 1` and `cos (1/√3)` are enclosed to about seven digits. -/
theorem corrected_two_point_bound :
    |(∫ x in (-1 : ℝ)..1, integrand x) -
      (integrand (-(1 / Real.sqrt 3)) + integrand (1 / Real.sqrt 3))| ≤
      (356 / 100000 : ℝ) := by
  rw [integral_eq, two_point_eq, abs_of_nonneg]
  · linarith [sin_one_upper, cos_node_lower]
  · linarith [sin_one_lower, cos_node_upper]

/-- The two-point rule has error exactly `8/45` on `x ^ 4`: the integral is `2/5` and the
rule gives `2/9`. -/
theorem quartic_two_point_error :
    (∫ x in (-1 : ℝ)..1, x ^ 4) -
      ((-(1 / Real.sqrt 3)) ^ 4 + (1 / Real.sqrt 3) ^ 4) = (8 / 45 : ℝ) := by
  have hi : (∫ x in (-1 : ℝ)..1, x ^ 4) = 2 / 5 := by cas [integrate]
  rw [hi]
  calc
    _ = 2 / 5 - 2 * ((1 / Real.sqrt (3 : ℝ)) ^ 2) ^ 2 := by ring
    _ = 8 / 45 := by rw [gauss_node_sq]; norm_num

/-- The sixth derivative of `x ^ 4` is identically zero. -/
theorem quartic_sixth_derivative (x : ℝ) :
    iteratedDeriv 6 (fun y : ℝ => y ^ 4) x = 0 := by
  simp [iteratedDeriv_pow, Nat.descFactorial]

/-- No constant `C` bounds the two-point error by `C * M` whenever `M` bounds the absolute
sixth derivative on `[-1, 1]`. The quartic `x ^ 4` has sixth derivative bounded by `M = 0`
and error `8/45`, refuting the manuscript's pairing of two nodes with six derivatives. -/
theorem sixth_derivative_bound_impossible (C : ℝ) :
    ¬ (∀ (f : ℝ → ℝ) (M : ℝ), ContDiff ℝ 6 f → 0 ≤ M →
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |iteratedDeriv 6 f x| ≤ M) →
      |(∫ x in (-1 : ℝ)..1, f x) -
        (f (-(1 / Real.sqrt 3)) + f (1 / Real.sqrt 3))| ≤ C * M) := by
  intro h
  have hq := h (fun x => x ^ 4) 0 (by fun_prop) le_rfl
    (fun x _ => by simp only [quartic_sixth_derivative, abs_zero, le_refl])
  rw [quartic_two_point_error] at hq
  norm_num at hq

end

end Quadrature.Example
