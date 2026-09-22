import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Quadrature.Analysis.Algebra

/-!
# Weighted polynomial integration

`polynomialIntegral a b w hw` is the linear functional `p ↦ ∫_a^b p x * w x` on real
polynomials, for a weight `w` continuous on the interval. When `a < b` and `w` is strictly
positive, `polynomialIntegral_square_pos` shows the functional is positive on nonzero
squares, which is the hypothesis the algebraic results of `Algebra` and `Orthogonal` need.
-/

open Polynomial MeasureTheory Set

namespace Quadrature

noncomputable section

/-- The functional `p ↦ ∫_a^b p x * w x` on `ℝ[X]`, linear in `p`. -/
def polynomialIntegral (a b : ℝ) (w : ℝ → ℝ)
    (hw : ContinuousOn w (uIcc a b)) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := ∫ x in a..b, p.eval x * w x
  map_add' p q := by
    simp only [Polynomial.eval_add, add_mul]
    exact intervalIntegral.integral_add
      (p.continuous.continuousOn.mul hw).intervalIntegrable
      (q.continuous.continuousOn.mul hw).intervalIntegrable
  map_smul' c p := by
    simp only [Polynomial.eval_smul, smul_eq_mul, RingHom.id_apply, mul_assoc]
    exact intervalIntegral.integral_const_mul c _

/-- A nonzero real polynomial is nonzero at some point of `[a, b]` when `a < b`, since it has
only finitely many roots. -/
theorem exists_eval_ne_zero_in_interval {a b : ℝ} (hab : a < b)
    (p : ℝ[X]) (hp : p ≠ 0) :
    ∃ x ∈ Icc a b, p.eval x ≠ 0 := by
  by_contra! h
  apply hp
  apply Polynomial.eq_zero_of_infinite_isRoot
  exact (Set.Icc_infinite hab).mono (fun x hx => h x hx)

/-- The integral of `p ^ 2` against `w` over `[a, b]` is strictly positive when `a < b`, `w`
is continuous and strictly positive on `[a, b]`, and `p ≠ 0`. -/
theorem polynomialIntegral_square_pos {a b : ℝ} (hab : a < b) (w : ℝ → ℝ)
    (hw : ContinuousOn w (uIcc a b)) (hwpos : ∀ x ∈ Icc a b, 0 < w x)
    (p : ℝ[X]) (hp : p ≠ 0) :
    0 < polynomialIntegral a b w hw (p ^ 2) := by
  obtain ⟨x, hx, hpx⟩ := exists_eval_ne_zero_in_interval hab p hp
  have hw' : ContinuousOn w (Icc a b) := by simpa [uIcc_of_le hab.le] using hw
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := fun _ : ℝ => 0) (g := fun y => p.eval y ^ 2 * w y) hab
    continuousOn_const (p.continuous.pow 2 |>.continuousOn.mul hw')
    (fun y hy => mul_nonneg (sq_nonneg _) (hwpos y ⟨hy.1.le, hy.2⟩).le)
    ⟨x, hx, mul_pos (sq_pos_of_ne_zero hpx) (hwpos x hx)⟩
  simpa [polynomialIntegral, Polynomial.eval_pow] using h

/-- The Christoffel numbers for a continuous strictly positive weight on `[a, b]` are
positive, provided the nodal polynomial is orthogonal to every polynomial of degree below
`n`. Specializes `gaussian_weight_pos`. -/
theorem integral_gaussian_weight_pos {a b : ℝ} (hab : a < b) (w : ℝ → ℝ)
    (hw : ContinuousOn w (uIcc a b)) (hwpos : ∀ x ∈ Icc a b, 0 < w x)
    {n : ℕ} (hn : 0 < n) (nodes : Fin n → ℝ) (hnodes : Function.Injective nodes)
    (horth : ∀ q : ℝ[X], q.natDegree < n →
      polynomialIntegral a b w hw (Lagrange.nodal Finset.univ nodes * q) = 0)
    (i : Fin n) :
    0 < interpolatoryWeight (polynomialIntegral a b w hw) nodes i :=
  gaussian_weight_pos hn _ nodes hnodes horth
    (polynomialIntegral_square_pos hab w hw hwpos) i

end
end Quadrature
