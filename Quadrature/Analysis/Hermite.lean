import Mathlib.Algebra.Polynomial.Derivative
import Quadrature.Analysis.Algebra

/-!
# Hermite interpolation at distinct nodes

Given distinct nodes `x₁, …, xₙ` with prescribed values and slopes, the Hermite interpolant
is the polynomial of degree below `2n` taking those values and first derivatives at the
nodes. It is built from the squared Lagrange cardinal polynomials `ℓᵢ ^ 2`, which vanish
together with their derivatives at every other node, each multiplied by an affine factor
that fixes the value and slope at `xᵢ`. The Gaussian remainder in `Remainder` is the error
of this interpolant.
-/

namespace Quadrature

open Polynomial
open scoped BigOperators

noncomputable section

/-- The `i`th summand of the Hermite interpolant, `(vᵢ + cᵢ (X - xᵢ)) ℓᵢ ^ 2` with `cᵢ`
chosen so that the derivative at `xᵢ` is the prescribed slope. -/
def hermiteTerm {n : ℕ} (nodes : Fin n → ℝ) (values slopes : Fin n → ℝ)
    (i : Fin n) : ℝ[X] :=
  let l := Lagrange.basis Finset.univ nodes i
  (C (values i) + C (slopes i - 2 * values i * l.derivative.eval (nodes i)) *
    (X - C (nodes i))) * l ^ 2

/-- The Hermite interpolant: the polynomial of degree below `2n` with prescribed values and
first derivatives at `n` distinct nodes. -/
def hermiteInterpolant {n : ℕ} (nodes : Fin n → ℝ) (values slopes : Fin n → ℝ) :
    ℝ[X] :=
  ∑ i, hermiteTerm nodes values slopes i

/-- The `i`th Hermite term takes the prescribed value at its own node. -/
theorem hermiteTerm_eval_self {n : ℕ} (nodes : Fin n → ℝ)
    (hnodes : Function.Injective nodes) (values slopes : Fin n → ℝ) (i : Fin n) :
    (hermiteTerm nodes values slopes i).eval (nodes i) = values i := by
  simp [hermiteTerm, Lagrange.eval_basis_self (Set.injOn_of_injective hnodes)
    (Finset.mem_univ i)]

/-- The `i`th Hermite term vanishes at every other node. -/
theorem hermiteTerm_eval_of_ne {n : ℕ} (nodes : Fin n → ℝ)
    (values slopes : Fin n → ℝ) {i j : Fin n} (hij : i ≠ j) :
    (hermiteTerm nodes values slopes i).eval (nodes j) = 0 := by
  simp [hermiteTerm, Lagrange.eval_basis_of_ne hij (Finset.mem_univ j)]

/-- The derivative of the `i`th Hermite term is the prescribed slope at its own node. -/
theorem hermiteTerm_derivative_eval_self {n : ℕ} (nodes : Fin n → ℝ)
    (hnodes : Function.Injective nodes) (values slopes : Fin n → ℝ) (i : Fin n) :
    (hermiteTerm nodes values slopes i).derivative.eval (nodes i) = slopes i := by
  simp [hermiteTerm, derivative_mul, derivative_pow,
    Lagrange.eval_basis_self (Set.injOn_of_injective hnodes) (Finset.mem_univ i)]
  ring

/-- The derivative of the `i`th Hermite term vanishes at every other node. -/
theorem hermiteTerm_derivative_eval_of_ne {n : ℕ} (nodes : Fin n → ℝ)
    (values slopes : Fin n → ℝ) {i j : Fin n} (hij : i ≠ j) :
    (hermiteTerm nodes values slopes i).derivative.eval (nodes j) = 0 := by
  simp [hermiteTerm, derivative_mul, derivative_pow,
    Lagrange.eval_basis_of_ne hij (Finset.mem_univ j)]

/-- The Hermite interpolant takes the prescribed value at each node. -/
theorem hermiteInterpolant_eval {n : ℕ} (nodes : Fin n → ℝ)
    (hnodes : Function.Injective nodes) (values slopes : Fin n → ℝ) (i : Fin n) :
    (hermiteInterpolant nodes values slopes).eval (nodes i) = values i := by
  simp only [hermiteInterpolant, eval_finsetSum]
  rw [Finset.sum_eq_single i]
  · exact hermiteTerm_eval_self nodes hnodes values slopes i
  · intro j _ hji
    exact hermiteTerm_eval_of_ne nodes values slopes hji
  · simp

/-- The derivative of the Hermite interpolant takes the prescribed slope at each node. -/
theorem hermiteInterpolant_derivative_eval {n : ℕ} (nodes : Fin n → ℝ)
    (hnodes : Function.Injective nodes) (values slopes : Fin n → ℝ) (i : Fin n) :
    (hermiteInterpolant nodes values slopes).derivative.eval (nodes i) = slopes i := by
  simp only [hermiteInterpolant, derivative_sum, eval_finsetSum]
  rw [Finset.sum_eq_single i]
  · exact hermiteTerm_derivative_eval_self nodes hnodes values slopes i
  · intro j _ hji
    exact hermiteTerm_derivative_eval_of_ne nodes values slopes hji
  · simp

/-- Each Hermite term has degree below `2n`: `ℓᵢ` has degree `n - 1` and the affine factor
has degree at most one. -/
theorem hermiteTerm_natDegree_lt {n : ℕ} (hn : 0 < n) (nodes : Fin n → ℝ)
    (hnodes : Function.Injective nodes) (values slopes : Fin n → ℝ) (i : Fin n) :
    (hermiteTerm nodes values slopes i).natDegree < 2 * n := by
  have hl : (Lagrange.basis Finset.univ nodes i).natDegree = n - 1 := by
    simpa using Lagrange.natDegree_basis (Set.injOn_of_injective hnodes) (Finset.mem_univ i)
  have ha (c d z : ℝ) : (C c + C d * (X - C z)).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simp
    · exact (natDegree_C_mul_le _ _).trans (natDegree_X_sub_C_le _)
  unfold hermiteTerm
  dsimp only
  have h := natDegree_mul_le (p := C (values i) +
    C (slopes i - 2 * values i *
      (Lagrange.basis Finset.univ nodes i).derivative.eval (nodes i)) * (X - C (nodes i)))
    (q := Lagrange.basis Finset.univ nodes i ^ 2)
  rw [natDegree_pow, hl] at h
  have := ha (values i) (slopes i - 2 * values i *
    (Lagrange.basis Finset.univ nodes i).derivative.eval (nodes i)) (nodes i)
  omega

/-- The Hermite interpolant at `n ≥ 1` distinct nodes has degree below `2n`. -/
theorem hermiteInterpolant_natDegree_lt {n : ℕ} (hn : 0 < n) (nodes : Fin n → ℝ)
    (hnodes : Function.Injective nodes) (values slopes : Fin n → ℝ) :
    (hermiteInterpolant nodes values slopes).natDegree < 2 * n := by
  have h (s : Finset (Fin n)) :
      (∑ i ∈ s, hermiteTerm nodes values slopes i).natDegree < 2 * n := by
    induction s using Finset.induction_on with
    | empty => simpa using (show 0 < 2 * n by omega)
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (natDegree_add_le _ _).trans_lt
        (max_lt (hermiteTerm_natDegree_lt hn nodes hnodes values slopes i) ih)
  exact h Finset.univ

end
end Quadrature
