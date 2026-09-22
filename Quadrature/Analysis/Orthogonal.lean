import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.RingTheory.Polynomial.DegreeLT
import Quadrature.Analysis.Integral

/-!
# Monic orthogonal polynomials

Let `L` be a linear functional on `ℝ[X]` with `L (p ^ 2) > 0` for every `p ≠ 0`. Then
`⟪p, q⟫ = L (p * q)` is an inner product, and `X ^ n` minus its orthogonal projection onto
the polynomials of degree below `n` is monic of degree `n` and orthogonal to every
polynomial of degree below `n`. This is the monic orthogonal polynomial `p_n` of `L`. For
the constant weight on `[-1, 1]` it is the monic Legendre polynomial. The construction uses
neither a three-term recurrence nor the existence of Gaussian nodes.
-/

namespace Quadrature

open Polynomial

noncomputable section

variable (L : ℝ[X] →ₗ[ℝ] ℝ)
    (hpositive : ∀ p : ℝ[X], p ≠ 0 → 0 < L (p ^ 2))

/-- The pairing `⟪p, q⟫ = L (p * q)` is an inner product on `ℝ[X]` when `L` is positive on
nonzero squares. -/
@[instance_reducible]
def momentInnerCore : InnerProductSpace.Core ℝ ℝ[X] where
  inner p q := L (p * q)
  conj_inner_symm p q := by simp [mul_comm]
  re_inner_nonneg p := by
    change 0 ≤ L (p * p)
    by_cases hp : p = 0
    · simp [hp]
    · simpa [pow_two] using (hpositive p hp).le
  add_left p q r := by simp [add_mul]
  smul_left p q c := by simp
  definite p hp := by
    by_contra hn
    have h := hpositive p hn
    simp only [pow_two] at h
    exact (ne_of_gt h) hp

include hpositive in
/-- For every `n` there is a monic polynomial of degree `n` with `L (p * q) = 0` for every
`q` of degree below `n`. Take `X ^ n` minus its orthogonal projection onto the polynomials
of degree below `n`: the difference is monic and orthogonal to every polynomial of degree
below `n`. -/
theorem exists_monic_orthogonal (n : ℕ) :
    ∃ p : ℝ[X], p.Monic ∧ p.degree = n ∧
      ∀ q : ℝ[X], q.degree < n → L (p * q) = 0 := by
  let : InnerProductSpace.Core ℝ ℝ[X] := momentInnerCore L hpositive
  let : NormedAddCommGroup ℝ[X] :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  let : InnerProductSpace ℝ ℝ[X] :=
    InnerProductSpace.ofCore (momentInnerCore L hpositive).toCore
  let projection := (degreeLT ℝ n).starProjection (X ^ n)
  have hdegree : projection.degree < n :=
    mem_degreeLT.mp ((degreeLT ℝ n).starProjection_apply_mem (X ^ n))
  refine ⟨X ^ n - projection, monic_X_pow_sub hdegree, ?_, ?_⟩
  · rw [degree_sub_eq_left_of_degree_lt (by simpa using hdegree), degree_X_pow]
  · intro q hq
    exact Submodule.starProjection_inner_eq_zero (X ^ n) q (mem_degreeLT.mpr hq)

/-- The monic orthogonal polynomial `p_n` of `L`: the monic polynomial of degree `n`
orthogonal to all polynomials of lower degree, chosen from `exists_monic_orthogonal`. -/
def orthogonalPolynomial (n : ℕ) : ℝ[X] :=
  (exists_monic_orthogonal L hpositive n).choose

/-- The monic orthogonal polynomial `p_n` is monic. -/
theorem orthogonalPolynomial_monic (n : ℕ) :
    (orthogonalPolynomial L hpositive n).Monic :=
  (exists_monic_orthogonal L hpositive n).choose_spec.1

/-- The monic orthogonal polynomial `p_n` has degree exactly `n`. -/
theorem orthogonalPolynomial_degree (n : ℕ) :
    (orthogonalPolynomial L hpositive n).degree = n :=
  (exists_monic_orthogonal L hpositive n).choose_spec.2.1

/-- The monic orthogonal polynomial `p_n` has `natDegree` equal to `n`. -/
theorem orthogonalPolynomial_natDegree (n : ℕ) :
    (orthogonalPolynomial L hpositive n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (orthogonalPolynomial_degree L hpositive n)

/-- `L (p_n * q) = 0` for every polynomial `q` of degree below `n`. -/
theorem orthogonalPolynomial_orthogonal (n : ℕ) (q : ℝ[X])
    (hq : q.degree < n) :
    L (orthogonalPolynomial L hpositive n * q) = 0 :=
  (exists_monic_orthogonal L hpositive n).choose_spec.2.2 q hq

/-- A monic polynomial of degree `n` orthogonal to every polynomial of degree below `n`
equals `p_n`. The difference has degree below `n` and is orthogonal to itself, so its
square has `L`-value zero and it vanishes by positivity. -/
theorem orthogonalPolynomial_unique (n : ℕ) (p : ℝ[X]) (hp : p.Monic)
    (hdegree : p.degree = n)
    (horth : ∀ q : ℝ[X], q.degree < n → L (p * q) = 0) :
    p = orthogonalPolynomial L hpositive n := by
  have hdiff : (p - orthogonalPolynomial L hpositive n).degree < n := by
    rw [← hdegree]
    apply degree_sub_lt_left
    · rw [orthogonalPolynomial_degree, hdegree]
    · exact hp.ne_zero
    · rw [hp, orthogonalPolynomial_monic]
  have hz : L ((p - orthogonalPolynomial L hpositive n) ^ 2) = 0 := by
    rw [pow_two, sub_mul, map_sub,
      horth _ hdiff, orthogonalPolynomial_orthogonal L hpositive n _ hdiff, sub_self]
  by_contra hne
  exact (ne_of_gt (hpositive _ (sub_ne_zero.mpr hne))) hz

/-- The monic orthogonal polynomial of degree `n` for the functional `p ↦ ∫_a^b p w`, with
`w` continuous and strictly positive on `[a, b]` and `a < b`. For `w = 1` on `[-1, 1]` this
is the monic Legendre polynomial. -/
def integralOrthogonalPolynomial (a b : ℝ) (hab : a < b) (w : ℝ → ℝ)
    (hw : ContinuousOn w (Set.uIcc a b))
    (hpositive : ∀ x ∈ Set.Icc a b, 0 < w x) (n : ℕ) : ℝ[X] :=
  orthogonalPolynomial (polynomialIntegral a b w hw)
    (polynomialIntegral_square_pos hab w hw hpositive) n

end
end Quadrature
