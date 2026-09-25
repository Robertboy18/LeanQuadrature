import PDE.Symbolic.Polynomial.RealRoot.Interval
import Quadrature.Legendre.Identification

/-!
# Gaussian rules from rational root certificates

A certified root bracket for a sparse rational polynomial `p` is a LeanPDE `RootBracket`, a
rational interval together with a monotonicity direction, whose decidable check `valid p`
passes. Validity certifies that `p` has exactly one root in the interval
(`RootBracket.existsUniqueRoot`). Given `n` disjoint certified brackets for a monic `p` of
degree `n`, the roots they isolate are the nodes of a Gaussian rule on `[-1, 1]` as soon as
the moments `∫_{-1}^1 p x * x^k` vanish for `k < n`, which identifies `p` with the monic
Legendre polynomial. `LegendreRootData` uses this for the rules of orders five to ten,
where the nodes have no convenient formulas in radicals.
-/

namespace Quadrature.Legendre.RootCertificates

open Polynomial Set
open PDE.Symbolic.Polynomial
open PDE.Symbolic.Polynomial.RealRoot
open PDE.Symbolic.Continuum

/-- The real polynomial denoted by a LeanPDE sparse rational polynomial, a list of
`(coefficient, exponent)` terms. -/
noncomputable def realPolynomial : Sparse.Univariate → ℝ[X]
  | [] => 0
  | term :: rest =>
      C (term.1 : ℝ) * X ^ term.2 (0 : Fin 1) + realPolynomial rest

/-- Evaluating `realPolynomial p` agrees with LeanPDE's `Sparse.evalReal`. -/
theorem eval_realPolynomial (p : Sparse.Univariate) (x : ℝ) :
    (realPolynomial p).eval x = Sparse.evalReal p x := by
  induction p with
  | nil => simp [realPolynomial, Sparse.evalReal]
  | cons term rest ih => simp [realPolynomial, Sparse.evalReal, ih]

/-- The moment `∫_{-1}^1 x^k = (1 - (-1)^(k+1)) / (k + 1)` as a rational number. -/
def moment (k : ℕ) : ℚ :=
  (1 - (-1) ^ (k + 1)) / (k + 1)

/-- The rational value of `∫_{-1}^1 p x * x^k` for a sparse polynomial `p`, computed term by
term from `moment`. -/
def shiftedMoment : Sparse.Univariate → ℕ → ℚ
  | [], _ => 0
  | term :: rest, k =>
      term.1 * moment (term.2 (0 : Fin 1) + k) + shiftedMoment rest k

/-- `∫_{-1}^1 c x^k = c * moment k`. -/
theorem integral_C_mul_X_pow (c : ℝ) (k : ℕ) :
    polynomialIntegral (-1) 1 (fun _ => 1) continuousOn_const (C c * X ^ k) =
      c * (moment k : ℝ) := by
  simp only [polynomialIntegral, LinearMap.coe_mk, AddHom.coe_mk,
    eval_mul, eval_C, eval_pow, eval_X, mul_one]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp [moment]

/-- `∫_{-1}^1 p x * x^k = shiftedMoment p k` for a sparse polynomial `p`. -/
theorem integral_realPolynomial_mul_X_pow (p : Sparse.Univariate) (k : ℕ) :
    polynomialIntegral (-1) 1 (fun _ => 1) continuousOn_const
      (realPolynomial p * X ^ k) = (shiftedMoment p k : ℝ) := by
  induction p with
  | nil => simp [realPolynomial, shiftedMoment]
  | cons term rest ih =>
      simp only [realPolynomial, add_mul, map_add, mul_assoc, ← pow_add,
        integral_C_mul_X_pow, ih, shiftedMoment, Rat.cast_add, Rat.cast_mul]

/-- If `shiftedMoment p k = 0` for all `k < n` then `realPolynomial p` is orthogonal on
`[-1, 1]` to every polynomial of degree below `n`. Expand `q` in monomials. -/
theorem orthogonal_of_shiftedMoments (p : Sparse.Univariate) (n : ℕ)
    (hmoments : ∀ k < n, shiftedMoment p k = 0)
    (q : ℝ[X]) (hq : q.natDegree < n) :
    polynomialIntegral (-1) 1 (fun _ => 1) continuousOn_const
      (realPolynomial p * q) = 0 := by
  classical
  rw [q.as_sum_range' n hq, Finset.mul_sum, map_sum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [← C_mul_X_pow_eq_monomial]
  have heq : realPolynomial p * (C (q.coeff k) * X ^ k) =
      (q.coeff k) • (realPolynomial p * X ^ k) := by
    rw [smul_eq_C_mul]
    ring
  rw [heq, map_smul, integral_realPolynomial_mul_X_pow,
    hmoments k (Finset.mem_range.mp hk)]
  simp

/-- The root isolated by each certified root bracket, one real number per bracket. Validity
of the brackets is all that is needed to define the nodes. -/
noncomputable def nodes {n : ℕ} (p : Sparse.Univariate)
    (brackets : Fin n → RootBracket)
    (hvalid : ∀ i, (brackets i).valid p = true) : Fin n → ℝ :=
  fun i => ((brackets i).existsUniqueRoot p (hvalid i)).exists.choose

/-- Each node lies in its bracket. -/
theorem nodes_mem {n : ℕ} (p : Sparse.Univariate)
    (brackets : Fin n → RootBracket)
    (hvalid : ∀ i, (brackets i).valid p = true) (i : Fin n) :
    (brackets i).interval.memReal (nodes p brackets hvalid i) :=
  ((brackets i).existsUniqueRoot p (hvalid i)).exists.choose_spec.1

/-- Each node is a root of `realPolynomial p`. -/
theorem nodes_root {n : ℕ} (p : Sparse.Univariate)
    (brackets : Fin n → RootBracket)
    (hvalid : ∀ i, (brackets i).valid p = true) (i : Fin n) :
    (realPolynomial p).IsRoot (nodes p brackets hvalid i) := by
  rw [IsRoot, eval_realPolynomial]
  exact ((brackets i).existsUniqueRoot p (hvalid i)).exists.choose_spec.2

/-- If the brackets are pairwise disjoint and listed in increasing order, the nodes are
strictly increasing. -/
theorem nodes_strictMono {n : ℕ} (p : Sparse.Univariate)
    (brackets : Fin n → RootBracket)
    (hvalid : ∀ i, (brackets i).valid p = true)
    (hordered : ∀ i j, i < j → (brackets i).interval.hi < (brackets j).interval.lo) :
    StrictMono (nodes p brackets hvalid) := by
  intro i j hij
  have hsep : ((brackets i).interval.hi : ℝ) < (brackets j).interval.lo :=
    Rat.cast_lt.mpr (hordered i j hij)
  exact (nodes_mem p brackets hvalid i).2.trans_lt
    (hsep.trans_le (nodes_mem p brackets hvalid j).1)

/-- For `n` disjoint ordered certified brackets of a monic `p` of degree `n`, the nodal
polynomial of the nodes is `realPolynomial p`. Both are monic of degree `n` and agree at the
`n` distinct nodes. -/
theorem nodal_eq {n : ℕ} (p : Sparse.Univariate)
    (brackets : Fin n → RootBracket)
    (hvalid : ∀ i, (brackets i).valid p = true)
    (hordered : ∀ i j, i < j → (brackets i).interval.hi < (brackets j).interval.lo)
    (hmonic : (realPolynomial p).Monic) (hdegree : (realPolynomial p).natDegree = n) :
    Lagrange.nodal Finset.univ (nodes p brackets hvalid) = realPolynomial p := by
  apply eq_of_degree_le_of_eval_finset_eq
    (Finset.univ.image (nodes p brackets hvalid))
  · rw [Finset.card_image_of_injective _ (nodes_strictMono p brackets hvalid hordered).injective,
      Finset.card_univ, Fintype.card_fin, Lagrange.degree_nodal, Finset.card_univ,
      Fintype.card_fin]
  · rw [Lagrange.degree_nodal, Finset.card_univ, Fintype.card_fin,
      degree_eq_natDegree hmonic.ne_zero, hdegree]
  · rw [Lagrange.nodal_monic, hmonic]
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    rw [Lagrange.eval_nodal_at_node (Finset.mem_univ _)]
    exact (nodes_root p brackets hvalid i).symm

/-- The Gaussian rule on `[-1, 1]` with nodes at the certified roots and weights the
Christoffel numbers. Needs the brackets inside `(-1, 1)`, `p` monic of degree `n`, and the
vanishing moments `shiftedMoment p k = 0` for `k < n`, which give orthogonality of the nodal
polynomial and hence positivity of the weights and exactness through degree `2n - 1`. -/
noncomputable def rule {n : ℕ} (hn : 0 < n) (p : Sparse.Univariate)
    (brackets : Fin n → RootBracket)
    (hvalid : ∀ i, (brackets i).valid p = true)
    (hordered : ∀ i j, i < j → (brackets i).interval.hi < (brackets j).interval.lo)
    (hinterior : ∀ i, -1 < (brackets i).interval.lo ∧ (brackets i).interval.hi < 1)
    (hmonic : (realPolynomial p).Monic) (hdegree : (realPolynomial p).natDegree = n)
    (hmoments : ∀ k < n, shiftedMoment p k = 0) : Rule n := by
  let r := nodes p brackets hvalid
  have hinj : Function.Injective r := (nodes_strictMono p brackets hvalid hordered).injective
  have horth : ∀ q : ℝ[X], q.natDegree < n →
      polynomialIntegral (-1) 1 (fun _ => 1) continuousOn_const
        (Lagrange.nodal Finset.univ r * q) = 0 := by
    intro q hq
    rw [nodal_eq p brackets hvalid hordered hmonic hdegree]
    exact orthogonal_of_shiftedMoments p n hmoments q hq
  exact
    { nodes := r
      weights := interpolatoryWeight
        (polynomialIntegral (-1) 1 (fun _ => 1) continuousOn_const) r
      injective := hinj
      interior := fun i => by
        have hlo : (-1 : ℝ) < (brackets i).interval.lo := by
          exact_mod_cast (hinterior i).1
        have hhi : ((brackets i).interval.hi : ℝ) < 1 := by
          exact_mod_cast (hinterior i).2
        exact ⟨hlo.trans_le (nodes_mem p brackets hvalid i).1,
          (nodes_mem p brackets hvalid i).2.trans_lt hhi⟩
      positive := integral_gaussian_weight_pos (by norm_num) _ _ (by intro x hx; norm_num)
        hn r hinj horth
      exact := gaussian_exact _ r hinj horth }

end Quadrature.Legendre.RootCertificates
