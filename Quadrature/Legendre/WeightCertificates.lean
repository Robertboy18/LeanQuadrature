import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Quadrature.Legendre.RootCertificates

/-!
# Weight enclosures from isolated roots

At a simple root `r` of the nodal polynomial `p`, the Lagrange cardinal polynomial is
`(p / (X - C r)) / p'(r)`, so the Christoffel number at `r` is `∫_{-1}^1 p / (X - r)` divided
by `p'(r)`. Synthetic division writes the numerator as a polynomial in `r` with rational
coefficients, so the weight is a rational function of that one root. Interval arithmetic
over the root's certified bracket then encloses the weight without reference to the other
nodes.
-/

namespace Quadrature.Legendre.RootCertificates

open Polynomial Set
open PDE.Symbolic.Polynomial
open PDE.Symbolic.Polynomial.RealRoot
open PDE.Symbolic.Continuum

/-- The divided difference `(X^k - r^k) / (X - r) = ∑_{i < k} X^i r^(k-1-i)`, written
without division. -/
noncomputable def dividedPower (k : ℕ) (r : ℝ) : ℝ[X] :=
  ∑ i ∈ Finset.range k, X ^ i * C (r ^ (k - 1 - i))

/-- `(X - r) * dividedPower k r = X^k - r^k`. -/
theorem mul_dividedPower (k : ℕ) (r : ℝ) :
    (X - C r) * dividedPower k r = X ^ k - C (r ^ k) := by
  simpa [dividedPower] using (Commute.all (X : ℝ[X]) (C r)).mul_geom_sum₂ k

/-- Synthetic division of a sparse polynomial `p` by `X - r`, term by term through
`dividedPower`. -/
noncomputable def quotient : Sparse.Univariate → ℝ → ℝ[X]
  | [], _ => 0
  | term :: rest, r =>
      C (term.1 : ℝ) * dividedPower (term.2 (0 : Fin 1)) r + quotient rest r

/-- `(X - r) * quotient p r = p - p(r)`, the division identity with remainder `p(r)`. -/
theorem mul_quotient (p : Sparse.Univariate) (r : ℝ) :
    (X - C r) * quotient p r = realPolynomial p - C (Sparse.evalReal p r) := by
  induction p with
  | nil => simp [quotient, realPolynomial, Sparse.evalReal]
  | cons term rest ih =>
      calc
        (X - C r) * quotient (term :: rest) r =
            C (term.1 : ℝ) * ((X - C r) * dividedPower (term.2 0) r) +
              (X - C r) * quotient rest r := by simp only [quotient]; ring
        _ = realPolynomial (term :: rest) - C (Sparse.evalReal (term :: rest) r) := by
          rw [mul_dividedPower, ih]
          simp only [realPolynomial, Sparse.evalReal, map_add, map_mul, map_pow]
          ring

/-- When `r` is a root of `p`, `quotient p r` is the exact polynomial quotient `p / (X - r)`. -/
theorem quotient_eq_div {p : Sparse.Univariate} {r : ℝ}
    (hroot : Sparse.evalReal p r = 0) :
    quotient p r = realPolynomial p / (X - C r) := by
  have h := mul_quotient p r
  rw [hroot, map_zero, sub_zero] at h
  rw [← h, mul_div_cancel_left₀ _ (X_sub_C_ne_zero r)]

/-- A sparse polynomial in `r` whose value at `r` is `∫_{-1}^1 quotient p r`, obtained by
integrating each term `X^i r^(k-1-i)` of the synthetic quotient. -/
def integratedQuotient : Sparse.Univariate → Sparse.Univariate
  | [] => []
  | term :: rest =>
      (List.range (term.2 (0 : Fin 1))).map
        (fun k => (term.1 * moment k, fun _ => term.2 (0 : Fin 1) - 1 - k)) ++
          integratedQuotient rest

private theorem evalReal_append (p q : Sparse.Univariate) (r : ℝ) :
    Sparse.evalReal (p ++ q) r = Sparse.evalReal p r + Sparse.evalReal q r := by
  induction p with
  | nil => simp [Sparse.evalReal]
  | cons term rest ih => simp [Sparse.evalReal, ih, add_assoc]

private theorem evalReal_map {α : Type*} (l : List α) (f : α → ℚ) (g : α → ℕ) (r : ℝ) :
    Sparse.evalReal (l.map fun a => (f a, fun _ => g a)) r =
      (l.map fun a => (f a : ℝ) * r ^ g a).sum := by
  induction l with
  | nil => simp [Sparse.evalReal]
  | cons a l ih => simp [Sparse.evalReal, ih]

/-- `∫_{-1}^1 quotient p r` equals `integratedQuotient p` evaluated at `r`. -/
theorem integral_quotient (p : Sparse.Univariate) (r : ℝ) :
    polynomialIntegral (-1) 1 (fun _ => 1) continuousOn_const (quotient p r) =
      Sparse.evalReal (integratedQuotient p) r := by
  induction p with
  | nil => simp [quotient, integratedQuotient, Sparse.evalReal]
  | cons term rest ih =>
      simp only [quotient, map_add, ← smul_eq_C_mul, map_smul, ih,
        integratedQuotient, evalReal_append, evalReal_map]
      congr 1
      rw [dividedPower, map_sum]
      simp_rw [mul_comm (X ^ _), integral_C_mul_X_pow]
      rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range,
        smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [Rat.cast_mul]
      ring

/-- The derivative of `realPolynomial p` at `r` equals LeanPDE's sparse derivative
`Sparse.derivativeRaw p` evaluated at `r`. -/
theorem eval_derivative_realPolynomial (p : Sparse.Univariate) (r : ℝ) :
    (realPolynomial p).derivative.eval r = Sparse.evalReal (Sparse.derivativeRaw p) r := by
  have heq : (realPolynomial p).eval = Sparse.evalReal p :=
    funext (eval_realPolynomial p)
  exact ((realPolynomial p).hasDerivAt r).unique
    (heq ▸ Sparse.hasDerivAt_evalRealRaw p r)

/-- When the nodal polynomial is `realPolynomial p`, the Christoffel number at node `i` is
`(integratedQuotient p)(rᵢ) / p'(rᵢ)`, a rational function of the single node `rᵢ`. -/
theorem interpolatoryWeight_eq_quotient {n : ℕ} (p : Sparse.Univariate)
    (r : Fin n → ℝ) (hnodal : Lagrange.nodal Finset.univ r = realPolynomial p)
    (i : Fin n) :
    interpolatoryWeight (polynomialIntegral (-1) 1 (fun _ => 1) continuousOn_const) r i =
      Sparse.evalReal (integratedQuotient p) (r i) /
        Sparse.evalReal (Sparse.derivativeRaw p) (r i) := by
  have hroot : Sparse.evalReal p (r i) = 0 := by
    rw [← eval_realPolynomial, ← hnodal]
    exact Lagrange.eval_nodal_at_node (Finset.mem_univ i)
  unfold interpolatoryWeight
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (Finset.mem_univ i),
    Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ i), hnodal,
    ← quotient_eq_div hroot, ← smul_eq_C_mul, map_smul, integral_quotient,
    eval_derivative_realPolynomial]
  simp [div_eq_mul_inv, mul_comm]

/-- A rational interval enclosing the weight: the interval quotient of the enclosures of
`integratedQuotient p` and of `p'` over the bracket, with the sign of `p'` read from the
bracket's direction. The fallback `RationalInterval.const 0` is never reached for a valid
bracket. -/
def weightInterval (p : Sparse.Univariate) (bracket : RootBracket) : RationalInterval :=
  let numerator := evalInterval (integratedQuotient p) bracket.interval
  let denominator := evalInterval (Sparse.derivativeRaw p) bracket.interval
  match bracket.direction with
  | .increasing =>
      if h : 0 < denominator.lo then
        numerator.divPositive denominator h
      else RationalInterval.const 0
  | .decreasing =>
      if h : 0 < denominator.neg.lo then
        numerator.neg.divPositive denominator.neg h
      else RationalInterval.const 0

/-- For a valid bracket containing `r`, `weightInterval p bracket` contains
`(integratedQuotient p)(r) / p'(r)`. -/
theorem weightInterval_sound (p : Sparse.Univariate) (bracket : RootBracket)
    (hvalid : bracket.valid p = true) {r : ℝ} (hr : bracket.interval.memReal r) :
    (weightInterval p bracket).memReal
      (Sparse.evalReal (integratedQuotient p) r /
        Sparse.evalReal (Sparse.derivativeRaw p) r) := by
  have hconditions := (bracket.valid_eq_true_iff p).mp hvalid
  have hn := evalInterval_sound (integratedQuotient p) hr
  have hd := evalInterval_sound (Sparse.derivativeRaw p) hr
  cases hdir : bracket.direction with
  | increasing =>
      simp only [RootBracket.Valid, hdir] at hconditions
      simpa only [weightInterval, hdir, dite_eq_left hconditions.2.2] using
        RationalInterval.divPositive_sound hconditions.2.2 hn hd
  | decreasing =>
      simp only [RootBracket.Valid, hdir] at hconditions
      have hpos : 0 < (evalInterval (Sparse.derivativeRaw p) bracket.interval).neg.lo := by
        exact neg_pos.mpr hconditions.2.2
      simpa only [weightInterval, hdir, dite_eq_left hpos, neg_div_neg_eq] using
        RationalInterval.divPositive_sound hpos
          (RationalInterval.neg_sound hn) (RationalInterval.neg_sound hd)

/-- Each Christoffel number of the rule built from certified brackets lies in
`weightInterval p (brackets i)`. -/
theorem weight_mem {n : ℕ} (p : Sparse.Univariate) (brackets : Fin n → RootBracket)
    (hvalid : ∀ i, (brackets i).valid p = true)
    (hordered : ∀ i j, i < j → (brackets i).interval.hi < (brackets j).interval.lo)
    (hmonic : (realPolynomial p).Monic) (hdegree : (realPolynomial p).natDegree = n)
    (i : Fin n) :
    (weightInterval p (brackets i)).memReal
      (interpolatoryWeight
        (polynomialIntegral (-1) 1 (fun _ => 1) continuousOn_const)
        (nodes p brackets hvalid) i) := by
  rw [interpolatoryWeight_eq_quotient p _ (nodal_eq p brackets hvalid hordered hmonic hdegree)]
  exact weightInterval_sound p (brackets i) (hvalid i) (nodes_mem p brackets hvalid i)

end Quadrature.Legendre.RootCertificates
