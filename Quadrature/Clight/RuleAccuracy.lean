import Quadrature.Clight.StoredRules
import Quadrature.Rules.Accuracy
import Quadrature.Rules.Certificates

/-!
# General-integrand accuracy for all ten original tables

The caller supplies a smooth real integrand, a binary64 callback satisfying
`CallbackContract`, and a range budget. The stored-rule certificates of all ten
tables are discharged here, so the conclusion applies to `Clight.storedTerms n`
for every `1 ≤ n ≤ 10`. The final theorem composes this with execution of the
initialized Clight library.
-/

namespace Quadrature.Binary64.StoredRule

open FloatLib.Floats.Formats.BinaryInterchange

-- Kernel evaluation comparing each certified table with the Clight stored terms, ten orders.
set_option maxRecDepth 20000 in
/-- For `n ≤ 10` the terms of the certified `table n` are exactly `Clight.storedTerms n`, by
kernel evaluation of both lists. -/
theorem table_terms (n : ℕ) (hn : n ≤ 10) :
    (table n).terms = Clight.storedTerms n := by
  interval_cases n <;> decide +kernel

/-- The nodal polynomial of the ideal rule of order `n` is the monic Legendre polynomial of
degree `n`. -/
theorem ideal_nodal_eq (n : ℕ) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    Lagrange.nodal Finset.univ (ideal n hlo hhi).nodes = Legendre.monicPolynomial n :=
  (ideal n hlo hhi).nodal_eq_integralOrthogonalPolynomial (by norm_num)
    (by intro x hx; norm_num)

/-- The total error bound for order `n`: rounding `2n·ε(radius)`, callback and table
perturbations with tolerances `6·10⁻¹⁶` and `5·10⁻¹⁶`, and the analytic Gaussian remainder. -/
noncomputable def errorBound (n : ℕ)
    (bound error lipschitz radius derivativeBound : ℝ) : ℝ :=
  2 * n * Model.epsilonAt FloatFormat.binary64 radius +
    (2 + n * (5 / 10 ^ 16)) * (error + lipschitz * (6 / 10 ^ 16)) +
    n * (5 / 10 ^ 16) * bound +
    derivativeBound / (2 * n).factorial *
      polynomialIntegral (-1) 1 (fun _ => 1) continuousOn_const
        ((Legendre.monicPolynomial n) ^ 2)

/-- For every `1 ≤ n ≤ 10`, under a callback contract and a range budget, the loop over
`Clight.storedTerms n` is finite and within `errorBound n ...` of the exact integral of `g`. -/
theorem accuracy (n : ℕ) (hlo : 1 ≤ n) (hhi : n ≤ 10)
    {f : Value → Value} {g : ℝ → ℝ} {bound error lipschitz radius derivativeBound : ℝ}
    (hc : Binary64.CallbackContract f g error)
    (hB : 0 ≤ bound) (he : 0 ≤ error) (hL : 0 ≤ lipschitz)
    (hg : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |g x| ≤ bound)
    (hlip : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      |g x - g y| ≤ lipschitz * |x - y|)
    (hmax : radius ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64))
    (hbudget : (2 + n * (5 / 10 ^ 16)) * (bound + error) +
      2 * n * Model.epsilonAt FloatFormat.binary64 radius ≤ radius)
    (hsmooth : ContDiffOn ℝ (2 * n) g (Set.Icc (-1 : ℝ) 1))
    (hderiv : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |iteratedDerivWithin (2 * n) g (Set.Icc (-1 : ℝ) 1) x| ≤ derivativeBound) :
    Model.isFinite (integrate f (Clight.storedTerms n)) = true ∧
    |Model.toReal (integrate f (Clight.storedTerms n)) - ∫ x in (-1 : ℝ)..1, g x| ≤
      errorBound n bound error lipschitz radius derivativeBound := by
  simpa only [table_terms n hhi, ideal_nodal_eq n hlo hhi, errorBound] using
    (table_certificate n hlo hhi).accuracy hlo hc hB he hL hg hlip hmax hbudget hsmooth hderiv

/-- For every `1 ≤ n ≤ 10`, under a callback contract and a range budget, every intermediate
value of the loop over `Clight.storedTerms n` is finite. -/
theorem finite_execution (n : ℕ) (hlo : 1 ≤ n) (hhi : n ≤ 10)
    {f : Value → Value} {g : ℝ → ℝ} {bound error radius : ℝ}
    (hc : Binary64.CallbackContract f g error) (hB : 0 ≤ bound) (he : 0 ≤ error)
    (hg : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |g x| ≤ bound)
    (hmax : radius ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64))
    (hbudget : (2 + n * (5 / 10 ^ 16)) * (bound + error) +
      2 * n * Model.epsilonAt FloatFormat.binary64 radius ≤ radius) :
    Model.ReductionTree.FiniteEval (integrationTree f (Clight.storedTerms n)) := by
  rw [← table_terms n hhi]
  exact (table_certificate n hlo hhi).finite_execution hlo hc hB he hg hmax hbudget

end Quadrature.Binary64.StoredRule

namespace Quadrature.Binary64.Clight

open FloatLib.Floats.Formats.BinaryInterchange ClightSource

/-- Executing the initialized Clight library with a callback that refines `f` returns a value
that is finite and within `StoredRule.errorBound` of the exact integral. This composes
`stored_callback_execution` with `StoredRule.accuracy`. -/
theorem stored_callback_execution_accuracy [CC.ExternalCalls]
    (fd : CC.FunDef) (f : Value → Value) (contract : CallbackContract fd f)
    (n : ℕ) (hlo : 1 ≤ n) (hhi : n ≤ 10)
    {g : ℝ → ℝ} {bound error lipschitz radius derivativeBound : ℝ}
    (hc : Binary64.CallbackContract f g error)
    (hB : 0 ≤ bound) (he : 0 ≤ error) (hL : 0 ≤ lipschitz)
    (hg : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |g x| ≤ bound)
    (hlip : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      |g x - g y| ≤ lipschitz * |x - y|)
    (hmax : radius ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64))
    (hbudget : (2 + n * (5 / 10 ^ 16)) * (bound + error) +
      2 * n * Model.epsilonAt FloatFormat.binary64 radius ≤ radius)
    (hsmooth : ContDiffOn ℝ (2 * n) g (Set.Icc (-1 : ℝ) 1))
    (hderiv : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |iteratedDerivWithin (2 * n) g (Set.Icc (-1 : ℝ) 1) x| ≤ derivativeBound)
    (k : CC.Cont) :
    ∃ value : Value,
      CC.StarE0 (CC.Step2 (callbackLibrary fd).globalenv)
        (storedLibraryCall (.Vptr testfunBlock (CC.Integers.Ptrofs.repr 0)) n k initialMemory)
        (.Returnstate (.Vfloat value) (CC.callCont k) initialMemory) ∧
      Model.isFinite value = true ∧
        |Model.toReal value - ∫ x in (-1 : ℝ)..1, g x| ≤
          StoredRule.errorBound n bound error lipschitz radius derivativeBound :=
  ⟨integrate f (storedTerms n), stored_callback_execution fd f contract n hhi k,
    StoredRule.accuracy n hlo hhi hc hB he hL hg hlip hmax hbudget hsmooth hderiv⟩

end Quadrature.Binary64.Clight
