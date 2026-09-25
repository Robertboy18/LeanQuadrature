import PDE.Symbolic.Continuum.Quadrature.Gaussian.Remainder
import Quadrature.Binary64.FiniteExecution
import Quadrature.Rules.Basic

/-!
# Accuracy for a certified stored Gaussian rule

A `CallbackContract` says the callback is finite and accurate on finite binary64
inputs in `[-1,1]`. A stored-rule certificate and a Lipschitz bound on the
integrand transfer that accuracy from the stored nodes to the exact Gaussian
nodes. Node and weight tolerances are explicit parameters, so each table uses
the tolerances proved for it. The final theorem adds the analytic Gaussian
remainder to obtain a bound against the exact integral.
-/

namespace Quadrature.Binary64

open FloatLib.Floats.Formats.BinaryInterchange PDE.Symbolic.Continuum
open scoped BigOperators

/-- For every finite binary64 input in `[-1,1]`, the callback `f` returns a finite value within
`error` of the real integrand `g` at the decoded input. -/
def CallbackContract (f : Value → Value) (g : ℝ → ℝ) (error : ℝ) : Prop :=
  ∀ x, Model.isFinite x = true → Model.toReal x ∈ Set.Icc (-1 : ℝ) 1 →
    Model.isFinite (f x) = true ∧
    |Model.toReal (f x) - g (Model.toReal x)| ≤ error

/-- If `g` is differentiable on `[-1,1]` with derivative bounded by `lipschitz` there, then `g`
is `lipschitz`-Lipschitz on `[-1,1]`, the node-sensitivity hypothesis used below. -/
theorem lipschitz_of_derivative_bound {g : ℝ → ℝ} {lipschitz : ℝ}
    (hg : DifferentiableOn ℝ g (Set.Icc (-1 : ℝ) 1))
    (hderiv : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |derivWithin g (Set.Icc (-1 : ℝ) 1) x| ≤ lipschitz) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      |g x - g y| ≤ lipschitz * |x - y| := by
  intro x hx y hy
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_derivWithin_le hg
      (fun z hz => by simpa only [Real.norm_eq_abs] using hderiv z hz) hy hx

namespace StoredRule.Certificate

variable {n : ℕ} {stored : StoredRule n} {ideal : Legendre.Rule n}
    {nodeTolerance weightTolerance : ℝ}

/-- Under a stored-rule certificate, Σ|stored weightᵢ| ≤ 2 + n·weightTolerance, since the ideal
weights are positive and sum to 2. -/
theorem sum_abs_weights_le
    (cert : stored.Certificate ideal nodeTolerance weightTolerance) (hn : 0 < n) :
    ∑ i, |Model.toReal (stored.weights i)| ≤ 2 + n * weightTolerance := by
  have hm := ideal.sum_weights hn
  norm_num [polynomialIntegral] at hm
  calc
    _ ≤ ∑ i, (ideal.weights i + weightTolerance) := by
      apply Finset.sum_le_sum
      intro i _
      have h := abs_add_le (Model.toReal (stored.weights i) - ideal.weights i)
        (ideal.weights i)
      rw [sub_add_cancel, abs_of_pos (ideal.positive i)] at h
      linarith [cert.weight_error i]
    _ = _ := by simp [Finset.sum_add_distrib, hm]

/-- Under a certificate and a callback contract, the callback at stored node i is finite and
within `error + lipschitz·nodeTolerance` of `g` at the ideal node i. -/
theorem callback_at_node (cert : stored.Certificate ideal nodeTolerance weightTolerance)
    {f : Value → Value} {g : ℝ → ℝ} {error lipschitz : ℝ}
    (hc : CallbackContract f g error) (hL : 0 ≤ lipschitz)
    (hg : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      |g x - g y| ≤ lipschitz * |x - y|) (i : Fin n) :
    Model.isFinite (f (stored.nodes i)) = true ∧
    |Model.toReal (f (stored.nodes i)) - g (ideal.nodes i)| ≤
      error + lipschitz * nodeTolerance := by
  have hc' := hc _ (cert.node_finite i) (cert.node_mem i)
  have hn := hg _ (cert.node_mem i) _
    ⟨(ideal.interior i).1.le, (ideal.interior i).2.le⟩
  have he := mul_le_mul_of_nonneg_left (cert.node_error i) hL
  exact ⟨hc'.1, (abs_sub_le _ _ _).trans (add_le_add hc'.2 (hn.trans he))⟩

/-- If |g| ≤ bound on `[-1,1]`, the absolute mass of the exact stored products is at most
`(2 + n·weightTolerance)·(bound + error)`. This is the left side of the range budget. -/
theorem product_mass_le (cert : stored.Certificate ideal nodeTolerance weightTolerance) (hn : 0 < n)
    {f : Value → Value} {g : ℝ → ℝ} {bound error : ℝ}
    (hc : CallbackContract f g error) (hB : 0 ≤ bound) (he : 0 ≤ error)
    (hg : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |g x| ≤ bound) :
    ∑ i, |Model.toReal (stored.weights i) * Model.toReal (f (stored.nodes i))| ≤
      (2 + n * weightTolerance) * (bound + error) := by
  have hsample (i : Fin n) : |Model.toReal (f (stored.nodes i))| ≤ bound + error := by
    have h := abs_add_le
      (Model.toReal (f (stored.nodes i)) - g (Model.toReal (stored.nodes i)))
      (g (Model.toReal (stored.nodes i)))
    rw [sub_add_cancel] at h
    linarith [(hc _ (cert.node_finite i) (cert.node_mem i)).2,
      hg _ (cert.node_mem i)]
  calc
    _ ≤ ∑ i, |Model.toReal (stored.weights i)| * (bound + error) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hsample i) (abs_nonneg _)
    _ = (∑ i, |Model.toReal (stored.weights i)|) * (bound + error) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (cert.sum_abs_weights_le hn) (add_nonneg hB he)

/-- The exact sum of stored products differs from the ideal rule applied to `g` by the table and
callback perturbations alone, before any arithmetic rounding. -/
theorem samples_error (cert : stored.Certificate ideal nodeTolerance weightTolerance) (hn : 0 < n)
    {f : Value → Value} {g : ℝ → ℝ} {bound error lipschitz : ℝ}
    (hc : CallbackContract f g error) (he : 0 ≤ error) (hL : 0 ≤ lipschitz)
    (hg : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |g x| ≤ bound)
    (hlip : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      |g x - g y| ≤ lipschitz * |x - y|) :
    |(∑ i, Model.toReal (stored.weights i) * Model.toReal (f (stored.nodes i))) -
        ideal.value g| ≤
      (2 + n * weightTolerance) * (error + lipschitz * nodeTolerance) +
        n * weightTolerance * bound := by
  have hsample (i : Fin n) :
      |Model.toReal (stored.weights i) * Model.toReal (f (stored.nodes i)) -
        ideal.weights i * g (ideal.nodes i)| ≤
      |Model.toReal (stored.weights i)| * (error + lipschitz * nodeTolerance) +
        weightTolerance * bound := by
    have h := weighted_sample_error (cert.weight_error i)
      (cert.callback_at_node hc hL hlip i).2
    have hi := hg _ ⟨(ideal.interior i).1.le, (ideal.interior i).2.le⟩
    exact h.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hi (cert.weight_tolerance_nonneg hn)))
  unfold GaussianRule.value
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |Model.toReal (stored.weights i) * Model.toReal (f (stored.nodes i)) -
        ideal.weights i * g (ideal.nodes i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (|Model.toReal (stored.weights i)| *
        (error + lipschitz * nodeTolerance) + weightTolerance * bound) :=
      Finset.sum_le_sum (fun i _ => hsample i)
    _ = (∑ i, |Model.toReal (stored.weights i)|) *
        (error + lipschitz * nodeTolerance) + n * weightTolerance * bound := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right (cert.sum_abs_weights_le hn)
        (add_nonneg he (mul_nonneg hL (cert.node_tolerance_nonneg hn)))) le_rfl

/-- Under a certificate, a callback contract, and a range budget, the loop result is finite and
within `2n·ε(radius)` plus the perturbation terms of `samples_error` of the ideal rule value. -/
theorem roundoff_bound (cert : stored.Certificate ideal nodeTolerance weightTolerance) (hn : 0 < n)
    {f : Value → Value} {g : ℝ → ℝ} {bound error lipschitz radius : ℝ}
    (hc : CallbackContract f g error)
    (hB : 0 ≤ bound) (he : 0 ≤ error) (hL : 0 ≤ lipschitz)
    (hg : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |g x| ≤ bound)
    (hlip : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      |g x - g y| ≤ lipschitz * |x - y|)
    (hmax : radius ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64))
    (hbudget : (2 + n * weightTolerance) * (bound + error) +
      2 * n * Model.epsilonAt FloatFormat.binary64 radius ≤ radius) :
    Model.isFinite (integrate f stored.terms) = true ∧
    |Model.toReal (integrate f stored.terms) - ideal.value g| ≤
      2 * n * Model.epsilonAt FloatFormat.binary64 radius +
        (2 + n * weightTolerance) * (error + lipschitz * nodeTolerance) +
        n * weightTolerance * bound := by
  have hf : ∀ t ∈ stored.terms,
      Model.isFinite t.1 = true ∧ Model.isFinite (f t.2) = true := by
    intro t ht
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
    exact ⟨cert.weight_finite i, (hc _ (cert.node_finite i) (cert.node_mem i)).1⟩
  have hb :
      (stored.terms.map fun t => |Model.toReal t.1 * Model.toReal (f t.2)|).sum +
        2 * stored.terms.length * Model.epsilonAt FloatFormat.binary64 radius ≤ radius := by
    simp only [StoredRule.terms, List.map_ofFn, List.sum_ofFn, List.length_ofFn]
    exact (add_le_add (cert.product_mass_le hn hc hB he hg) le_rfl).trans hbudget
  have ha := integrate_error_from_budget f stored.terms radius hmax hf hb
  simp only [StoredRule.terms, List.map_ofFn, List.sum_ofFn, List.length_ofFn] at ha
  refine ⟨ha.1, ?_⟩
  have ht := abs_sub_le (Model.toReal (integrate f stored.terms))
    (∑ i, Model.toReal (stored.weights i) * Model.toReal (f (stored.nodes i)))
    (ideal.value g)
  simpa only [add_assoc] using
    ht.trans (add_le_add ha.2 (cert.samples_error hn hc he hL hg hlip))

/-- Under a certificate, a callback contract, and a range budget, every intermediate value of
the loop is finite (`Model.ReductionTree.FiniteEval`). -/
theorem finite_execution
    (cert : stored.Certificate ideal nodeTolerance weightTolerance) (hn : 0 < n)
    {f : Value → Value} {g : ℝ → ℝ} {bound error radius : ℝ}
    (hc : CallbackContract f g error) (hB : 0 ≤ bound) (he : 0 ≤ error)
    (hg : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |g x| ≤ bound)
    (hmax : radius ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64))
    (hbudget : (2 + n * weightTolerance) * (bound + error) +
      2 * n * Model.epsilonAt FloatFormat.binary64 radius ≤ radius) :
    Model.ReductionTree.FiniteEval (integrationTree f stored.terms) := by
  apply integrationTree_finite_from_budget f stored.terms radius hmax
  · intro t ht
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
    exact ⟨cert.weight_finite i, (hc _ (cert.node_finite i) (cert.node_mem i)).1⟩
  · simp only [StoredRule.terms, List.map_ofFn, List.sum_ofFn, List.length_ofFn]
    exact (add_le_add (cert.product_mass_le hn hc hB he hg) le_rfl).trans hbudget

/-- Total error for a certified stored rule and a `2n` times differentiable integrand: the
bound of `roundoff_bound` plus the Gaussian remainder `M/(2n)! · ∫ nodal²`, where `M` bounds
the `2n`-th derivative on `[-1,1]`. -/
theorem accuracy (cert : stored.Certificate ideal nodeTolerance weightTolerance) (hn : 0 < n)
    {f : Value → Value} {g : ℝ → ℝ} {bound error lipschitz radius derivativeBound : ℝ}
    (hc : CallbackContract f g error)
    (hB : 0 ≤ bound) (he : 0 ≤ error) (hL : 0 ≤ lipschitz)
    (hg : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |g x| ≤ bound)
    (hlip : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      |g x - g y| ≤ lipschitz * |x - y|)
    (hmax : radius ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64))
    (hbudget : (2 + n * weightTolerance) * (bound + error) +
      2 * n * Model.epsilonAt FloatFormat.binary64 radius ≤ radius)
    (hsmooth : ContDiffOn ℝ (2 * n) g (Set.Icc (-1 : ℝ) 1))
    (hderiv : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |iteratedDerivWithin (2 * n) g (Set.Icc (-1 : ℝ) 1) x| ≤ derivativeBound) :
    Model.isFinite (integrate f stored.terms) = true ∧
    |Model.toReal (integrate f stored.terms) - ∫ x in (-1 : ℝ)..1, g x| ≤
      2 * n * Model.epsilonAt FloatFormat.binary64 radius +
        (2 + n * weightTolerance) * (error + lipschitz * nodeTolerance) +
        n * weightTolerance * bound +
        derivativeBound / (2 * n).factorial *
          polynomialIntegral (-1) 1 (fun _ => 1) continuousOn_const
            ((Lagrange.nodal Finset.univ ideal.nodes) ^ 2) := by
  have hr := cert.roundoff_bound hn hc hB he hL hg hlip hmax hbudget
  have hq := ideal.abs_error_le (by norm_num) (fun _ _ => by norm_num) hn hsmooth hderiv
  simp only [mul_one, abs_sub_comm (∫ x in (-1 : ℝ)..1, g x)] at hq
  exact ⟨hr.1, (abs_sub_le _ (ideal.value g) _).trans (add_le_add hr.2 hq)⟩

end StoredRule.Certificate

end Quadrature.Binary64
