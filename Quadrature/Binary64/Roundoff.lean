import FloatLib.Numerics.Reduction.Error
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Composing quadrature errors along a reduction schedule

The total error of a rounded quadrature sum splits into three parts: the analytic error of
the exact rule, the perturbation of each weighted sample, and the rounding at the additions
performed. FloatLib bounds the last part for any reduction tree. The sample lemmas are real
inequalities that do not depend on the reduction schedule.
-/

namespace Quadrature

open FloatLib.Numerics

/-- If each leaf value is within `error a` of its ideal, the exact sums over the tree differ by
at most the sum of the leaf errors. -/
theorem reduction_perturbation_bound {α : Type*} (t : ReductionTree α)
    (actual ideal error : α → ℝ)
    (h : ∀ a, |actual a - ideal a| ≤ error a) :
    |t.eval (· + ·) actual - t.eval (· + ·) ideal| ≤
      t.eval (· + ·) error := by
  induction t with
  | leaf a => exact h a
  | node a b ha hb =>
    simp only [ReductionTree.eval]
    calc
      |(a.eval (· + ·) actual + b.eval (· + ·) actual) -
          (a.eval (· + ·) ideal + b.eval (· + ·) ideal)| =
          |(a.eval (· + ·) actual - a.eval (· + ·) ideal) +
            (b.eval (· + ·) actual - b.eval (· + ·) ideal)| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add ha hb)

/-- The rounded reduction is within the rounding budget plus the summed sample errors plus the
analytic error of the exact rule. No relative-error assumption on the final sum is made, so
cancellation is allowed. -/
theorem total_error_bound {α β : Type*} (t : ReductionTree α)
    (combine : β → β → β) (value : α → β) (interpret : β → ℝ)
    (allowance : β → β → ℝ) (ideal sampleError : α → ℝ)
    (integral analyticError : ℝ)
    (hadd : t.AllNodes combine value (fun x y =>
      |interpret (combine x y) - (interpret x + interpret y)| ≤ allowance x y))
    (hsample : ∀ a, |interpret (value a) - ideal a| ≤ sampleError a)
    (hanalytic : |t.eval (· + ·) ideal - integral| ≤ analyticError) :
    |interpret (t.eval combine value) - integral| ≤
      t.errorBudget combine value allowance +
        t.eval (· + ·) sampleError + analyticError := by
  have hround := t.abs_eval_sub_exact_le_errorBudget combine value interpret allowance hadd
  have hs := reduction_perturbation_bound t (interpret ∘ value) ideal sampleError hsample
  have htri₁ := abs_sub_le (interpret (t.eval combine value))
    (t.eval (· + ·) (interpret ∘ value)) (t.eval (· + ·) ideal)
  have htri₂ := abs_sub_le (interpret (t.eval combine value))
    (t.eval (· + ·) ideal) integral
  linarith

/-- If the weight is perturbed by at most `ew` and the sample by at most `ef`, the exact product
is perturbed by at most `|roundedWeight|·ef + ew·|sample|`. The sample error can in turn
include node displacement and callback evaluation. -/
theorem weighted_sample_error {weight roundedWeight sample roundedSample ew ef : ℝ}
    (hw : |roundedWeight - weight| ≤ ew)
    (hf : |roundedSample - sample| ≤ ef) :
    |roundedWeight * roundedSample - weight * sample| ≤
      |roundedWeight| * ef + ew * |sample| := by
  calc
    |roundedWeight * roundedSample - weight * sample| =
        |roundedWeight * (roundedSample - sample) +
          (roundedWeight - weight) * sample| := by congr 1; ring
    _ ≤ |roundedWeight * (roundedSample - sample)| +
        |(roundedWeight - weight) * sample| := abs_add_le _ _
    _ = |roundedWeight| * |roundedSample - sample| +
        |roundedWeight - weight| * |sample| := by rw [abs_mul, abs_mul]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left hf (abs_nonneg _))
      (mul_le_mul_of_nonneg_right hw (abs_nonneg _))

/-- If in addition the computed product is within `em` of the exact product of the perturbed
factors, the computed product is within `em + |roundedWeight|·ef + ew·|sample|` of the ideal. -/
theorem rounded_weighted_sample_error
    {weight roundedWeight sample roundedSample result ew ef em : ℝ}
    (hw : |roundedWeight - weight| ≤ ew)
    (hf : |roundedSample - sample| ≤ ef)
    (hm : |result - roundedWeight * roundedSample| ≤ em) :
    |result - weight * sample| ≤
      em + |roundedWeight| * ef + ew * |sample| := by
  have h := weighted_sample_error hw hf
  have ht := abs_sub_le result (roundedWeight * roundedSample) (weight * sample)
  linarith

end Quadrature
