import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Counterexamples to two overflow helper inequalities of the Rocq development

The overflow argument in `quadmodel_accuracy.v` of the Rocq development, at revision
`e79a28dba247db9f934289bcf4e4debd5eebc884`, relies on two real inequalities that are false.
`finite_integrate_model_aux` fails at `n = 1` with function bound `2 ^ 1022`, callback error
`0` and derivative bound `0`, even though `parameter_limits` holds there
(`one_node_finiteness_helper_false`). `gauss_pt_wt_limit_aux` fails at `n = 0` with function
bound `2 ^ 1024`, since `parameter_limits` imposes nothing on the function bound at zero
nodes (`zero_node_product_helper_false`). The binary64 constants come from LAProof: unit
roundoff `u = 2 ^ -53`, absolute roundoff `η = 2 ^ -1075` and overflow threshold
`T = 2 ^ 1024`, the threshold rather than the largest finite double. The transcription keeps
the truncated natural subtraction `(n - 1 : ℕ)` of the Rocq source. Both examples refute
intermediate inequalities of the proof rather than exhibit overflowing executions.
-/

namespace Quadrature.OverflowCounterexample

noncomputable section

/-- The binary64 unit roundoff `u = 2 ^ -53`, LAProof's `default_rel`. -/
def unitRoundoff : ℝ := 1 / 2 ^ 53

/-- The binary64 absolute roundoff `η = 2 ^ -1075`, LAProof's `default_abs`. -/
def absoluteRoundoff : ℝ := 1 / 2 ^ 1075

/-- The binary64 overflow threshold `T = 2 ^ 1024`, LAProof's `fmax`. -/
def overflowThreshold : ℝ := 2 ^ 1024

/-- The Rocq development's `parameter_limits` at binary64: the admissible range of `n`,
function bound and callback error, with the truncated subtraction `(n - 1 : ℕ)`. -/
def parameterLimits (n : ℕ) (functionBound callbackError : ℝ) : Prop :=
  (1 + (n - 1 : ℕ) * (unitRoundoff / (1 + unitRoundoff))) *
    (n * ((1 + unitRoundoff / (1 + unitRoundoff)) *
      ((2 + unitRoundoff) * (functionBound + callbackError)) + absoluteRoundoff)) <
    overflowThreshold

/-- The Rocq development's per-product error expression `maxwf`. -/
def productError (functionBound derivativeBound callbackError : ℝ) : ℝ :=
  functionBound * unitRoundoff ^ 2 + 3 * functionBound * unitRoundoff +
    unitRoundoff ^ 3 * derivativeBound + 3 * unitRoundoff ^ 2 * derivativeBound +
    unitRoundoff ^ 2 * callbackError + 2 * unitRoundoff * derivativeBound +
    3 * unitRoundoff * callbackError + 2 * callbackError + absoluteRoundoff

/-- The right side of `finite_integrate_model_aux`, with `g k = (1 + u) ^ k - 1`. -/
def summationLimit (n : ℕ) : ℝ :=
  overflowThreshold / (1 + unitRoundoff) * 1 /
    (1 + n * ((1 + unitRoundoff) ^ (n - 1) - 1 + 1))

set_option exponentiation.threshold 1075 in
/-- At `n = 1` with function bound `2 ^ 1022` the parameter limits hold, yet the summation
bound of `finite_integrate_model_aux` fails. -/
theorem one_node_finiteness_helper_false :
    parameterLimits 1 (2 ^ 1022) 0 ∧
      ¬ (2 * (2 ^ 1022) + productError (2 ^ 1022) 0 0 < summationLimit 1) := by
  norm_num [parameterLimits, productError, summationLimit,
    unitRoundoff, absoluteRoundoff, overflowThreshold]

set_option exponentiation.threshold 1075 in
/-- The product helper `gauss_pt_wt_limit_aux` does hold at the `n = 1` counterexample, so
only the summation step fails there. -/
theorem one_node_product_helper_holds :
    2 * (2 ^ 1022 + 0) * (1 + unitRoundoff) + absoluteRoundoff <
      overflowThreshold := by
  norm_num [unitRoundoff, absoluteRoundoff, overflowThreshold]

set_option exponentiation.threshold 1075 in
/-- At `n = 0` the parameter limits hold for function bound `2 ^ 1024`, yet the product bound
of `gauss_pt_wt_limit_aux` fails. -/
theorem zero_node_product_helper_false :
    parameterLimits 0 overflowThreshold 0 ∧
      ¬ (2 * (overflowThreshold + 0) * (1 + unitRoundoff) + absoluteRoundoff <
        overflowThreshold) := by
  norm_num [parameterLimits, unitRoundoff, absoluteRoundoff, overflowThreshold]

end

end Quadrature.OverflowCounterexample
