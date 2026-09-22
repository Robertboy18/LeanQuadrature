import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Tree
import Quadrature.Binary64.Constants
import Quadrature.Binary64.Roundoff

/-!
# Binary64 quadrature in the C evaluation order

`integrate` performs one rounded multiplication and one rounded addition per
sample, starting from positive zero, in the order of the loop of the original C
program. It uses FloatLib's executable IEEE model. The finiteness and callback
hypotheses of the later theorems are proved from the range budget and the
cosine certificates rather than assumed.
-/

namespace Quadrature.Binary64

open FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

/-- The loop of the original C program: for each (weight, node) pair, multiply the weight by
`f node` and add the product to the accumulator, which starts at positive zero. -/
def integrate (f : Value → Value) (terms : List (Value × Value)) : Value :=
  (terms.map fun term => Model.mul term.1 (f term.2)).foldl Model.add zero

/-- The callback `0.5 * (1 - x) * cosine x`, with the left-to-right parenthesization of the
original C program. -/
def testfun (cosine : Value → Value) (x : Value) : Value :=
  Model.mul (Model.mul half (Model.sub one x)) (cosine x)

/-- The two-point rule as the loop sees it: unit weights at `leftNode` and `rightNode`. -/
def twoPointTerms : List (Value × Value) := [(one, leftNode), (one, rightNode)]

/-- Append additions to an accumulator tree in loop order. -/
def accumulationTree (initial : ReductionTree Value) : List Value → ReductionTree Value
  | [] => initial
  | x :: xs => accumulationTree (.node initial (.leaf x)) xs

/-- Evaluating an accumulation tree is a left fold, for any operation and leaf decoder. -/
theorem accumulationTree_eval_with {α : Type*}
    (op : α → α → α) (decode : Value → α)
    (initial : ReductionTree Value) (xs : List Value) :
    (accumulationTree initial xs).eval op decode =
      (xs.map decode).foldl op (initial.eval op decode) := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih => exact ih (.node initial (.leaf x))

/-- Evaluating the accumulation tree with `Model.add` is the left fold of `Model.add` over the
appended values, starting from the value of the initial tree. -/
theorem accumulationTree_eval (initial : ReductionTree Value) (xs : List Value) :
    (accumulationTree initial xs).eval Model.add id =
      xs.foldl Model.add (initial.eval Model.add id) := by
  simpa only [List.map_id] using accumulationTree_eval_with Model.add id initial xs

/-- The leaves of the accumulation tree are the initial leaves followed by the appended list. -/
theorem accumulationTree_leaves (initial : ReductionTree Value) (xs : List Value) :
    (accumulationTree initial xs).leaves = initial.leaves ++ xs := by
  induction xs generalizing initial with
  | nil => simp [accumulationTree]
  | cons x xs ih =>
    simp [accumulationTree, ih, ReductionTree.leaves, List.append_assoc]

/-- The execution tree includes the loop's initial zero and every weighted sample. -/
def integrationTree (f : Value → Value) (terms : List (Value × Value)) :
    ReductionTree Value :=
  accumulationTree (.leaf zero) (terms.map fun term => Model.mul term.1 (f term.2))

/-- Evaluating `integrationTree f terms` with `Model.add` gives `integrate f terms`. -/
theorem integrationTree_eval (f : Value → Value) (terms : List (Value × Value)) :
    (integrationTree f terms).eval Model.add id = integrate f terms :=
  accumulationTree_eval _ _

/-- The real value of positive zero is 0. -/
theorem zero_toReal : Model.toReal zero = 0 := by
  have hz : Model.toDyadic? zero = some ⟨false, 0, 0⟩ := by decide
  rw [Model.toReal_eq, hz]
  norm_num [FloatLib.Numerics.Dyadic.toReal,
    FloatLib.Numerics.Dyadic.signedSignificand]

/-- If every node of the integration tree is finite, the result differs from the exact sum of
the rounded products by at most FloatLib's `errorBudget`, the sum of half-ULPs at the
additions performed. -/
theorem integrate_roundoff_bound (f : Value → Value) (terms : List (Value × Value))
    (hfinite : Model.ReductionTree.FiniteEval (integrationTree f terms)) :
    |Model.toReal (integrate f terms) -
      (terms.map fun term => Model.toReal (Model.mul term.1 (f term.2))).sum| ≤
      Model.ReductionTree.errorBudget (integrationTree f terms) := by
  have h := Model.ReductionTree.abs_toReal_eval_sub_sum_le
    (integrationTree f terms) (by decide) hfinite
  rw [integrationTree_eval] at h
  simpa [integrationTree, accumulationTree_leaves,
    ReductionTree.leaves, List.map_map, Function.comp_def, zero_toReal] using h

/-- If the stored weight is within `ew` of the ideal weight and the callback value within `ef`
of the ideal sample, the rounded product is within one half-ULP plus `|weight|·ef + ew·|sample|`
of the ideal product. -/
theorem sample_error (weight node : Value) (f : Value → Value)
    (idealWeight idealSample ew ef : ℝ)
    (hwfinite : Model.isFinite weight = true)
    (hffinite : Model.isFinite (f node) = true)
    (hmfinite : Model.isFinite (Model.mul weight (f node)) = true)
    (hw : |Model.toReal weight - idealWeight| ≤ ew)
    (hf : |Model.toReal (f node) - idealSample| ≤ ef) :
    |Model.toReal (Model.mul weight (f node)) - idealWeight * idealSample| ≤
      Model.epsilonAt FloatFormat.binary64 (Model.toReal weight * Model.toReal (f node)) +
        |Model.toReal weight| * ef + ew * |idealSample| := by
  exact rounded_weighted_sample_error hw hf
    (Model.abs_toReal_mul_sub_le weight (f node) (by decide) hwfinite hffinite hmfinite)

/-- For `1 ≤ n ≤ 4` and `i < n`, the flattened table index `n(n−1)/2 + i` is below ten, so the
first four rules read only the first ten entries. -/
theorem table_index_lt_ten {n i : ℕ} (hn : 1 ≤ n) (hn4 : n ≤ 4) (hi : i < n) :
    n * (n - 1) / 2 + i < 10 := by
  interval_cases n <;> norm_num at * <;> omega

end Quadrature.Binary64
