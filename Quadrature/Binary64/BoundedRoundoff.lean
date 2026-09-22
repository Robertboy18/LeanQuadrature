import FloatLib.Floats.Formats.Flocq.Theory.Analysis.Ulp
import Mathlib.Algebra.Order.BigOperators.Group.List
import Quadrature.Binary64.Program
import Quadrature.Rules.Constants

/-!
# Rounding bounds for binary64 operations and reductions

A range budget is a real `radius` no larger than the largest finite binary64,
together with the inequality Σ|exact products| + 2n·ε(radius) ≤ radius, where
ε(radius) is FloatLib's local absolute rounding bound `Model.epsilonAt` at that
radius and n is the number of samples. It implies that no multiplication or
addition of the loop overflows. The operation lemmas and `fold_add_error`
consume such a budget. Every error bound is absolute, so cancellation between
positive and negative samples causes no difficulty.

The radius-8 corollaries give the concrete bound `10⁻¹⁵` used in the two-point
cosine example. They follow from the same operation bounds.
-/

namespace Quadrature.Binary64

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.Flocq FloatLib.Numerics

/-- FloatLib's local rounding bound `Model.epsilonAt` is nonnegative at every radius. -/
theorem epsilonAt_nonneg (radius : ℝ) :
    0 ≤ Model.epsilonAt FloatFormat.binary64 radius :=
  (abs_nonneg _).trans (Model.abs_roundAt_sub_le _ _)

/-- If |x| ≤ radius then nearest-even rounding moves x by at most ε(radius). The ULP is
monotone in the magnitude, so the half-ULP at the radius dominates every rounding inside it. -/
theorem round_bounded {radius x : ℝ} (hx : |x| ≤ radius) :
    |Model.roundAt FloatFormat.binary64 x - x| ≤
      Model.epsilonAt FloatFormat.binary64 radius := by
  by_cases hx0 : x = 0
  · subst x
    simpa only [Model.roundAt_zero, sub_self, abs_zero] using epsilonAt_nonneg radius
  have hm := ulp_mono_pos (β := binaryRadix)
    (fexp := Model.fexpOf FloatFormat.binary64) (abs_pos.mpr hx0) hx
  rw [ulp_abs] at hm
  exact (Model.abs_roundAt_sub_le _ _).trans
    (div_le_div_of_nonneg_right hm (by norm_num))

/-- If x and y are finite and |x + y| ≤ radius ≤ maxFinite then `Model.add x y` is finite
and within ε(radius) of the exact sum. -/
theorem add_bounded {radius : ℝ}
    (hmax : radius ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64))
    (x y : Value) (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hbound : |Model.toReal x + Model.toReal y| ≤ radius) :
    Model.isFinite (Model.add x y) = true ∧
    |Model.toReal (Model.add x y) - (Model.toReal x + Model.toReal y)| ≤
      Model.epsilonAt FloatFormat.binary64 radius := by
  have hf := Model.isFinite_add_of_abs_toReal_add_le_posMaxFinite
    x y (by decide) hx hy (hbound.trans hmax)
  refine ⟨hf, ?_⟩
  rw [Model.toReal_add_eq_roundAt x y (by decide) hx hy hf]
  exact round_bounded hbound

/-- If x and y are finite and |x − y| ≤ radius ≤ maxFinite then `Model.sub x y` is finite
and within ε(radius) of the exact difference. -/
theorem sub_bounded {radius : ℝ}
    (hmax : radius ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64))
    (x y : Value) (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hbound : |Model.toReal x - Model.toReal y| ≤ radius) :
    Model.isFinite (Model.sub x y) = true ∧
    |Model.toReal (Model.sub x y) - (Model.toReal x - Model.toReal y)| ≤
      Model.epsilonAt FloatFormat.binary64 radius := by
  have hf := Model.isFinite_sub_of_abs_toReal_sub_le_posMaxFinite
    x y (by decide) hx hy (hbound.trans hmax)
  refine ⟨hf, ?_⟩
  rw [Model.toReal_sub_eq_roundAt x y (by decide) hx hy hf]
  exact round_bounded hbound

/-- If x and y are finite and |x · y| ≤ radius ≤ maxFinite then `Model.mul x y` is finite
and within ε(radius) of the exact product. -/
theorem mul_bounded {radius : ℝ}
    (hmax : radius ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64))
    (x y : Value) (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hbound : |Model.toReal x * Model.toReal y| ≤ radius) :
    Model.isFinite (Model.mul x y) = true ∧
    |Model.toReal (Model.mul x y) - Model.toReal x * Model.toReal y| ≤
      Model.epsilonAt FloatFormat.binary64 radius := by
  have hf := Model.isFinite_mul_of_abs_mul_le_posMaxFinite
    x y (by decide) hx hy (by rw [← abs_mul]; exact hbound.trans hmax)
  refine ⟨hf, ?_⟩
  rw [Model.toReal_mul_eq_roundAt x y (by decide) hx hy hf]
  exact round_bounded hbound

/-- If |init| + Σ|xᵢ| + n·ε(radius) ≤ radius then the left fold of `Model.add` from `init`
stays finite and its total error is at most n·ε(radius). Each addition spends one ε of the
budget, so every partial sum stays inside the radius. -/
theorem fold_add_error {radius : ℝ}
    (hmax : radius ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64))
    (xs : List Value) (initial : Value) (hinit : Model.isFinite initial = true)
    (hfinite : ∀ x ∈ xs, Model.isFinite x = true)
    (hbudget : |Model.toReal initial| + (xs.map fun x => |Model.toReal x|).sum +
      xs.length * Model.epsilonAt FloatFormat.binary64 radius ≤ radius) :
    Model.isFinite (xs.foldl Model.add initial) = true ∧
    |Model.toReal (xs.foldl Model.add initial) -
      (Model.toReal initial + (xs.map Model.toReal).sum)| ≤
      xs.length * Model.epsilonAt FloatFormat.binary64 radius := by
  have he := epsilonAt_nonneg radius
  induction xs generalizing initial with
  | nil => simpa using hinit
  | cons x xs ih =>
    have htail : 0 ≤ (xs.map fun y => |Model.toReal y|).sum :=
      List.sum_nonneg (by simp)
    have hlen : 0 ≤ (xs.length : ℝ) * Model.epsilonAt FloatFormat.binary64 radius :=
      mul_nonneg (Nat.cast_nonneg _) he
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
      Nat.cast_one] at hbudget ⊢
    have hx := hfinite x (by simp)
    have ha := add_bounded hmax initial x hinit hx
      ((abs_add_le _ _).trans (by nlinarith))
    have hamag : |Model.toReal (Model.add initial x)| ≤
        |Model.toReal initial| + |Model.toReal x| +
          Model.epsilonAt FloatFormat.binary64 radius := by
      have ht := abs_add_le (Model.toReal (Model.add initial x) -
        (Model.toReal initial + Model.toReal x))
        (Model.toReal initial + Model.toReal x)
      rw [sub_add_cancel] at ht
      linarith [ha.2, abs_add_le (Model.toReal initial) (Model.toReal x)]
    have hi := ih (Model.add initial x) ha.1
      (fun y hy => hfinite y (List.mem_cons_of_mem x hy)) (by nlinarith)
    refine ⟨hi.1, ?_⟩
    change |Model.toReal (xs.foldl Model.add (Model.add initial x)) -
      (Model.toReal initial + (Model.toReal x + (xs.map Model.toReal).sum))| ≤ _
    calc
      _ = |(Model.toReal (xs.foldl Model.add (Model.add initial x)) -
          (Model.toReal (Model.add initial x) + (xs.map Model.toReal).sum)) +
          (Model.toReal (Model.add initial x) -
            (Model.toReal initial + Model.toReal x))| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hi.2 ha.2)
      _ = _ := by ring

/-- The largest finite binary64 is at least 16, so radius 8 is admissible. -/
theorem maxFinite_large : (16 : ℝ) ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64) := by
  have h : Model.toDyadic? (Model.posMaxFinite FloatFormat.binary64) =
      some ⟨false, 9007199254740991, 971⟩ := by decide
  rw [Model.toReal_eq, h]
  norm_num [Dyadic.toReal, Dyadic.signedSignificand]
  have hp : (1 : ℝ) ≤ 2 ^ (971 : ℕ) := one_le_pow₀ (by norm_num)
  change (16 : ℝ) ≤ 9007199254740991 * 2 ^ (971 : ℕ)
  exact (by norm_num : (16 : ℝ) ≤ 9007199254740991).trans
    (le_mul_of_one_le_right (by norm_num) hp)

/-- Half an ULP at 8 is `2⁻⁵⁰`, which is less than `10⁻¹⁵`. -/
private theorem epsilonAt_eight_le :
    Model.epsilonAt FloatFormat.binary64 8 ≤ (1 / 10 ^ 15 : ℝ) := by
  change ulp binaryRadix (Model.fexpOf FloatFormat.binary64) 8 / 2 ≤ _
  have hb : bpow binaryRadix (3 : ℤ) = (8 : ℝ) := by
    norm_num [bpow, binaryRadix, Radix.toReal]
  rw [← hb, ulp_bpow]
  have he : Model.fexpOf FloatFormat.binary64 (3 + 1) = -49 := by decide
  rw [he]
  norm_num [bpow, binaryRadix, Radix.toReal]

/-- Nearest-even rounding moves a real number of magnitude at most 8 by at most `10⁻¹⁵`. -/
theorem round_small {x : ℝ} (hx : |x| ≤ 8) :
    |Model.roundAt FloatFormat.binary64 x - x| ≤ (1 / 10 ^ 15 : ℝ) :=
  (round_bounded hx).trans epsilonAt_eight_le

/-- At radius 8, `add_bounded` gives finiteness and an absolute error of at most `10⁻¹⁵`. -/
theorem add_small (x y : Value) (hx : Model.isFinite x = true)
    (hy : Model.isFinite y = true) (hbound : |Model.toReal x + Model.toReal y| ≤ 8) :
    Model.isFinite (Model.add x y) = true ∧
    |Model.toReal (Model.add x y) - (Model.toReal x + Model.toReal y)| ≤
      (1 / 10 ^ 15 : ℝ) := by
  obtain ⟨hf, he⟩ := add_bounded (by linarith [maxFinite_large]) x y hx hy hbound
  exact ⟨hf, he.trans epsilonAt_eight_le⟩

/-- At radius 8, `sub_bounded` gives finiteness and an absolute error of at most `10⁻¹⁵`. -/
theorem sub_small (x y : Value) (hx : Model.isFinite x = true)
    (hy : Model.isFinite y = true) (hbound : |Model.toReal x - Model.toReal y| ≤ 8) :
    Model.isFinite (Model.sub x y) = true ∧
    |Model.toReal (Model.sub x y) - (Model.toReal x - Model.toReal y)| ≤
      (1 / 10 ^ 15 : ℝ) := by
  obtain ⟨hf, he⟩ := sub_bounded (by linarith [maxFinite_large]) x y hx hy hbound
  exact ⟨hf, he.trans epsilonAt_eight_le⟩

/-- At radius 8, `mul_bounded` gives finiteness and an absolute error of at most `10⁻¹⁵`. -/
theorem mul_small (x y : Value) (hx : Model.isFinite x = true)
    (hy : Model.isFinite y = true) (hbound : |Model.toReal x * Model.toReal y| ≤ 8) :
    Model.isFinite (Model.mul x y) = true ∧
    |Model.toReal (Model.mul x y) - Model.toReal x * Model.toReal y| ≤
      (1 / 10 ^ 15 : ℝ) := by
  obtain ⟨hf, he⟩ := mul_bounded (by linarith [maxFinite_large]) x y hx hy hbound
  exact ⟨hf, he.trans epsilonAt_eight_le⟩

end Quadrature.Binary64
