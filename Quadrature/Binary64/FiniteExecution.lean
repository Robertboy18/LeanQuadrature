import Quadrature.Binary64.FunctionalAccuracy

/-!
# Finite intermediate values and rounded real semantics

Under the range budget every intermediate value of the loop is finite
(`Model.ReductionTree.FiniteEval`), and the decoded result equals the real fold
with one nearest-even rounding per operation. Finiteness covers every product
and every partial sum, including the initial positive zero, so FloatLib's
`FiniteEval` certificate is proved from the budget rather than assumed.
-/

namespace Quadrature.Binary64

open FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

/-- Under the range budget every weighted product `Model.mul t.1 (f t.2)` is finite. One exact
product is at most the whole absolute mass, which lies inside the radius. -/
theorem weighted_product_finite_from_budget (f : Value → Value)
    (terms : List (Value × Value)) (radius : ℝ)
    (hmax : radius ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64))
    (hfinite : ∀ t ∈ terms,
      Model.isFinite t.1 = true ∧ Model.isFinite (f t.2) = true)
    (hbudget :
      (terms.map fun t => |Model.toReal t.1 * Model.toReal (f t.2)|).sum +
        2 * terms.length * Model.epsilonAt FloatFormat.binary64 radius ≤ radius)
    (t : Value × Value) (ht : t ∈ terms) :
    Model.isFinite (Model.mul t.1 (f t.2)) = true := by
  have he := epsilonAt_nonneg radius
  have hm :
      |Model.toReal t.1 * Model.toReal (f t.2)| ≤
        (terms.map fun t => |Model.toReal t.1 * Model.toReal (f t.2)|).sum := by
    apply List.single_le_sum ?_ _ (List.mem_map.mpr ⟨t, ht, rfl⟩)
    intro x hx
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
    exact abs_nonneg _
  exact (mul_bounded hmax t.1 (f t.2) (hfinite t ht).1 (hfinite t ht).2
    (by nlinarith [mul_nonneg (Nat.cast_nonneg terms.length) he])).1

/-- Under the range budget the loop result after any prefix of the terms is finite. A prefix has
smaller mass and fewer roundings, so it satisfies the same budget. -/
theorem integrate_take_finite_from_budget (f : Value → Value)
    (terms : List (Value × Value)) (radius : ℝ)
    (hmax : radius ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64))
    (hfinite : ∀ t ∈ terms,
      Model.isFinite t.1 = true ∧ Model.isFinite (f t.2) = true)
    (hbudget :
      (terms.map fun t => |Model.toReal t.1 * Model.toReal (f t.2)|).sum +
        2 * terms.length * Model.epsilonAt FloatFormat.binary64 radius ≤ radius)
    (n : ℕ) :
    Model.isFinite (integrate f (terms.take n)) = true := by
  have he := epsilonAt_nonneg radius
  have htail : 0 ≤ ((terms.drop n).map
      fun t => |Model.toReal t.1 * Model.toReal (f t.2)|).sum :=
    List.sum_nonneg (by
      intro x hx
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
      exact abs_nonneg _)
  have hmass :
      ((terms.take n).map fun t => |Model.toReal t.1 * Model.toReal (f t.2)|).sum ≤
        (terms.map fun t => |Model.toReal t.1 * Model.toReal (f t.2)|).sum := by
    conv_rhs => rw [← List.take_append_drop n terms]
    rw [List.map_append, List.sum_append]
    exact le_add_of_nonneg_right htail
  have hlength : ((terms.take n).length : ℝ) ≤ terms.length := by
    simp only [List.length_take]
    exact_mod_cast Nat.min_le_right n terms.length
  exact (integrate_error_from_budget f (terms.take n) radius hmax
    (fun t ht => hfinite t (List.mem_of_mem_take ht))
    ((add_le_add hmass
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlength (by norm_num)) he)).trans hbudget)).1

private theorem accumulationTree_finite_of_prefixes
    (initial : ReductionTree Value) (xs : List Value)
    (hinit : Model.ReductionTree.FiniteEval initial)
    (hfinite : ∀ x ∈ xs, Model.isFinite x = true)
    (hprefix : ∀ n, Model.isFinite
      ((xs.take n).foldl Model.add (initial.eval Model.add id)) = true) :
    Model.ReductionTree.FiniteEval (accumulationTree initial xs) := by
  induction xs generalizing initial with
  | nil => exact hinit
  | cons x xs ih =>
    apply ih (.node initial (.leaf x))
    · exact ⟨hinit, hfinite x (by simp), hprefix 1⟩
    · intro y hy
      exact hfinite y (List.mem_cons_of_mem x hy)
    · intro n
      exact hprefix (n + 1)

/-- Under the range budget every node of `integrationTree f terms` evaluates to a finite value.
The leaves are the initial zero and the products, and the inner nodes are the partial sums. -/
theorem integrationTree_finite_from_budget (f : Value → Value)
    (terms : List (Value × Value)) (radius : ℝ)
    (hmax : radius ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64))
    (hfinite : ∀ t ∈ terms,
      Model.isFinite t.1 = true ∧ Model.isFinite (f t.2) = true)
    (hbudget :
      (terms.map fun t => |Model.toReal t.1 * Model.toReal (f t.2)|).sum +
        2 * terms.length * Model.epsilonAt FloatFormat.binary64 radius ≤ radius) :
    Model.ReductionTree.FiniteEval (integrationTree f terms) := by
  apply accumulationTree_finite_of_prefixes (.leaf zero)
  · exact zero_finite
  · intro p hp
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
    exact weighted_product_finite_from_budget f terms radius hmax hfinite hbudget t ht
  · intro n
    simpa only [← List.map_take, integrate, ReductionTree.eval, id_eq] using
      integrate_take_finite_from_budget f terms radius hmax hfinite hbudget n

/-- Under the range budget the real value of `integrate f terms` is the left fold from 0 of
nearest-even rounded additions over the nearest-even rounded exact products. FloatLib's
`toReal_eval` gives this once every intermediate value is known to be finite. -/
theorem integrate_toReal_from_budget (f : Value → Value)
    (terms : List (Value × Value)) (radius : ℝ)
    (hmax : radius ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64))
    (hfinite : ∀ t ∈ terms,
      Model.isFinite t.1 = true ∧ Model.isFinite (f t.2) = true)
    (hbudget :
      (terms.map fun t => |Model.toReal t.1 * Model.toReal (f t.2)|).sum +
        2 * terms.length * Model.epsilonAt FloatFormat.binary64 radius ≤ radius) :
    Model.toReal (integrate f terms) =
      (terms.map fun t =>
        Model.roundAt FloatFormat.binary64 (Model.toReal t.1 * Model.toReal (f t.2))).foldl
          (fun x y => Model.roundAt FloatFormat.binary64 (x + y)) 0 := by
  have ht := Model.ReductionTree.toReal_eval (integrationTree f terms) (by decide)
    (integrationTree_finite_from_budget f terms radius hmax hfinite hbudget)
  rw [integrationTree_eval] at ht
  rw [ht, integrationTree, accumulationTree_eval_with]
  simp only [ReductionTree.eval, zero_toReal, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro t ht
  exact Model.toReal_mul_eq_roundAt _ _ (by decide) (hfinite t ht).1 (hfinite t ht).2
    (weighted_product_finite_from_budget f terms radius hmax hfinite hbudget t ht)

end Quadrature.Binary64
