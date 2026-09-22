import Quadrature.Binary64.BoundedRoundoff

/-!
# Range and error bounds for the functional quadrature loop

The range budget of `BoundedRoundoff` is stated for the exact products of the
stored weights and the callback results. This file proves that under the budget
every multiplication and addition of `integrate` is finite and that the result
is within 2n·ε(radius) of the exact sum of products. No assumption about the
sign of the integrand or of the final sum is needed.
-/

namespace Quadrature.Binary64

open FloatLib.Floats.Formats.BinaryInterchange

/-- If |actual x − ideal x| ≤ e for every x in the list then the two sums differ by at most
n·e, where n is the length. Repeated entries count each time. -/
theorem list_sum_error {α : Type*} (xs : List α) (actual ideal : α → ℝ) (error : ℝ)
    (herror : ∀ x ∈ xs, |actual x - ideal x| ≤ error) :
    |(xs.map actual).sum - (xs.map ideal).sum| ≤ xs.length * error := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := herror x (by simp)
    have ht := ih (fun y hy => herror y (List.mem_cons_of_mem x hy))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc
      _ = |(actual x - ideal x) + ((xs.map actual).sum - (xs.map ideal).sum)| := by
        congr 1
        ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hx ht)
      _ = _ := by ring

/-- If |actual x − ideal x| ≤ e for every x in the list then Σ|actual x| ≤ Σ|ideal x| + n·e,
where n is the length. -/
theorem list_abs_mass_le {α : Type*} (xs : List α) (actual ideal : α → ℝ) (error : ℝ)
    (herror : ∀ x ∈ xs, |actual x - ideal x| ≤ error) :
    (xs.map fun x => |actual x|).sum ≤
      (xs.map fun x => |ideal x|).sum + xs.length * error := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := herror x (by simp)
    have ht := ih (fun y hy => herror y (List.mem_cons_of_mem x hy))
    have hm := abs_add_le (actual x - ideal x) (ideal x)
    rw [sub_add_cancel] at hm
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- Under the range budget `integrate f terms` is finite and within 2n·ε(radius) of the exact
sum Σ weightᵢ · f(nodeᵢ). Each product spends one ε, `list_abs_mass_le` bounds the mass of the
rounded products, and `fold_add_error` spends one more ε per addition. -/
theorem integrate_error_from_budget (f : Value → Value) (terms : List (Value × Value))
    (radius : ℝ)
    (hmax : radius ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64))
    (hfinite : ∀ t ∈ terms,
      Model.isFinite t.1 = true ∧ Model.isFinite (f t.2) = true)
    (hbudget :
      (terms.map fun t => |Model.toReal t.1 * Model.toReal (f t.2)|).sum +
        2 * terms.length * Model.epsilonAt FloatFormat.binary64 radius ≤ radius) :
    Model.isFinite (integrate f terms) = true ∧
    |Model.toReal (integrate f terms) -
      (terms.map fun t => Model.toReal t.1 * Model.toReal (f t.2)).sum| ≤
      2 * terms.length * Model.epsilonAt FloatFormat.binary64 radius := by
  let products := terms.map fun t => Model.mul t.1 (f t.2)
  let exactProduct := fun t : Value × Value => Model.toReal t.1 * Model.toReal (f t.2)
  let roundedProduct := fun t : Value × Value => Model.toReal (Model.mul t.1 (f t.2))
  let epsilon := Model.epsilonAt FloatFormat.binary64 radius
  have he : 0 ≤ epsilon := epsilonAt_nonneg radius
  have hproducts : ∀ t ∈ terms,
      Model.isFinite (Model.mul t.1 (f t.2)) = true ∧
      |roundedProduct t - exactProduct t| ≤ epsilon := by
    intro t ht
    have hm : |exactProduct t| ≤ (terms.map fun u => |exactProduct u|).sum := by
      apply List.single_le_sum ?_ _ (List.mem_map.mpr ⟨t, ht, rfl⟩)
      intro x hx
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
      exact abs_nonneg _
    apply mul_bounded hmax t.1 (f t.2) (hfinite t ht).1 (hfinite t ht).2
    dsimp only [exactProduct] at hm
    nlinarith [mul_nonneg (Nat.cast_nonneg (terms.length)) he]
  have hmass := list_abs_mass_le terms roundedProduct exactProduct epsilon
    (fun t ht => (hproducts t ht).2)
  have hsum := list_sum_error terms roundedProduct exactProduct epsilon
    (fun t ht => (hproducts t ht).2)
  have hf : ∀ p ∈ products, Model.isFinite p = true := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
    exact (hproducts t ht).1
  have hb : |Model.toReal zero| + (products.map fun p => |Model.toReal p|).sum +
      products.length * epsilon ≤ radius := by
    simp only [zero_toReal, abs_zero, zero_add, products, List.map_map, List.length_map]
    dsimp only [Function.comp_def]
    dsimp only [roundedProduct, exactProduct, epsilon] at hmass ⊢
    linarith
  have hadd := fold_add_error hmax products zero zero_finite hf hb
  simp only [zero_toReal, zero_add] at hadd
  change Model.isFinite (integrate f terms) = true ∧
    |Model.toReal (integrate f terms) - (products.map Model.toReal).sum| ≤
      products.length * epsilon at hadd
  refine ⟨hadd.1, ?_⟩
  have ht := abs_sub_le (Model.toReal (integrate f terms))
    (products.map Model.toReal).sum (terms.map exactProduct).sum
  simp only [products, List.map_map, List.length_map] at hadd ht
  dsimp only [roundedProduct, exactProduct, epsilon, Function.comp_def] at hsum hadd ht
  linarith [hadd.2]

end Quadrature.Binary64
