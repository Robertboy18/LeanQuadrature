import Mathlib.Tactic
import PDE.Symbolic.Continuum.Quadrature.GaussLegendre

/-!
# Explicit Gauss–Legendre rules

LeanPDE's `QuadratureRule` is a list of `(weight, node)` pairs with nodes in `[0, 1]`, and
the rules here have weights summing to one, so `valueOn f a b` is the affine transport of
the rule to `[a, b]`. In that convention this file writes the Gauss–Legendre rules with one
to four nodes in radicals and proves each exact through degree `2n - 1`
(`ExactUpTo (2n - 1)`) by checking the monomial moments one degree at a time.
`LegendreIdentification` transports them to `[-1, 1]` as `GaussianRule`s.
-/

namespace Quadrature.Legendre

open PDE.Symbolic.Continuum

noncomputable section

/-- The one-point Gauss–Legendre rule: the midpoint `1/2` with weight one. -/
def one : QuadratureRule where
  terms := [(1, 1 / 2)]
  nodes_mem_unit := by
    intro term h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst term
    norm_num

/-- The one-point rule is exact through degree one. -/
theorem one_exact : one.ExactUpTo 1 := by
  intro k hk
  interval_cases k <;>
    norm_num [QuadratureRule.moment, QuadratureRule.normalizedValue, one, weightedSum]

/-- The two-point Gauss–Legendre rule, LeanPDE's `gaussLegendreTwoRule`, with nodes
`(1 ∓ 1/√3)/2` and equal weights `1/2`. -/
abbrev two := gaussLegendreTwoRule

/-- The two-point rule is exact through degree three. -/
theorem two_exact : two.ExactUpTo 3 :=
  gaussLegendreTwoRule.exactUpTo_three

/-- The outer node `√(3/5)` of the three-point rule on `[-1, 1]`. -/
def threeNode : ℝ := Real.sqrt (3 / 5)

/-- `threeNode ^ 2 = 3/5`. -/
theorem threeNode_sq : threeNode ^ 2 = (3 / 5 : ℝ) := by
  exact Real.sq_sqrt (by norm_num)

/-- `threeNode` lies in `[0, 1]`. -/
theorem threeNode_mem : threeNode ∈ Set.Icc (0 : ℝ) 1 := by
  have hn : 0 ≤ threeNode := Real.sqrt_nonneg _
  constructor
  · exact hn
  · nlinarith [threeNode_sq]

/-- The three-point Gauss–Legendre rule: nodes `(1 - √(3/5))/2`, `1/2`, `(1 + √(3/5))/2`
with weights `5/18`, `4/9`, `5/18`. -/
def three : QuadratureRule where
  terms := [(5 / 18, (1 - threeNode) / 2), (4 / 9, 1 / 2),
    (5 / 18, (1 + threeNode) / 2)]
  nodes_mem_unit := by
    intro term h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h <;> subst term <;>
      constructor <;> dsimp <;> nlinarith [threeNode_mem.1, threeNode_mem.2]

/-- The three-point rule is exact through degree five. -/
theorem three_exact : three.ExactUpTo 5 := by
  have hfour : threeNode ^ 4 = (9 / 25 : ℝ) := by
    calc
      _ = (threeNode ^ 2) ^ 2 := by ring
      _ = _ := by rw [threeNode_sq]; norm_num
  intro k hk
  interval_cases k <;>
    norm_num [QuadratureRule.moment, QuadratureRule.normalizedValue, three, weightedSum] <;>
    ring_nf <;> nlinarith [threeNode_sq]

/-- The radical `√30` appearing in the four-point nodes and weights. -/
def fourRadical : ℝ := Real.sqrt 30

/-- `fourRadical ^ 2 = 30`. -/
theorem fourRadical_sq : fourRadical ^ 2 = 30 :=
  Real.sq_sqrt (by norm_num)

/-- The inner node `√((15 - 2√30)/35)` of the four-point rule on `[-1, 1]`. -/
def fourInner : ℝ := Real.sqrt ((15 - 2 * fourRadical) / 35)
/-- The outer node `√((15 + 2√30)/35)` of the four-point rule on `[-1, 1]`. -/
def fourOuter : ℝ := Real.sqrt ((15 + 2 * fourRadical) / 35)

/-- `0 ≤ √30 ≤ 6`. -/
theorem fourRadical_bounds : (0 : ℝ) ≤ fourRadical ∧ fourRadical ≤ 6 := by
  have h : 0 ≤ fourRadical := Real.sqrt_nonneg _
  exact ⟨h, by nlinarith [fourRadical_sq]⟩

/-- `fourInner ^ 2 = (15 - 2√30)/35`. -/
theorem fourInner_sq : fourInner ^ 2 = (15 - 2 * fourRadical) / 35 :=
  Real.sq_sqrt (by nlinarith [fourRadical_bounds.2])

/-- `fourOuter ^ 2 = (15 + 2√30)/35`. -/
theorem fourOuter_sq : fourOuter ^ 2 = (15 + 2 * fourRadical) / 35 :=
  Real.sq_sqrt (by nlinarith [fourRadical_bounds.1])

/-- `fourInner` lies in `[0, 1]`. -/
theorem fourInner_mem : fourInner ∈ Set.Icc (0 : ℝ) 1 := by
  have h : 0 ≤ fourInner := Real.sqrt_nonneg _
  exact ⟨h, by nlinarith [fourInner_sq, fourRadical_bounds.1]⟩

/-- `fourOuter` lies in `[0, 1]`. -/
theorem fourOuter_mem : fourOuter ∈ Set.Icc (0 : ℝ) 1 := by
  have h : 0 ≤ fourOuter := Real.sqrt_nonneg _
  exact ⟨h, by nlinarith [fourOuter_sq, fourRadical_bounds.2]⟩

/-- The four-point Gauss–Legendre rule with nodes in ascending order, `(1 ∓ fourOuter)/2` and
`(1 ∓ fourInner)/2`, with weights `(18 ∓ √30)/72`. -/
def four : QuadratureRule where
  terms := [((18 - fourRadical) / 72, (1 - fourOuter) / 2),
    ((18 + fourRadical) / 72, (1 - fourInner) / 2),
    ((18 + fourRadical) / 72, (1 + fourInner) / 2),
    ((18 - fourRadical) / 72, (1 + fourOuter) / 2)]
  nodes_mem_unit := by
    intro term h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h <;> subst term <;>
      constructor <;> dsimp <;>
      nlinarith [fourInner_mem.1, fourInner_mem.2, fourOuter_mem.1, fourOuter_mem.2]

/-- The four-point rule is exact through degree seven. -/
theorem four_exact : four.ExactUpTo 7 := by
  have hi4 : fourInner ^ 4 = ((15 - 2 * fourRadical) / 35) ^ 2 := by
    calc
      _ = (fourInner ^ 2) ^ 2 := by ring
      _ = _ := by rw [fourInner_sq]
  have ho4 : fourOuter ^ 4 = ((15 + 2 * fourRadical) / 35) ^ 2 := by
    calc
      _ = (fourOuter ^ 2) ^ 2 := by ring
      _ = _ := by rw [fourOuter_sq]
  have hi6 : fourInner ^ 6 = ((15 - 2 * fourRadical) / 35) ^ 3 := by
    calc
      _ = (fourInner ^ 2) ^ 3 := by ring
      _ = _ := by rw [fourInner_sq]
  have ho6 : fourOuter ^ 6 = ((15 + 2 * fourRadical) / 35) ^ 3 := by
    calc
      _ = (fourOuter ^ 2) ^ 3 := by ring
      _ = _ := by rw [fourOuter_sq]
  intro k hk
  interval_cases k <;>
    norm_num [QuadratureRule.moment, QuadratureRule.normalizedValue, four, weightedSum] <;>
    ring_nf <;>
    simp only [fourInner_sq, fourOuter_sq, hi4, ho4, hi6, ho6] <;>
    ring_nf <;> nlinarith [fourRadical_sq]

end
end Quadrature.Legendre
