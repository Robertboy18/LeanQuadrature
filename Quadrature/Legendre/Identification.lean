import PDE.Symbolic.Continuum.Quadrature.Gaussian.Characterization
import PDE.Symbolic.Continuum.Quadrature.Approximation
import Quadrature.Legendre.Basic

/-!
# The explicit rules use the constructed Legendre family

`Rule n` is a `GaussianRule` with `n` nodes for the constant weight on `[-1, 1]`. The one-
to four-point rules of `Legendre` are transported from LeanPDE's `[0, 1]` convention and
packaged as such rules. `GaussianRule.nodal_eq_integralOrthogonalPolynomial` then identifies
each nodal polynomial with `monicPolynomial n`, the monic Legendre polynomial obtained by
orthogonal projection in `Orthogonal`.
-/

namespace Quadrature.Legendre

open Polynomial Set PDE.Symbolic.Continuum
open scoped BigOperators

noncomputable section

/-- A Gaussian rule with `n` nodes for the constant weight `1` on `[-1, 1]`. -/
abbrev Rule (n : ℕ) := GaussianRule (-1) 1 (fun _ => 1) continuousOn_const n

/-- The positive node `1/√3` of the two-point rule on `[-1, 1]`, written as `√3/3`. -/
def twoNode : ℝ := Real.sqrt 3 / 3

/-- `twoNode ^ 2 = 1/3`. -/
theorem twoNode_sq : twoNode ^ 2 = (1 / 3 : ℝ) := by
  dsimp [twoNode]
  nlinarith [sqrt_three_sq]

/-- `twoNode` lies in the open interval `(0, 1)`. -/
theorem twoNode_interior : twoNode ∈ Ioo (0 : ℝ) 1 := by
  have h : 0 ≤ twoNode := div_nonneg (Real.sqrt_nonneg _) (by norm_num)
  constructor <;> nlinarith [twoNode_sq]

/-- `threeNode = √(3/5)` lies in the open interval `(0, 1)`. -/
theorem threeNode_interior : threeNode ∈ Ioo (0 : ℝ) 1 := by
  constructor <;> nlinarith [threeNode_sq, threeNode_mem.1]

/-- The four-point nodes satisfy `0 < fourInner < fourOuter < 1`. -/
theorem fourNodes_ordered : 0 < fourInner ∧ fourInner < fourOuter ∧ fourOuter < 1 := by
  have hr : 0 < fourRadical := by nlinarith [fourRadical_sq, fourRadical_bounds.1]
  refine ⟨?_, ?_, ?_⟩ <;>
    nlinarith [fourInner_sq, fourOuter_sq, fourInner_mem.1, fourOuter_mem.1,
      fourRadical_bounds.2]

/-- The midpoint rule on `[-1, 1]`: the single node `0` with weight `2`. -/
def oneGaussian : Rule 1 where
  nodes := ![0]
  weights := ![2]
  injective := fun i j _ => Subsingleton.elim i j
  interior := by intro i; fin_cases i; norm_num
  positive := by intro i; fin_cases i; norm_num
  exact := by
    intro p hp
    have h := QuadratureRule.valueOn_eq_integral_of_natDegree_le one_exact p (by omega) (-1) 1
    norm_num [one, QuadratureRule.valueOn, QuadratureRule.termsOn, weightedSum,
      polynomialIntegral, Fin.sum_univ_succ] at h ⊢
    exact h

/-- The two-point Gauss–Legendre rule on `[-1, 1]`: nodes `±1/√3`, each with weight `1`. -/
def twoGaussian : Rule 2 where
  nodes := ![-twoNode, twoNode]
  weights := ![1, 1]
  injective := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> linarith [twoNode_interior.1]
  interior := by
    intro i
    fin_cases i <;> dsimp <;>
      constructor <;> linarith [twoNode_interior.1, twoNode_interior.2]
  positive := by intro i; fin_cases i <;> norm_num
  exact := by
    intro p hp
    have h := QuadratureRule.valueOn_eq_integral_of_natDegree_le two_exact p (by omega) (-1) 1
    convert h using 1 <;>
      simp [two, gaussLegendreTwoRule, gaussLegendreTwoLeftNode, gaussLegendreTwoRightNode,
        QuadratureRule.valueOn, QuadratureRule.termsOn, weightedSum, polynomialIntegral,
        Fin.sum_univ_succ, twoNode]
    ring_nf

/-- The three-point Gauss–Legendre rule on `[-1, 1]`: nodes `-√(3/5)`, `0`, `√(3/5)` with
weights `5/9`, `8/9`, `5/9`. -/
def threeGaussian : Rule 3 where
  nodes := ![-threeNode, 0, threeNode]
  weights := ![5 / 9, 8 / 9, 5 / 9]
  injective := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> linarith [threeNode_interior.1]
  interior := by
    intro i
    fin_cases i <;> dsimp <;>
      constructor <;> linarith [threeNode_interior.1, threeNode_interior.2]
  positive := by intro i; fin_cases i <;> norm_num
  exact := by
    intro p hp
    have h := QuadratureRule.valueOn_eq_integral_of_natDegree_le three_exact p (by omega) (-1) 1
    convert h using 1 <;>
      simp [three, QuadratureRule.valueOn, QuadratureRule.termsOn, weightedSum,
        polynomialIntegral, Fin.sum_univ_succ]
    ring_nf

/-- The four-point Gauss–Legendre rule on `[-1, 1]`: nodes `±fourOuter`, `±fourInner` with
weights `(18 - √30)/36` on the outer pair and `(18 + √30)/36` on the inner pair. -/
def fourGaussian : Rule 4 where
  nodes := ![-fourOuter, -fourInner, fourInner, fourOuter]
  weights := ![(18 - fourRadical) / 36, (18 + fourRadical) / 36,
    (18 + fourRadical) / 36, (18 - fourRadical) / 36]
  injective := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp at h ⊢ <;>
      linarith [fourNodes_ordered.1, fourNodes_ordered.2.1]
  interior := by
    intro i
    fin_cases i <;> dsimp <;>
      constructor <;>
      linarith [fourNodes_ordered.1, fourNodes_ordered.2.1, fourNodes_ordered.2.2]
  positive := by
    intro i
    fin_cases i <;> simp <;> linarith [fourRadical_bounds.1, fourRadical_bounds.2]
  exact := by
    intro p hp
    have h := QuadratureRule.valueOn_eq_integral_of_natDegree_le four_exact p (by omega) (-1) 1
    convert h using 1 <;>
      simp [four, QuadratureRule.valueOn, QuadratureRule.termsOn, weightedSum,
        polynomialIntegral, Fin.sum_univ_succ]
    ring_nf

/-- The monic Legendre polynomial of degree `n`, defined as the monic orthogonal polynomial
for the constant weight on `[-1, 1]`. -/
def monicPolynomial (n : ℕ) : ℝ[X] :=
  integralOrthogonalPolynomial (-1) 1 (by norm_num) (fun _ => 1)
    continuousOn_const (by intro x hx; norm_num) n

/-- The nodal polynomial of `oneGaussian` is the monic Legendre polynomial of degree one. -/
theorem one_nodal_eq :
    Lagrange.nodal Finset.univ oneGaussian.nodes = monicPolynomial 1 :=
  oneGaussian.nodal_eq_integralOrthogonalPolynomial (by norm_num) (by intro x hx; norm_num)

/-- The nodal polynomial of `twoGaussian` is the monic Legendre polynomial of degree two. -/
theorem two_nodal_eq :
    Lagrange.nodal Finset.univ twoGaussian.nodes = monicPolynomial 2 :=
  twoGaussian.nodal_eq_integralOrthogonalPolynomial (by norm_num) (by intro x hx; norm_num)

/-- The nodal polynomial of `threeGaussian` is the monic Legendre polynomial of degree
three. -/
theorem three_nodal_eq :
    Lagrange.nodal Finset.univ threeGaussian.nodes = monicPolynomial 3 :=
  threeGaussian.nodal_eq_integralOrthogonalPolynomial (by norm_num) (by intro x hx; norm_num)

/-- The nodal polynomial of `fourGaussian` is the monic Legendre polynomial of degree
four. -/
theorem four_nodal_eq :
    Lagrange.nodal Finset.univ fourGaussian.nodes = monicPolynomial 4 :=
  fourGaussian.nodal_eq_integralOrthogonalPolynomial (by norm_num) (by intro x hx; norm_num)

end
end Quadrature.Legendre
