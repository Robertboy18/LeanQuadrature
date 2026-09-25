import Quadrature.Binary64.Program
import PDE.Symbolic.Continuum.Quadrature.Legendre.Identification
import Quadrature.Rules.Constants

/-!
# Stored rules and their certificates

A stored rule is a table of binary64 weights and nodes in accumulation order. A
stored-rule certificate for it, against an ideal Legendre rule, consists of
finiteness of every table entry, decoded nodes in `[-1,1]`, and node and weight
error bounds `nodeTolerance` and `weightTolerance` against the ideal rule. The
tables here hold the constants of the original C program, including its
three-point outer weight `0.555555555555556`, which is `4.69·10⁻¹⁶` from `5/9`.
The uniform weight tolerance is therefore `5·10⁻¹⁶`, and the tolerance `2⁻⁵³`
of the Appel–Bindel manuscript would be false for that entry.
-/

namespace Quadrature.Binary64

open FloatLib.Floats.Formats.BinaryInterchange
open PDE.Symbolic.Continuum

/-- A table of `n` binary64 weights and `n` nodes, indexed in accumulation order. -/
structure StoredRule (n : ℕ) where
  weights : Fin n → Value
  nodes : Fin n → Value

namespace StoredRule

/-- The (weight, node) list in accumulation order, as `integrate` consumes it. -/
def terms {n : ℕ} (stored : StoredRule n) : List (Value × Value) :=
  List.ofFn fun i => (stored.weights i, stored.nodes i)

/-- A stored-rule certificate: every entry is finite, every decoded node lies in `[-1,1]`, and
every node and weight is within `nodeTolerance` and `weightTolerance` of the ideal rule. The
default arguments are `nodeTolerance := 1/10^16` and `weightTolerance := 5/10^16`, so
`stored.Certificate ideal` with no tolerances means the tight node tolerance. Orders one
through four meet it and orders five through ten do not, so `Rules/Certificates` states
their certificates with `6/10^16` explicitly. -/
structure Certificate {n : ℕ} (stored : StoredRule n) (ideal : Legendre.Rule n)
    (nodeTolerance : ℝ := 1 / 10 ^ 16) (weightTolerance : ℝ := 5 / 10 ^ 16) : Prop where
  weight_finite : ∀ i, Model.isFinite (stored.weights i) = true
  node_finite : ∀ i, Model.isFinite (stored.nodes i) = true
  node_mem : ∀ i, Model.toReal (stored.nodes i) ∈ Set.Icc (-1 : ℝ) 1
  node_error : ∀ i, |Model.toReal (stored.nodes i) - ideal.nodes i| ≤ nodeTolerance
  weight_error : ∀ i,
    |Model.toReal (stored.weights i) - ideal.weights i| ≤ weightTolerance

/-- A certificate for a rule with at least one node forces `0 ≤ nodeTolerance`. -/
theorem Certificate.node_tolerance_nonneg {n : ℕ} {stored : StoredRule n}
    {ideal : Legendre.Rule n} {nodeTolerance weightTolerance : ℝ}
    (cert : stored.Certificate ideal nodeTolerance weightTolerance) (hn : 0 < n) :
    0 ≤ nodeTolerance :=
  (abs_nonneg _).trans (cert.node_error ⟨0, hn⟩)

/-- A certificate for a rule with at least one node forces `0 ≤ weightTolerance`. -/
theorem Certificate.weight_tolerance_nonneg {n : ℕ} {stored : StoredRule n}
    {ideal : Legendre.Rule n} {nodeTolerance weightTolerance : ℝ}
    (cert : stored.Certificate ideal nodeTolerance weightTolerance) (hn : 0 < n) :
    0 ≤ weightTolerance :=
  (abs_nonneg _).trans (cert.weight_error ⟨0, hn⟩)

end StoredRule

/-- The stored one-point rule: weight `2` at node `0`. -/
def oneStored : StoredRule 1 := ⟨![two], ![zero]⟩
/-- The stored two-point rule: unit weights at the stored nodes for `∓1/√3`. -/
def twoStored : StoredRule 2 := ⟨![one, one], ![leftNode, rightNode]⟩
/-- The stored three-point rule: the C outer weight, the middle weight `8/9`, and the stored
nodes for `-√(3/5)`, `0`, `√(3/5)`. -/
def threeStored : StoredRule 3 :=
  ⟨![threeOuterWeight, threeMiddleWeight, threeOuterWeight],
    ![negativeThreeNode64, zero, threeNode64]⟩
/-- The stored four-point rule: outer, inner, inner, outer weights and the four stored nodes in
increasing order. -/
def fourStored : StoredRule 4 :=
  ⟨![fourOuterWeight, fourInnerWeight, fourInnerWeight, fourOuterWeight],
    ![negativeFourOuter64, negativeFourInner64, fourInner64, fourOuter64]⟩

/-- The two-point stored rule has the same terms as `twoPointTerms`. -/
theorem twoStored_terms : twoStored.terms = twoPointTerms := by decide

/-- The Legendre two-point node `Legendre.twoNode` equals `1/√3`. -/
theorem twoNode_eq_recip_sqrt : Legendre.twoNode = 1 / Real.sqrt 3 := by
  dsimp [Legendre.twoNode]
  have hs : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith

/-- The one-point table is certified against `Legendre.oneGaussian` with the default tolerances.
Both entries are exact. -/
theorem oneStored_certificate : oneStored.Certificate Legendre.oneGaussian where
  weight_finite := by decide
  node_finite := by decide
  node_mem := by intro i; fin_cases i; norm_num [oneStored, zero_toReal]
  node_error := by
    intro i
    fin_cases i
    norm_num [oneStored, Legendre.oneGaussian, zero_toReal]
  weight_error := by
    intro i
    fin_cases i
    norm_num [oneStored, Legendre.oneGaussian, two_toReal]

/-- The two-point table is certified against `Legendre.twoGaussian` with the default tolerances,
using `leftNode_error` and `rightNode_error`. -/
theorem twoStored_certificate : twoStored.Certificate Legendre.twoGaussian where
  weight_finite := by decide
  node_finite := by decide
  node_mem := by
    intro i
    fin_cases i <;> norm_num [twoStored, leftNode_toReal, rightNode_toReal]
  node_error := by
    intro i
    fin_cases i
    · change |Model.toReal leftNode - -Legendre.twoNode| ≤ (1 / 10 ^ 16 : ℝ)
      rw [twoNode_eq_recip_sqrt]
      exact leftNode_error
    · change |Model.toReal rightNode - Legendre.twoNode| ≤ (1 / 10 ^ 16 : ℝ)
      rw [twoNode_eq_recip_sqrt]
      exact rightNode_error
  weight_error := by
    intro i
    fin_cases i <;> norm_num [twoStored, Legendre.twoGaussian, one_toReal]

/-- The three-point table is certified against `Legendre.threeGaussian` with the default
tolerances. The outer weight needs the full `5·10⁻¹⁶`. -/
theorem threeStored_certificate : threeStored.Certificate Legendre.threeGaussian where
  weight_finite := by decide
  node_finite := by decide
  node_mem := by
    intro i
    fin_cases i <;>
      norm_num [threeStored, negativeThreeNode64_toReal, threeNode64_toReal, zero_toReal]
  node_error := by
    intro i
    fin_cases i
    · exact negativeThreeNode64_error
    · norm_num [threeStored, Legendre.threeGaussian, zero_toReal]
    · exact threeNode64_error
  weight_error := by
    intro i
    fin_cases i
    · exact threeOuterWeight_error
    · exact threeMiddleWeight_error.trans (by norm_num)
    · exact threeOuterWeight_error

/-- The four-point table is certified against `Legendre.fourGaussian` with the default
tolerances. -/
theorem fourStored_certificate : fourStored.Certificate Legendre.fourGaussian where
  weight_finite := by decide
  node_finite := by decide
  node_mem := by
    intro i
    fin_cases i <;>
      norm_num [fourStored, negativeFourOuter64_toReal, negativeFourInner64_toReal,
        fourOuter64_toReal, fourInner64_toReal]
  node_error := by
    intro i
    fin_cases i
    · exact negativeFourOuter64_error
    · exact negativeFourInner64_error
    · exact fourInner64_error
    · exact fourOuter64_error
  weight_error := by
    intro i
    fin_cases i
    · exact fourOuterWeight_error.trans (by norm_num)
    · exact fourInnerWeight_error.trans (by norm_num)
    · exact fourInnerWeight_error.trans (by norm_num)
    · exact fourOuterWeight_error.trans (by norm_num)

end Quadrature.Binary64
