import Quadrature.Legendre.RootData
import Quadrature.Rules.Tables

/-!
# Certificates for all ten stored Gaussian rules

Every table of the original C program receives a stored-rule certificate here.
Orders one through four reuse the certificates of `Rules/Basic` after `table n`
is identified with the hand-written rule. Orders five through ten are checked
against isolated Legendre roots and rational enclosures of their interpolatory
weights, with tolerances `6·10⁻¹⁶` for nodes and `5·10⁻¹⁶` for weights. Orders
one through four also meet the tighter node tolerance `10⁻¹⁶`, and order six
does not (`six_node_exceeds_tighter_tolerance`).

For each order from five to ten, the `*_node_check` theorem computes by kernel
evaluation that the exact rational value of every stored node is within
`6·10⁻¹⁶` of both endpoints of the isolating bracket of the corresponding
Legendre root. The `*_weight_check` theorem does the same for every stored
weight with tolerance `5·10⁻¹⁶` against the rational enclosure
`weightInterval` of the interpolatory weight over that bracket. The
`*_weights_mem` theorem proves that the ideal weight lies in that enclosure, and
the `*_certificate` theorem assembles the three into a certificate with
`certificate_of_enclosures`.
-/

namespace Quadrature.Binary64.StoredRule

open Legendre.RootCertificates Legendre.RootData

-- Kernel evaluation of the rational node enclosure check for the five-point rule.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem five_node_check (i : Fin 5) :
    nodeRational 5 i - (6 / 10 ^ 16 : ℚ) ≤ (fiveBrackets i).interval.lo ∧
    (fiveBrackets i).interval.hi ≤ nodeRational 5 i + (6 / 10 ^ 16 : ℚ) := by
  fin_cases i <;> decide +kernel

-- Kernel evaluation of the rational weight enclosure check for the five-point rule.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem five_weight_check (i : Fin 5) :
    weightRational 5 i - (5 / 10 ^ 16 : ℚ) ≤
      (weightInterval fivePolynomial (fiveBrackets i)).lo ∧
    (weightInterval fivePolynomial (fiveBrackets i)).hi ≤
      weightRational 5 i + (5 / 10 ^ 16 : ℚ) := by
  fin_cases i <;> decide +kernel

theorem five_weights_mem (i : Fin 5) :
    (weightInterval fivePolynomial (fiveBrackets i)).memReal (fiveGaussian.weights i) :=
  weight_mem fivePolynomial fiveBrackets five_valid
    five_ordered five_monic five_degree i

/-- The original 5-point table approximates its exact Gaussian rule. -/
theorem five_certificate :
    (table 5).Certificate fiveGaussian (6 / 10 ^ 16) (5 / 10 ^ 16) := by
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using
    certificate_of_enclosures 5 (by decide) fiveGaussian
    (fun i => (fiveBrackets i).interval)
    (fun i => weightInterval fivePolynomial (fiveBrackets i))
    five_nodes_mem five_weights_mem (6 / 10 ^ 16) (5 / 10 ^ 16)
    five_node_check five_weight_check

-- Kernel evaluation of the rational node enclosure check for the six-point rule.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem six_node_check (i : Fin 6) :
    nodeRational 6 i - (6 / 10 ^ 16 : ℚ) ≤ (sixBrackets i).interval.lo ∧
    (sixBrackets i).interval.hi ≤ nodeRational 6 i + (6 / 10 ^ 16 : ℚ) := by
  fin_cases i <;> decide +kernel

-- Kernel evaluation of the rational weight enclosure check for the six-point rule.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem six_weight_check (i : Fin 6) :
    weightRational 6 i - (5 / 10 ^ 16 : ℚ) ≤
      (weightInterval sixPolynomial (sixBrackets i)).lo ∧
    (weightInterval sixPolynomial (sixBrackets i)).hi ≤
      weightRational 6 i + (5 / 10 ^ 16 : ℚ) := by
  fin_cases i <;> decide +kernel

theorem six_weights_mem (i : Fin 6) :
    (weightInterval sixPolynomial (sixBrackets i)).memReal (sixGaussian.weights i) :=
  weight_mem sixPolynomial sixBrackets six_valid
    six_ordered six_monic six_degree i

/-- The original 6-point table approximates its exact Gaussian rule. -/
theorem six_certificate :
    (table 6).Certificate sixGaussian (6 / 10 ^ 16) (5 / 10 ^ 16) := by
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using
    certificate_of_enclosures 6 (by decide) sixGaussian
    (fun i => (sixBrackets i).interval)
    (fun i => weightInterval sixPolynomial (sixBrackets i))
    six_nodes_mem six_weights_mem (6 / 10 ^ 16) (5 / 10 ^ 16)
    six_node_check six_weight_check

-- Kernel evaluation of the rational node enclosure check for the seven-point rule.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem seven_node_check (i : Fin 7) :
    nodeRational 7 i - (6 / 10 ^ 16 : ℚ) ≤ (sevenBrackets i).interval.lo ∧
    (sevenBrackets i).interval.hi ≤ nodeRational 7 i + (6 / 10 ^ 16 : ℚ) := by
  fin_cases i <;> decide +kernel

-- Kernel evaluation of the rational weight enclosure check for the seven-point rule.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem seven_weight_check (i : Fin 7) :
    weightRational 7 i - (5 / 10 ^ 16 : ℚ) ≤
      (weightInterval sevenPolynomial (sevenBrackets i)).lo ∧
    (weightInterval sevenPolynomial (sevenBrackets i)).hi ≤
      weightRational 7 i + (5 / 10 ^ 16 : ℚ) := by
  fin_cases i <;> decide +kernel

theorem seven_weights_mem (i : Fin 7) :
    (weightInterval sevenPolynomial (sevenBrackets i)).memReal (sevenGaussian.weights i) :=
  weight_mem sevenPolynomial sevenBrackets seven_valid
    seven_ordered seven_monic seven_degree i

/-- The original 7-point table approximates its exact Gaussian rule. -/
theorem seven_certificate :
    (table 7).Certificate sevenGaussian (6 / 10 ^ 16) (5 / 10 ^ 16) := by
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using
    certificate_of_enclosures 7 (by decide) sevenGaussian
    (fun i => (sevenBrackets i).interval)
    (fun i => weightInterval sevenPolynomial (sevenBrackets i))
    seven_nodes_mem seven_weights_mem (6 / 10 ^ 16) (5 / 10 ^ 16)
    seven_node_check seven_weight_check

-- Kernel evaluation of the rational node enclosure check for the eight-point rule.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem eight_node_check (i : Fin 8) :
    nodeRational 8 i - (6 / 10 ^ 16 : ℚ) ≤ (eightBrackets i).interval.lo ∧
    (eightBrackets i).interval.hi ≤ nodeRational 8 i + (6 / 10 ^ 16 : ℚ) := by
  fin_cases i <;> decide +kernel

-- Kernel evaluation of the rational weight enclosure check for the eight-point rule.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem eight_weight_check (i : Fin 8) :
    weightRational 8 i - (5 / 10 ^ 16 : ℚ) ≤
      (weightInterval eightPolynomial (eightBrackets i)).lo ∧
    (weightInterval eightPolynomial (eightBrackets i)).hi ≤
      weightRational 8 i + (5 / 10 ^ 16 : ℚ) := by
  fin_cases i <;> decide +kernel

theorem eight_weights_mem (i : Fin 8) :
    (weightInterval eightPolynomial (eightBrackets i)).memReal (eightGaussian.weights i) :=
  weight_mem eightPolynomial eightBrackets eight_valid
    eight_ordered eight_monic eight_degree i

/-- The original 8-point table approximates its exact Gaussian rule. -/
theorem eight_certificate :
    (table 8).Certificate eightGaussian (6 / 10 ^ 16) (5 / 10 ^ 16) := by
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using
    certificate_of_enclosures 8 (by decide) eightGaussian
    (fun i => (eightBrackets i).interval)
    (fun i => weightInterval eightPolynomial (eightBrackets i))
    eight_nodes_mem eight_weights_mem (6 / 10 ^ 16) (5 / 10 ^ 16)
    eight_node_check eight_weight_check

-- Kernel evaluation of the rational node enclosure check for the nine-point rule.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem nine_node_check (i : Fin 9) :
    nodeRational 9 i - (6 / 10 ^ 16 : ℚ) ≤ (nineBrackets i).interval.lo ∧
    (nineBrackets i).interval.hi ≤ nodeRational 9 i + (6 / 10 ^ 16 : ℚ) := by
  fin_cases i <;> decide +kernel

-- Kernel evaluation of the rational weight enclosure check for the nine-point rule.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem nine_weight_check (i : Fin 9) :
    weightRational 9 i - (5 / 10 ^ 16 : ℚ) ≤
      (weightInterval ninePolynomial (nineBrackets i)).lo ∧
    (weightInterval ninePolynomial (nineBrackets i)).hi ≤
      weightRational 9 i + (5 / 10 ^ 16 : ℚ) := by
  fin_cases i <;> decide +kernel

theorem nine_weights_mem (i : Fin 9) :
    (weightInterval ninePolynomial (nineBrackets i)).memReal (nineGaussian.weights i) :=
  weight_mem ninePolynomial nineBrackets nine_valid
    nine_ordered nine_monic nine_degree i

/-- The original 9-point table approximates its exact Gaussian rule. -/
theorem nine_certificate :
    (table 9).Certificate nineGaussian (6 / 10 ^ 16) (5 / 10 ^ 16) := by
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using
    certificate_of_enclosures 9 (by decide) nineGaussian
    (fun i => (nineBrackets i).interval)
    (fun i => weightInterval ninePolynomial (nineBrackets i))
    nine_nodes_mem nine_weights_mem (6 / 10 ^ 16) (5 / 10 ^ 16)
    nine_node_check nine_weight_check

-- Kernel evaluation of the rational node enclosure check for the ten-point rule.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem ten_node_check (i : Fin 10) :
    nodeRational 10 i - (6 / 10 ^ 16 : ℚ) ≤ (tenBrackets i).interval.lo ∧
    (tenBrackets i).interval.hi ≤ nodeRational 10 i + (6 / 10 ^ 16 : ℚ) := by
  fin_cases i <;> decide +kernel

-- Kernel evaluation of the rational weight enclosure check for the ten-point rule.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem ten_weight_check (i : Fin 10) :
    weightRational 10 i - (5 / 10 ^ 16 : ℚ) ≤
      (weightInterval tenPolynomial (tenBrackets i)).lo ∧
    (weightInterval tenPolynomial (tenBrackets i)).hi ≤
      weightRational 10 i + (5 / 10 ^ 16 : ℚ) := by
  fin_cases i <;> decide +kernel

theorem ten_weights_mem (i : Fin 10) :
    (weightInterval tenPolynomial (tenBrackets i)).memReal (tenGaussian.weights i) :=
  weight_mem tenPolynomial tenBrackets ten_valid
    ten_ordered ten_monic ten_degree i

/-- The original 10-point table approximates its exact Gaussian rule. -/
theorem ten_certificate :
    (table 10).Certificate tenGaussian (6 / 10 ^ 16) (5 / 10 ^ 16) := by
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using
    certificate_of_enclosures 10 (by decide) tenGaussian
    (fun i => (tenBrackets i).interval)
    (fun i => weightInterval tenPolynomial (tenBrackets i))
    ten_nodes_mem ten_weights_mem (6 / 10 ^ 16) (5 / 10 ^ 16)
    ten_node_check ten_weight_check

/-- The one-point slice of the flattened table is the hand-written `oneStored`, by kernel
evaluation of each entry. -/
theorem table_one : table 1 = oneStored := by
  unfold table oneStored
  congr 1 <;> funext i <;> fin_cases i <;> decide +kernel

/-- The two-point slice of the flattened table is the hand-written `twoStored`, by kernel
evaluation of each entry. -/
theorem table_two : table 2 = twoStored := by
  unfold table twoStored
  congr 1 <;> funext i <;> fin_cases i <;> decide +kernel

/-- The three-point slice of the flattened table is the hand-written `threeStored`, by kernel
evaluation of each entry. -/
theorem table_three : table 3 = threeStored := by
  unfold table threeStored
  congr 1 <;> funext i <;> fin_cases i <;> decide +kernel

/-- The four-point slice of the flattened table is the hand-written `fourStored`, by kernel
evaluation of each entry. -/
theorem table_four : table 4 = fourStored := by
  unfold table fourStored
  congr 1 <;> funext i <;> fin_cases i <;> decide +kernel

open FloatLib.Floats.Formats.BinaryInterchange in
/-- Records that the tight node tolerance `10⁻¹⁶` fails at node 1 of the six-point table, whose
proved node tolerance is `6·10⁻¹⁶`. The lower endpoint of the root bracket already exceeds the
stored value by more than `10⁻¹⁶`. -/
theorem six_node_exceeds_tighter_tolerance :
    (1 / 10 ^ 16 : ℝ) < |Model.toReal ((table 6).nodes 1) - sixGaussian.nodes 1| := by
  rw [node_toReal 6 (by decide)]
  have hx := six_nodes_mem 1
  have h : nodeRational 6 1 + (1 / 10 ^ 16 : ℚ) < (sixBrackets 1).interval.lo := by
    decide +kernel
  have h' : (nodeRational 6 1 : ℝ) + (1 / 10 ^ 16 : ℝ) <
      ((sixBrackets 1).interval.lo : ℝ) := by
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one] using
      (Rat.cast_lt (K := ℝ)).2 h
  rw [abs_sub_comm]
  exact (show (1 / 10 ^ 16 : ℝ) < sixGaussian.nodes 1 - nodeRational 6 1 by
    linarith [hx.1]).trans_le (le_abs_self _)

/-- The exact Gaussian rule of order `n` for `1 ≤ n ≤ 10`, selected by cases on `n`. -/
noncomputable def ideal (n : ℕ) (hlo : 1 ≤ n) (hhi : n ≤ 10) : Legendre.Rule n := by
  interval_cases n
  · exact Legendre.oneGaussian
  · exact Legendre.twoGaussian
  · exact Legendre.threeGaussian
  · exact Legendre.fourGaussian
  · exact fiveGaussian
  · exact sixGaussian
  · exact sevenGaussian
  · exact eightGaussian
  · exact nineGaussian
  · exact tenGaussian

/-- For every `1 ≤ n ≤ 10`, `table n` has a stored-rule certificate against `ideal n` with node
tolerance `6·10⁻¹⁶` and weight tolerance `5·10⁻¹⁶`. Orders one through four are weakened from
their tighter certificates with `Certificate.mono`. -/
theorem table_certificate (n : ℕ) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    (table n).Certificate (ideal n hlo hhi) (6 / 10 ^ 16) (5 / 10 ^ 16) := by
  interval_cases n
  · rw [table_one]
    exact oneStored_certificate.mono (by norm_num) le_rfl
  · rw [table_two]
    exact twoStored_certificate.mono (by norm_num) le_rfl
  · rw [table_three]
    exact threeStored_certificate.mono (by norm_num) le_rfl
  · rw [table_four]
    exact fourStored_certificate.mono (by norm_num) le_rfl
  · exact five_certificate
  · exact six_certificate
  · exact seven_certificate
  · exact eight_certificate
  · exact nine_certificate
  · exact ten_certificate

end Quadrature.Binary64.StoredRule
