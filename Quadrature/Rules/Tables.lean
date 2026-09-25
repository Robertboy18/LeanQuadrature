import Quadrature.Clight.TableData
import PDE.Symbolic.Continuum.Quadrature.Legendre.WeightCertificates
import Quadrature.Rules.Basic

/-!
# Exact table decoding and rational enclosure checks

`table n` selects the `n`-point rule from the flattened 55-entry node and weight
tables of the original C program. Each entry is decoded to an exact rational
with FloatLib's `toRat?`, and a stored-rule certificate is assembled from
rational enclosure checks against the ideal nodes and weights. No floating-point
arithmetic takes part in validating a tolerance.
-/

namespace Quadrature.Binary64.StoredRule

open FloatLib.Floats.Formats.BinaryInterchange
open PDE.Symbolic.Continuum
open PDE.Symbolic.Polynomial.RealRoot
open Legendre.RootCertificates

/-- The stored `n`-point rule: entry `i` of the `n`-point rule is element `n(n−1)/2 + i` of the
flattened 55-entry table, the triangular offset the original C program uses. Out-of-range
indices yield `+0.0` because of `getD`. -/
def table (n : ℕ) : StoredRule n where
  weights i := Model.ofNatBits
    (ClightTableData.weightBits[n * (n - 1) / 2 + i.val]?.getD 0)
  nodes i := Model.ofNatBits
    (ClightTableData.nodeBits[n * (n - 1) / 2 + i.val]?.getD 0)

/-- Exact rational value of a stored node, with `0` for a nonfinite entry. `node_decode` shows
the decoding succeeds for `n ≤ 10`. -/
def nodeRational (n : ℕ) (i : Fin n) : ℚ :=
  (Model.toRat? ((table n).nodes i)).getD 0

/-- Exact rational value of a stored weight, with `0` for a nonfinite entry. `weight_decode`
shows the decoding succeeds for `n ≤ 10`. -/
def weightRational (n : ℕ) (i : Fin n) : ℚ :=
  (Model.toRat? ((table n).weights i)).getD 0

-- Kernel evaluation of FloatLib's rational decoding of every stored node, ten orders.
set_option maxRecDepth 20000 in
/-- For `n ≤ 10` every stored node decodes to `some (nodeRational n i)`, so it is finite, by
kernel evaluation. -/
theorem node_decode (n : ℕ) (hn : n ≤ 10) (i : Fin n) :
    Model.toRat? ((table n).nodes i) = some (nodeRational n i) := by
  interval_cases n <;> fin_cases i <;> decide +kernel

-- Kernel evaluation of FloatLib's rational decoding of every stored weight, ten orders.
set_option maxRecDepth 20000 in
/-- For `n ≤ 10` every stored weight decodes to `some (weightRational n i)`, so it is finite, by
kernel evaluation. -/
theorem weight_decode (n : ℕ) (hn : n ≤ 10) (i : Fin n) :
    Model.toRat? ((table n).weights i) = some (weightRational n i) := by
  interval_cases n <;> fin_cases i <;> decide +kernel

/-- If `toRat?` returns `some r` then the value is finite and its real value is `r`. -/
theorem finite_real_of_toRat {value : Value} {r : ℚ}
    (h : Model.toRat? value = some r) :
    Model.isFinite value = true ∧ Model.toReal value = (r : ℝ) := by
  cases hd : Model.toDyadic? value with
  | none => simp [Model.toRat?, hd] at h
  | some d =>
      have hr : d.toRat = r := by simpa [Model.toRat?, hd] using h
      refine ⟨Model.isFinite_eq_true_of_toDyadic?_some hd, ?_⟩
      rw [Model.toReal_eq, hd, ← hr, FloatLib.Numerics.Dyadic.cast_toRat]

/-- For `n ≤ 10` the real value of a stored node is its rational decoding `nodeRational n i`. -/
theorem node_toReal (n : ℕ) (hn : n ≤ 10) (i : Fin n) :
    Model.toReal ((table n).nodes i) = (nodeRational n i : ℝ) :=
  (finite_real_of_toRat (node_decode n hn i)).2

/-- For `n ≤ 10` the real value of a stored weight is its rational decoding
`weightRational n i`. -/
theorem weight_toReal (n : ℕ) (hn : n ≤ 10) (i : Fin n) :
    Model.toReal ((table n).weights i) = (weightRational n i : ℝ) :=
  (finite_real_of_toRat (weight_decode n hn i)).2

/-- For `n ≤ 10` every stored node lies in `[-1,1]`, by kernel evaluation of the rational
decodings. -/
theorem table_node_mem (n : ℕ) (hn : n ≤ 10) (i : Fin n) :
    Model.toReal ((table n).nodes i) ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [node_toReal n hn i]
  have h : (-1 : ℚ) ≤ nodeRational n i ∧ nodeRational n i ≤ 1 := by
    interval_cases n <;> fin_cases i <;> decide +kernel
  change (-1 : ℝ) ≤ (nodeRational n i : ℝ) ∧ (nodeRational n i : ℝ) ≤ 1
  exact_mod_cast h

/-- If x lies in a rational interval whose endpoints are within δ of the rational r, then
|r − x| ≤ δ. -/
theorem abs_sub_le_of_enclosure {r δ : ℚ} {x : ℝ} {interval : RationalInterval}
    (hx : interval.memReal x)
    (hlo : r - δ ≤ interval.lo) (hhi : interval.hi ≤ r + δ) :
    |(r : ℝ) - x| ≤ (δ : ℝ) := by
  have hlo' : (r : ℝ) - δ ≤ interval.lo := by exact_mod_cast hlo
  have hhi' : (interval.hi : ℝ) ≤ (r : ℝ) + δ := by exact_mod_cast hhi
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2]

/-- If the ideal nodes and weights lie in rational intervals whose endpoints are within the
tolerances of the decoded table entries, then `table n` has a stored-rule certificate. -/
theorem certificate_of_enclosures (n : ℕ) (hn : n ≤ 10) (ideal : Legendre.Rule n)
    (nodeIntervals weightIntervals : Fin n → RationalInterval)
    (hnode : ∀ i, (nodeIntervals i).memReal (ideal.nodes i))
    (hweight : ∀ i, (weightIntervals i).memReal (ideal.weights i))
    (nodeTolerance weightTolerance : ℚ)
    (hnodeCheck : ∀ i, nodeRational n i - nodeTolerance ≤ (nodeIntervals i).lo ∧
      (nodeIntervals i).hi ≤ nodeRational n i + nodeTolerance)
    (hweightCheck : ∀ i, weightRational n i - weightTolerance ≤ (weightIntervals i).lo ∧
      (weightIntervals i).hi ≤ weightRational n i + weightTolerance) :
    (table n).Certificate ideal nodeTolerance weightTolerance where
  weight_finite i := (finite_real_of_toRat (weight_decode n hn i)).1
  node_finite i := (finite_real_of_toRat (node_decode n hn i)).1
  node_mem := table_node_mem n hn
  node_error i := by
    rw [node_toReal n hn i]
    exact abs_sub_le_of_enclosure (hnode i) (hnodeCheck i).1 (hnodeCheck i).2
  weight_error i := by
    rw [weight_toReal n hn i]
    exact abs_sub_le_of_enclosure (hweight i) (hweightCheck i).1 (hweightCheck i).2

/-- A stored-rule certificate stays valid when either tolerance is increased. -/
theorem Certificate.mono {n : ℕ} {stored : StoredRule n} {ideal : Legendre.Rule n}
    {nodeTolerance weightTolerance nodeTolerance' weightTolerance' : ℝ}
    (cert : stored.Certificate ideal nodeTolerance weightTolerance)
    (hnode : nodeTolerance ≤ nodeTolerance') (hweight : weightTolerance ≤ weightTolerance') :
    stored.Certificate ideal nodeTolerance' weightTolerance' where
  weight_finite := cert.weight_finite
  node_finite := cert.node_finite
  node_mem := cert.node_mem
  node_error i := (cert.node_error i).trans hnode
  weight_error i := (cert.weight_error i).trans hweight

end Quadrature.Binary64.StoredRule
