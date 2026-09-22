import
  FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.RoundingSemantics.Executable
import Quadrature.CSource.Tables.Literals

/-!
# Exact meaning of the decimal tables in the original C text

A `Decimal` read by `Quadrature.CSource.Tables.Literals` denotes the exact rational
`Decimal.value`. `Decimal.round_toReal` identifies its finite binary64
conversion with one nearest-even rounding of that rational, by FloatLib's
rational-rounding theorem. `node_values` and `weight_values` then state that
the table values of the Clight model are the rounded source decimals, bit for
bit, including the sign of zero.
-/

namespace Quadrature.CSourceTables

open FloatLib.Floats.Formats.BinaryInterchange

/-- When `d.round` is finite, its real value is the nearest-even rounding `Model.roundAt` of the
exact rational `d.value`. -/
theorem Decimal.round_toReal (d : Decimal) (hfinite : Model.isFinite d.round = true) :
    Model.toReal d.round = Model.roundAt .binary64 (d.value : ℝ) := by
  have hden : (10 : ℕ) ^ d.places ≠ 0 := pow_ne_zero _ (by decide)
  by_cases hzero : d.significand = 0
  · cases hsign : d.negative <;>
      simp [Decimal.round, Decimal.value, hzero, hsign, Model.roundAt]
  · rw [Decimal.round, Model.roundRat,
      Model.toReal_roundRatScaled_eq_roundAt .binary64 d.negative d.significand
        (10 ^ d.places) 0 (by decide) hzero hden hfinite]
    congr 1
    cases hsign : d.negative <;>
      simp [Decimal.value, Model.signedScaledRatToReal, Model.scaledRatToReal, hsign]

/-- The rounded binary64 values of the decimals of table `name` in `source`. -/
def tableValues (source : List Char) (name : String) :
    Option (List (Model FloatFormat.binary64)) :=
  (tableDecimals source name).map (List.map Decimal.round)

/-- If `tableBits` gives `bits`, then `tableValues` gives the decodings of `bits`, since encoding
binary64 values is injective. -/
theorem table_values_of_bits (source : List Char) (name : String) (bits : List Nat)
    (h : tableBits source name = some bits) :
    tableValues source name = some (bits.map (Model.ofNatBits (fmt := .binary64))) := by
  have hvalues := congrArg (Option.map (List.map (Model.ofNatBits (fmt := .binary64)))) h
  simpa [tableBits, tableValues, List.map_map, Function.comp_def] using hvalues

/-- The rounded node decimals of the C text are the node values of the Clight tables, bit for
bit. -/
theorem node_values :
    tableValues CSourceData.source "gauss_pts" =
      some (Binary64.ClightTableData.nodeBits.map (Model.ofNatBits (fmt := .binary64))) :=
  table_values_of_bits _ _ _ node_bits

/-- The rounded weight decimals of the C text are the weight values of the Clight tables, bit for
bit. -/
theorem weight_values :
    tableValues CSourceData.source "gauss_wts" =
      some (Binary64.ClightTableData.weightBits.map (Model.ofNatBits (fmt := .binary64))) :=
  table_values_of_bits _ _ _ weight_bits

/-- The node table of the C text has 55 literals. -/
theorem node_count :
    (tableDecimals CSourceData.source "gauss_pts").map List.length = some 55 := by
  simpa [tableBits, Binary64.ClightTableData.nodeBits] using
    congrArg (Option.map List.length) node_bits

/-- The weight table of the C text has 55 literals. -/
theorem weight_count :
    (tableDecimals CSourceData.source "gauss_wts").map List.length = some 55 := by
  simpa [tableBits, Binary64.ClightTableData.weightBits] using
    congrArg (Option.map List.length) weight_bits

/-- Every rounded node is finite, so `Decimal.round_toReal` applies to each of them. -/
theorem node_values_finite :
    (tableValues CSourceData.source "gauss_pts").map (fun values ↦ values.all Model.isFinite) =
      some true := by
  rw [node_values]
  decide +kernel

/-- Every rounded weight is finite, so `Decimal.round_toReal` applies to each of them. -/
theorem weight_values_finite :
    (tableValues CSourceData.source "gauss_wts").map (fun values ↦ values.all Model.isFinite) =
      some true := by
  rw [weight_values]
  decide +kernel

end Quadrature.CSourceTables
