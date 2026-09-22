import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Rational
import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
import Mathlib.Data.Rat.Defs
import Quadrature.CSource.Frontend.SourceData
import Quadrature.Clight.TableData

/-!
# Decimal table literals in the original C text

A deliberately small reader for the two table initializers in the text of the
original C program (`CSourceData.source`). `initializer` finds the unique
declaration `static const double NAME[] = {`. `bodyDecimals` replaces block
comments by whitespace and reads the comma-separated signed decimals as
natural-number digit strings. `Decimal.round` converts each exact decimal to
binary64 once, with FloatLib's rational rounder under nearest-even rounding.
`node_bits` and `weight_bits` check by kernel evaluation that all 110 values
agree with the initializers imported from clightgen in
`Quadrature.Clight.TableData`. The reader accepts only this declaration shape
and the literal grammar `-? digits "." digits`.
-/

namespace Quadrature.CSourceTables

open FloatLib.Floats.Formats.BinaryInterchange

/-- A decimal literal as written: sign, the digits as one natural number, and the number of
fractional places, so that `-0.0` keeps its sign. -/
structure Decimal where
  negative : Bool
  significand : Nat
  places : Nat
  deriving DecidableEq, Repr

/-- The exact rational `±significand / 10^places` denoted by `d`. -/
def Decimal.value (d : Decimal) : ℚ :=
  let magnitude : ℚ := d.significand / 10 ^ d.places
  if d.negative then -magnitude else magnitude

/-- The binary64 value nearest to `d.value`, ties to even, by FloatLib's rational rounder. -/
def Decimal.round (d : Decimal) : Model FloatFormat.binary64 :=
  Model.roundRat .binary64 d.negative d.significand (10 ^ d.places)

/-- `stripComments inside chars` replaces each block comment by one space. The flag `inside`
records whether a comment is open. An unterminated comment gives `none`. -/
def stripComments : Bool → List Char → Option (List Char)
  | true, [] => none
  | false, [] => some []
  | true, '*' :: '/' :: rest => stripComments false rest
  | true, _ :: rest => stripComments true rest
  | false, '/' :: '*' :: rest => (' ' :: ·) <$> stripComments true rest
  | false, c :: rest => (c :: ·) <$> stripComments false rest

/-- The six ASCII whitespace characters of C. -/
def isSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0b' || c == '\x0c'

/-- `chars` without leading and trailing whitespace. -/
def trim (chars : List Char) : List Char :=
  ((chars.dropWhile isSpace).reverse.dropWhile isSpace).reverse

/-- The natural number written by a nonempty string of ASCII digits, and `none` otherwise. -/
def digits (chars : List Char) : Option Nat :=
  if chars.isEmpty || !chars.all (fun c ↦ '0' ≤ c && c ≤ '9') then none
  else some (chars.foldl (fun n c ↦ 10 * n + (c.toNat - '0'.toNat)) 0)

/-- Reads one literal of the form `-? digits "." digits`, ignoring surrounding whitespace, into a
`Decimal`. Any other spelling gives `none`. -/
def decimal (chars : List Char) : Option Decimal := do
  let chars := trim chars
  let (negative, magnitude) :=
    match chars with
    | '-' :: rest => (true, rest)
    | _ => (false, chars)
  match magnitude.splitOn '.' with
  | [whole, fraction] =>
      let a ← digits whole
      let b ← digits fraction
      return ⟨negative, a * 10 ^ fraction.length + b, fraction.length⟩
  | _ => none

/-- Reads the comma-separated literals of an initializer body after stripping comments, allowing
the trailing comma the source uses. -/
def bodyDecimals (body : List Char) : Option (List Decimal) := do
  let clean ← stripComments false body
  let parts := clean.splitOn ','
  let entries :=
    if (trim (parts.getLastD [])).isEmpty then parts.dropLast else parts
  entries.mapM decimal

/-- `afterPrefix prefix chars` is `chars` without the leading `prefix`, or `none` if `prefix` is
not a prefix of `chars`. -/
def afterPrefix : List Char → List Char → Option (List Char)
  | [], chars => some chars
  | _ :: _, [] => none
  | p :: remaining, c :: chars =>
      if p == c then afterPrefix remaining chars else none

/-- The suffix of the text after the first occurrence of the nonempty `marker`. -/
def findAfter (marker : List Char) : List Char → Option (List Char)
  | [] => none
  | c :: chars =>
      match afterPrefix marker (c :: chars) with
      | some rest => some rest
      | none => findAfter marker chars

/-- The prefix of the text before the first occurrence of the nonempty `marker`. -/
def beforeMarker (marker : List Char) : List Char → Option (List Char)
  | [] => none
  | c :: chars =>
      if (afterPrefix marker (c :: chars)).isSome then some []
      else (c :: ·) <$> beforeMarker marker chars

/-- The text between `static const double NAME[] = {` and the following `};`, provided that
declaration spelling occurs exactly once in `source`. The reader is specific to this shape. -/
def initializer (source : List Char) (name : String) : Option (List Char) := do
  let marker := "static const double ".toList ++ name.toList ++ "[] = {".toList
  let rest ← findAfter marker source
  if (findAfter marker rest).isSome then none
  else beforeMarker "};".toList rest

/-- The decimals of the table `name` in `source`, or `none` when the declaration is missing or
duplicated or a literal is malformed. -/
def tableDecimals (source : List Char) (name : String) : Option (List Decimal) := do
  let body ← initializer source name
  bodyDecimals body

/-- The 64-bit encodings of the rounded decimals of table `name` in `source`. -/
def tableBits (source : List Char) (name : String) : Option (List Nat) :=
  (tableDecimals source name).map (List.map (fun d ↦ d.round.toNatBits))

-- Lex the source text, parse the 55 decimals of `gauss_pts`, round each rationally, compare.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The 55 node literals of the C text round to the words imported from clightgen. -/
theorem node_bits :
    tableBits CSourceData.source "gauss_pts" =
      some Binary64.ClightTableData.nodeBits := by
  decide +kernel

-- Lex the source text, parse the 55 decimals of `gauss_wts`, round each rationally, compare.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The 55 weight literals of the C text round to the words imported from clightgen. -/
theorem weight_bits :
    tableBits CSourceData.source "gauss_wts" =
      some Binary64.ClightTableData.weightBits := by
  decide +kernel

end Quadrature.CSourceTables
