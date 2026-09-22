import Quadrature.CSource.Frontend.ClightEquality
import Quadrature.CSource.Frontend.Translation

/-!
# The original five C functions reproduce their imported Clight syntax

Each theorem starts from the full text of the original C program
(`CSourceData.source`), reads the translation unit, selects the unique
definition of the named function, translates it with
`Quadrature.CSource.Frontend.Translation`, and compares the result by kernel evaluation
with the function imported from clightgen's output in
`Quadrature.Clight.Source`. Equality covers types, temporaries, expression
grouping, calls, loop clauses and statement nesting. The two `_array` theorems
check that the hoisted static tables hold the 55 imported initializer words.
-/

namespace Quadrature.CSource

open Binary64

-- Parse and translate the full source text, then compare the Clight AST of `gauss_point`.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The node accessor of the C text translates to the imported `f_gauss_point`. -/
theorem gauss_point_translation :
    sourceFunction CSourceData.source "gauss_point" = some ClightSource.f_gauss_point := by
  decide +kernel

-- Parse and translate the full source text, then compare the Clight AST of `gauss_weight`.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The weight accessor of the C text translates to the imported `f_gauss_weight`. -/
theorem gauss_weight_translation :
    sourceFunction CSourceData.source "gauss_weight" = some ClightSource.f_gauss_weight := by
  decide +kernel

-- Parse and translate the full source text, then compare the Clight AST of `integrate`.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The integrator of the C text translates to the imported `f_integrate`: its nested calls,
compound addition and three loop clauses produce the same Clight statements. -/
theorem integrate_translation :
    sourceFunction CSourceData.source "integrate" = some ClightSource.f_integrate := by
  decide +kernel

-- Parse and translate the full source text, then compare the Clight AST of `testfun`.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The callback of the C text translates to the imported `f_testfun`, with its call to the
external `cos` and its arithmetic grouping. -/
theorem testfun_translation :
    sourceFunction CSourceData.source "testfun" = some ClightSource.f_testfun := by
  decide +kernel

-- Parse and translate the full source text, then compare the Clight AST of `integrate_testfun`.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The wrapper of the C text translates to the imported `f_integrate_testfun`, passing the
address of `testfun` and the literal `2`. -/
theorem integrate_testfun_translation :
    sourceFunction CSourceData.source "integrate_testfun" =
      some ClightSource.f_integrate_testfun := by
  decide +kernel

/-- The static arrays hoisted while translating the function `name` in `source`, with their
contents as 64-bit encodings. -/
def sourceArrayBits (source : List Char) (name : String) :
    Option (List (String × List Nat)) :=
  (translateSource source name).map fun result ↦
    result.arrays.map fun (text, values) ↦ (text, values.map (·.toNatBits))

-- Parse and translate `gauss_point`, then compare its hoisted table with the imported words.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Translating `gauss_point` hoists one table, `gauss_pts`, holding the 55 imported node
words. -/
theorem gauss_point_array :
    sourceArrayBits CSourceData.source "gauss_point" =
      some [("gauss_pts", ClightTableData.nodeBits)] := by
  decide +kernel

-- Parse and translate `gauss_weight`, then compare its hoisted table with the imported words.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Translating `gauss_weight` hoists one table, `gauss_wts`, holding the 55 imported weight
words. -/
theorem gauss_weight_array :
    sourceArrayBits CSourceData.source "gauss_weight" =
      some [("gauss_wts", ClightTableData.weightBits)] := by
  decide +kernel

end Quadrature.CSource
