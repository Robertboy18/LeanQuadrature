import Quadrature.CSource.Cosine.Clight
import Quadrature.CSource.Library.Initialization

/-!
# The initialized Clight output of the C frontend

`fromSources` normalizes all six selected functions, including the shipped
cosine, and retains the two static tables. `from_sources` identifies its
output with `program`. This differs from the earlier authored Clight
polynomial: the cosine keeps the source parameter and signed literals.

Initialization agrees with the C library. `internal` proves that all callable
definitions use the closed structured fragment, so their executions require
no assumption about external calls.
-/

namespace Quadrature.CSource.Library.Normalized

open CC Binary64 Binary64.ClightSource

private def assemble (nodes weights : List Nat)
    (point weight integrate callback wrapper cosine : CC.Function) : CC.Program :=
  CC.mkprogram []
    [(_gauss_pts, .Gvar (Clight.tableGlobal nodes)),
     (_gauss_wts, .Gvar (Clight.tableGlobal weights)),
     (_gauss_point, .Gfun (.Internal point)),
     (_gauss_weight, .Gfun (.Internal weight)),
     (_integrate, .Gfun (.Internal integrate)),
     (_testfun, .Gfun (.Internal callback)),
     (_integrate_testfun, .Gfun (.Internal wrapper)),
     (_cos, .Gfun (.Internal cosine))]
    [_gauss_point, _gauss_weight, _integrate, _testfun, _integrate_testfun, _cos]
    _integrate_testfun

/-- The complete Clight output of the restricted frontend on the selected library. -/
def program : CC.Program :=
  assemble ClightTableData.nodeBits ClightTableData.weightBits
    f_gauss_point f_gauss_weight f_integrate f_testfun f_integrate_testfun
    Cosine.normalizedFunction

/-- Normalize the selected functions and their static arrays, failing on missing definitions,
unexpected tables or table lengths other than 55. -/
def fromSources (original replacement : List Char) : Option CC.Program := do
  let point ← sourceFunction original "gauss_point"
  let weight ← sourceFunction original "gauss_weight"
  let integrate ← sourceFunction original "integrate"
  let callback ← sourceFunction original "testfun"
  let wrapper ← sourceFunction original "integrate_testfun"
  let cosine ← sourceFunction replacement "cos"
  let [("gauss_pts", nodes)] ← CSource.sourceArrayBits original "gauss_point" | none
  let [("gauss_wts", weights)] ← CSource.sourceArrayBits original "gauss_weight" | none
  let [] ← CSource.sourceArrayBits replacement "cos" | none
  if nodes.length != 55 || weights.length != 55 then none
  else some (assemble nodes weights point weight integrate callback wrapper cosine)

/-- Normalizing both source files yields `program`, including the replacement cosine body. -/
theorem from_sources :
    fromSources CSourceData.source Cosine.source = some program := by
  simp only [fromSources, gauss_point_translation, gauss_weight_translation,
    integrate_translation, testfun_translation, integrate_testfun_translation, Cosine.translation,
    gauss_point_array, gauss_weight_array, Cosine.normalized_no_arrays]
  rfl

-- Global allocation reads the table initializers, independently of the function bodies.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The normalized library initializes to the same memory as the typed C library. -/
theorem initialized : program.initMem = some Library.initialMemory := by
  have h : program.initMem = Clight.polynomialLibrary.initMem := rfl
  rw [h]
  exact Clight.polynomialLibrary_initialized

/-- Both frontend outputs have the same initialized global memory. -/
theorem initialization_agrees : program.initMem = Library.polynomialLibrary.initMem := by
  exact initialized.trans (Library.initialized (.Internal Cosine.function)).symm

/-- The frontend output contains only internal structured functions. -/
theorem internal : Clight.InternalProgram program := by
  unfold Clight.InternalProgram program assemble
  decide +kernel

/-- The normalized library has the same table and accessor blocks as the C library. -/
def tableFunctions : Clight.TableFunctions program.globalenv where
  nodes := Positive.ofNat 1
  weights := Positive.ofNat 2
  point := Positive.ofNat 3
  weight := Positive.ofNat 4
  nodes_symbol := rfl
  weights_symbol := rfl
  point_symbol := rfl
  weight_symbol := rfl
  point_function := rfl
  weight_function := rfl

/-- Its initialized tables contain every stored order, including the empty rule. -/
def storedContext (n : Nat) (hn : n ≤ 10) :
    Clight.StoredLibraryContext program.globalenv Library.initialMemory (Clight.storedTerms n) where
  toTableFunctions := tableFunctions
  count_bound := by rw [Clight.stored_terms_length n hn]; exact hn
  cells := by
    rw [Clight.stored_terms_length n hn]
    exact Clight.stored_table_cells n hn

/-- The normalized callback retains the same global block as the C callback. -/
theorem callback_function :
    Genv.findFunct program.globalenv.genv_genv
      (.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero) = some (.Internal f_testfun) := rfl

/-- `cos` resolves to the normalized source function, not to an external contract. -/
theorem cosine_function :
    Genv.findFunct program.globalenv.genv_genv
      (.Vptr (Positive.ofNat 8) Integers.Ptrofs.zero) =
        some (.Internal Cosine.normalizedFunction) := rfl

end Quadrature.CSource.Library.Normalized
