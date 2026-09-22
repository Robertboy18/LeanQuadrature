import Quadrature.CSource.Cosine.Function
import Quadrature.CSource.Semantics.GlobalInitialization
import Quadrature.CSource.Wrapper.Function
import Quadrature.Clight.StoredRules

/-!
# The initialized C quadrature library

`fromSources` reads the five one-dimensional functions and their two static
tables from the retained original source, then the polynomial from `cosine.c`.
`from_sources` identifies the resulting library with `polynomialLibrary`.
The original file's two-dimensional routines are not part of this library.

`initialized` proves allocation of all eight globals succeeds.
`tableFunctions`, `wrapperFunctions` and `table_cells` discharge the symbol,
function and storage premises of the C execution theorems. Global initialization
ignores function bodies, so its memory agrees with the already checked Clight
initial memory; this equality concerns storage, not a compiler pass.
-/

namespace Quadrature.CSource.Library

open CC Binary64 Binary64.ClightSource

private def assemble (nodes weights : List Nat)
    (point weight integrate callback wrapper : C.Function) (cosine : C.FunDef) : C.Library where
  definitions :=
    [(_gauss_pts, .Gvar (Clight.tableGlobal nodes)),
     (_gauss_wts, .Gvar (Clight.tableGlobal weights)),
     (_gauss_point, .Gfun (.Internal point)),
     (_gauss_weight, .Gfun (.Internal weight)),
     (_integrate, .Gfun (.Internal integrate)),
     (_testfun, .Gfun (.Internal callback)),
     (_integrate_testfun, .Gfun (.Internal wrapper)),
     (_cos, .Gfun cosine)]
  publicNames := [_gauss_point, _gauss_weight, _integrate, _testfun, _integrate_testfun, _cos]
  composites := PTree.empty

/-- The original five one-dimensional functions and both tables, with `cosine` at `cos`. -/
def withCosine (cosine : C.FunDef) : C.Library :=
  assemble ClightTableData.nodeBits ClightTableData.weightBits
    (Typed.accessor _gauss_pts) (Typed.accessor _gauss_wts) Typed.integrate Typed.testfun
    Typed.integrateTestfun cosine

/-- The C library using the internal polynomial in place of the external cosine. -/
def polynomialLibrary : C.Library := withCosine (.Internal Cosine.function)

/-- Parse the selected functions, their 55-entry tables and the replacement cosine, failing
if a definition, expected table name, table length or supported syntax is absent. -/
def fromSources (original replacement : List Char) : Option C.Library := do
  let point ← typedSourceFunction original "gauss_point"
  let weight ← typedSourceFunction original "gauss_weight"
  let integrate ← typedSourceFunction original "integrate"
  let callback ← typedSourceFunction original "testfun"
  let wrapper ← typedSourceFunction original "integrate_testfun"
  let cosine ← typedSourceFunction replacement "cos"
  let [("gauss_pts", nodes)] ← Typed.sourceArrayBits original "gauss_point" | none
  let [("gauss_wts", weights)] ← Typed.sourceArrayBits original "gauss_weight" | none
  let [] ← Typed.sourceArrayBits replacement "cos" | none
  if nodes.length != 55 || weights.length != 55 then none
  else some (assemble nodes weights point weight integrate callback wrapper (.Internal cosine))

/-- The retained original C text and the shipped polynomial produce `polynomialLibrary`. -/
theorem from_sources :
    fromSources CSourceData.source Cosine.source = some polynomialLibrary := by
  simp only [fromSources, Typed.gauss_point_elaboration, Typed.gauss_weight_elaboration,
    Typed.integrate_elaboration, Typed.testfun_elaboration, Typed.integrate_testfun_elaboration,
    Cosine.elaboration, Typed.gauss_point_array, Typed.gauss_weight_array, Cosine.no_arrays]
  rfl

-- Reduce global allocation; the definitions' C function bodies are never inspected.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- Initialization succeeds for any definition of `cos`; the two table initializers determine
the same memory as in the Clight library. -/
theorem initialized (cosine : C.FunDef) :
    (withCosine cosine).initMem = some Clight.initialMemory := by
  have h : (withCosine cosine).initMem = Clight.polynomialLibrary.initMem := by rfl
  rw [h]
  exact Clight.polynomialLibrary_initialized

/-- The global environment of the polynomial C library. -/
def globalEnv : C.GlobalEnv := polynomialLibrary.globalEnv

/-- The actual initial memory of the C library. Its initialization succeeds by `initialized`. -/
def initialMemory : Mem := Clight.initialMemory

/-- The table and accessor symbols, with their parsed C definitions, are all resolved. -/
def tableFunctions (cosine : C.FunDef) :
    C.SourceTableFunctions (withCosine cosine).globalEnv where
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

/-- The integrator and callback symbols resolve to their parsed C definitions. -/
def wrapperFunctions (cosine : C.FunDef) :
    C.SourceWrapperFunctions (withCosine cosine).globalEnv where
  integrator := Positive.ofNat 5
  callback := Positive.ofNat 6
  integrator_symbol := rfl
  callback_symbol := rfl
  integrator_function := rfl
  callback_function := rfl

/-- The wrapper itself is installed at block 7. -/
theorem wrapper_function (cosine : C.FunDef) :
    Genv.findFunct (withCosine cosine).globalEnv.globals
      (.Vptr (Positive.ofNat 7) Integers.Ptrofs.zero) =
        some (.Internal Typed.integrateTestfun) := rfl

/-- The symbol `cos` is installed at block 8. -/
theorem cosine_symbol (cosine : C.FunDef) :
    Genv.findSymbol (withCosine cosine).globalEnv.globals _cos = some (Positive.ofNat 8) := rfl

/-- The function at `cos` is exactly the definition supplied to `withCosine`. -/
theorem cosine_function (cosine : C.FunDef) :
    Genv.findFunct (withCosine cosine).globalEnv.globals
      (.Vptr (Positive.ofNat 8) Integers.Ptrofs.zero) = some cosine := rfl

/-- Every stored rule, including the empty zero-node rule, is present at its C offsets. -/
theorem table_cells (cosine : C.FunDef) (n : Nat) (hn : n ≤ 10) :
    Clight.TableCells initialMemory (tableFunctions cosine).nodes
      (tableFunctions cosine).weights n 0 (Clight.storedTerms n) :=
  Clight.stored_table_cells n hn

-- Reduce the next-block field of the successfully initialized eight-global library.
set_option maxRecDepth 20000 in
/-- All eight globals have been allocated before any library call begins. -/
theorem initial_nextblock : initialMemory.nextblock = Positive.ofNat 9 := by rfl

end Quadrature.CSource.Library
