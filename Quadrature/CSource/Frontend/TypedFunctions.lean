import Quadrature.CSource.Accessors.TableExpressions
import Quadrature.CSource.Frontend.Elaboration
import Quadrature.CSource.Semantics.Equality

/-!
# Typed C functions obtained from the original source

The `_elaboration` theorems run the parser and the elaborator of
`Quadrature.CSource.Frontend.Elaboration` on the full text of the original C program
and compare the result by kernel evaluation with the expected typed functions
`accessor`, `integrate`, `testfun` and `integrateTestfun`. The expected
functions keep nested calls and source control flow, with local variables in
memory rather than Clight temporaries.

For each accessor, the parsed return expression is also connected to the
pure-phase theorem `table_read_from_memory`. That connection evaluates the
expression alone, given the parameter and table loads. Entry, return and full
calls of the same accessors are proved in `Quadrature.CSource.Accessors.Entry`,
`Quadrature.CSource.Accessors.Return` and `Quadrature.CSource.Accessors.Calls`.
-/

namespace Quadrature.CSource.Typed

open CC Binary64.ClightSource

private def readVar (name : Ident) (type : Ty) : C.Expr :=
  .Evalof (.Evar name type) type

private def integer (n : Nat) : C.Expr :=
  .Eval (.Vint (Integers.Int.repr n)) tint

private def accessorType : Ty := .Tfunction [tint, tint] tdouble cc_default

private def callbackType : Ty := .Tfunction [tdouble] tdouble cc_default

private def accessorCall (name : Ident) : C.Expr :=
  .Ecall (readVar name accessorType)
    (.Econs (readVar _i tint) (.Econs (readVar _n tint) .Enil)) tdouble

/-- The typed C function of either table accessor: parameters `i` and `npts`, no locals, body
`return accessorRead table;`. -/
def accessor (table : Ident) : C.Function where
  fn_return := tdouble
  fn_callconv := cc_default
  fn_params := [(_i, tint), (_npts, tint)]
  fn_vars := []
  fn_body := .Sreturn (some (C.accessorRead table))

/-- The typed C integrator: parameters `f` and `n`, locals `i` and `s` in memory, and the body
`s = 0.0; for (i = 0; i < n; i++) s += gauss_weight(i, n) * f(gauss_point(i, n)); return s;`
with its calls in place. -/
def integrate : C.Function where
  fn_return := tdouble
  fn_callconv := cc_default
  fn_params := [(_f, tptr callbackType), (_n, tint)]
  fn_vars := [(_i, tint), (_s, tdouble)]
  fn_body :=
    .Ssequence
      (.Sdo (.Eassign (.Evar _s tdouble)
        (.Eval (.Vfloat (Floats.Float.ofBits (Integers.Int64.repr 0))) tdouble) tdouble))
      (.Ssequence
        (.Sfor
          (.Sdo (.Eassign (.Evar _i tint) (integer 0) tint))
          (.Ebinop .Olt (readVar _i tint) (readVar _n tint) tint)
          (.Sdo (.Epostincr .incr (.Evar _i tint) tint))
          (.Sdo (.Eassignop .Oadd (.Evar _s tdouble)
            (.Ebinop .Omul (accessorCall _gauss_weight)
              (.Ecall (readVar _f (tptr callbackType))
                (.Econs (accessorCall _gauss_point) .Enil) tdouble) tdouble)
            tdouble tdouble)))
        (.Sreturn (some (readVar _s tdouble))))

/-- The typed C callback: parameter `x` and body `return 0.5 * (1 - x) * cos(x);`, with the call
to the external `cos` in place. -/
def testfun : C.Function where
  fn_return := tdouble
  fn_callconv := cc_default
  fn_params := [(_x, tdouble)]
  fn_vars := []
  fn_body := .Sreturn (some
    (.Ebinop .Omul
      (.Ebinop .Omul
        (.Eval (.Vfloat (Floats.Float.ofBits (Integers.Int64.repr 4602678819172646912)))
          tdouble)
        (.Ebinop .Osub (integer 1) (readVar _x tdouble) tdouble) tdouble)
      (.Ecall (readVar _cos callbackType) (.Econs (readVar _x tdouble) .Enil) tdouble)
      tdouble))

/-- The typed C wrapper: no parameters and body `return integrate(&testfun, 2);`. -/
def integrateTestfun : C.Function where
  fn_return := tdouble
  fn_callconv := cc_default
  fn_params := []
  fn_vars := []
  fn_body := .Sreturn (some
    (.Ecall (readVar _integrate
      (.Tfunction [tptr callbackType, tint] tdouble cc_default))
      (.Econs (.Eaddrof (.Evar _testfun callbackType) (tptr callbackType))
        (.Econs (integer 2) .Enil)) tdouble))

-- Parse and elaborate the full source text, then compare the typed AST of `gauss_point`.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The node accessor of the C text elaborates to `accessor _gauss_pts`. -/
theorem gauss_point_elaboration :
    typedSourceFunction CSourceData.source "gauss_point" =
      some (accessor _gauss_pts) := by
  decide +kernel

-- Parse and elaborate the full source text, then compare the typed AST of `gauss_weight`.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The weight accessor of the C text elaborates to `accessor _gauss_wts`. -/
theorem gauss_weight_elaboration :
    typedSourceFunction CSourceData.source "gauss_weight" =
      some (accessor _gauss_wts) := by
  decide +kernel

-- Parse and elaborate the full source text, then compare the typed AST of `integrate`.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The integrator of the C text elaborates to `integrate`. -/
theorem integrate_elaboration :
    typedSourceFunction CSourceData.source "integrate" = some integrate := by
  decide +kernel

-- Parse and elaborate the full source text, then compare the typed AST of `testfun`.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The callback of the C text elaborates to `testfun`. -/
theorem testfun_elaboration :
    typedSourceFunction CSourceData.source "testfun" = some testfun := by
  decide +kernel

-- Parse and elaborate the full source text, then compare the typed AST of `integrate_testfun`.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The wrapper of the C text elaborates to `integrateTestfun`. -/
theorem integrate_testfun_elaboration :
    typedSourceFunction CSourceData.source "integrate_testfun" =
      some integrateTestfun := by
  decide +kernel

/-- The static arrays hoisted while elaborating the function `name` in `source`, with their
contents as 64-bit encodings. -/
def sourceArrayBits (source : List Char) (name : String) :
    Option (List (String × List Nat)) :=
  (elaborateSource source name).map fun result ↦
    result.arrays.map fun (text, values) ↦ (text, values.map (·.toNatBits))

-- Parse and elaborate `gauss_point`, then compare its hoisted table with the imported words.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Elaborating `gauss_point` hoists one table, `gauss_pts`, holding the 55 imported node
words. -/
theorem gauss_point_array :
    sourceArrayBits CSourceData.source "gauss_point" =
      some [("gauss_pts", Binary64.ClightTableData.nodeBits)] := by
  decide +kernel

-- Parse and elaborate `gauss_weight`, then compare its hoisted table with the imported words.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Elaborating `gauss_weight` hoists one table, `gauss_wts`, holding the 55 imported weight
words. -/
theorem gauss_weight_array :
    sourceArrayBits CSourceData.source "gauss_weight" =
      some [("gauss_wts", Binary64.ClightTableData.weightBits)] := by
  decide +kernel

/-- The operand of the `return` when the elaborated function `name` in `source` consists of one
`return` statement, and `none` otherwise. -/
def sourceReturnExpression (source : List Char) (name : String) : Option C.Expr := do
  let function ← typedSourceFunction source name
  match function.fn_body with
  | .Sreturn (some value) => some value
  | _ => none

/-- The return expression of the node accessor of the C text is `accessorRead _gauss_pts`. -/
theorem gauss_point_return_expression :
    sourceReturnExpression CSourceData.source "gauss_point" =
      some (C.accessorRead _gauss_pts) := by
  simp [sourceReturnExpression, gauss_point_elaboration, accessor]

/-- The return expression of the weight accessor of the C text is `accessorRead _gauss_wts`. -/
theorem gauss_weight_return_expression :
    sourceReturnExpression CSourceData.source "gauss_weight" =
      some (C.accessorRead _gauss_wts) := by
  simp [sourceReturnExpression, gauss_weight_elaboration, accessor]

/-- `ReturnExpressionEvaluates source name ge locals memory value`: the function `name` in
`source` elaborates to a single `return`, whose operand evaluates in the pure phase to `value` in
environment `locals` and memory `memory`. Entry and return of the function are covered by
`SourceFunctionEntry` and `SourceFunctionCall`. -/
def ReturnExpressionEvaluates (source : List Char) (name : String)
    (ge : C.ExpressionEnv) (locals : Env) (memory : Mem) (value : Val) : Prop :=
  ∃ expression, sourceReturnExpression source name = some expression ∧
    C.EvalRvalue ge locals memory expression value

/-- Assume `n` and `i` (both at most 10) are in the parameter blocks and `value` is at
`8 * tableOffset n i` in the `gauss_pts` block. Then the return expression of the node accessor
of the C text evaluates to `Vfloat value`. -/
theorem gauss_point_return_from_memory (ge : CGenv) (m : Mem)
    (count index tableBlock : Block) (n i : Nat) (value : Floats.Float)
    (hn : n ≤ 10) (hi : i ≤ 10)
    (hsym : Genv.findSymbol ge.genv_genv _gauss_pts = some tableBlock)
    (hc : Mem.load .Mint32 m count 0 = some (.Vint (Integers.Int.repr n)))
    (hx : Mem.load .Mint32 m index 0 = some (.Vint (Integers.Int.repr i)))
    (hload : Mem.load .Mfloat64 m tableBlock (8 * Binary64.Clight.tableOffset n i : Nat) =
      some (.Vfloat value)) :
    ReturnExpressionEvaluates CSourceData.source "gauss_point"
      (.ofClight ge) (C.accessorLocals count index) m (.Vfloat value) := by
  refine ⟨_, gauss_point_return_expression, ?_⟩
  exact C.table_read_from_memory ge m count index tableBlock _gauss_pts n i value hn hi
    (by decide +kernel) (by decide +kernel) hsym hc hx hload

/-- The same statement for the weight accessor and the `gauss_wts` block. -/
theorem gauss_weight_return_from_memory (ge : CGenv) (m : Mem)
    (count index tableBlock : Block) (n i : Nat) (value : Floats.Float)
    (hn : n ≤ 10) (hi : i ≤ 10)
    (hsym : Genv.findSymbol ge.genv_genv _gauss_wts = some tableBlock)
    (hc : Mem.load .Mint32 m count 0 = some (.Vint (Integers.Int.repr n)))
    (hx : Mem.load .Mint32 m index 0 = some (.Vint (Integers.Int.repr i)))
    (hload : Mem.load .Mfloat64 m tableBlock (8 * Binary64.Clight.tableOffset n i : Nat) =
      some (.Vfloat value)) :
    ReturnExpressionEvaluates CSourceData.source "gauss_weight"
      (.ofClight ge) (C.accessorLocals count index) m (.Vfloat value) := by
  refine ⟨_, gauss_weight_return_expression, ?_⟩
  exact C.table_read_from_memory ge m count index tableBlock _gauss_wts n i value hn hi
    (by decide +kernel) (by decide +kernel) hsym hc hx hload

end Quadrature.CSource.Typed
