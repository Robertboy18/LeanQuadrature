import Quadrature.CSource.Integrator.Calls
import Quadrature.CSource.Accessors.Total
import Quadrature.CSource.Callback.Total

/-!
# The loop's nested calls in every evaluation order

`weighted_sample_read_eval` covers the weight lookup, node lookup, and
callback call inside one loop iteration. Each call preserves the caller's
memory, so evaluating another operand first leaves all local and table
reads valid.
-/

namespace Quadrature.CSource.C

open CC Binary64.ClightSource FloatLib.Floats.Formats.BinaryInterchange

variable [ExternalCalls]

/-- An accessor call retains its table value after any preceding calls that preserve memory. -/
theorem accessor_read_eval (ge : GlobalEnv) (frame : IntegratorFrame) (memory : Mem)
    (name table : Ident) (functionBlock tableBlock : Block)
    (callback : Val) (n i : Nat) (accumulator value : Floats.Float)
    (hn : n ≤ 10) (hi : i ≤ 10)
    (state : IntegratorState frame memory callback n i accumulator)
    (hname : frame.locals.get name = none)
    (hnamei : table ≠ _i) (hnamen : table ≠ _npts)
    (hsym : Genv.findSymbol ge.globals name = some functionBlock)
    (hfun : Genv.findFunct ge.globals (.Vptr functionBlock Integers.Ptrofs.zero) =
      some (.Internal (Typed.accessor table)))
    (htable : Genv.findSymbol ge.globals table = some tableBlock)
    (hload : Mem.load .Mfloat64 memory tableBlock
      (8 * Binary64.Clight.tableOffset n i : Nat) = some (.Vfloat value)) :
    ReadEval ge frame.locals memory .RV (accessorCall name) (.value (.Vfloat value)) := by
  apply ReadEval.call (pointer := .Vptr functionBlock Integers.Ptrofs.zero)
    (parameters := [tint, tint]) (returnType := tdouble) (cc := cc_default)
    (function := .Internal (Typed.accessor table))
    (values := [.Vint (Integers.Int.repr i), .Vint (Integers.Int.repr n)])
  · exact .global_function ge _ memory name functionBlock [tint, tint] tdouble cc_default
      hname hsym
  · exact .cons _ _ _ _ _ _ _
      (.local ge _ memory _i tint frame.index .Mint32 (.Vint (Integers.Int.repr i))
        rfl rfl rfl state.index_load) (fun _ _ => rfl)
      (.cons _ _ _ _ _ _ _
        (.local ge _ memory _n tint frame.count .Mint32 (.Vint (Integers.Int.repr n))
          rfl rfl rfl state.count_load) (fun _ _ => rfl) .nil)
  · exact hfun
  · rfl
  · rfl
  · intro current hmemory
    exact accessor_call_correct ge current table tableBlock n i value hn hi hnamei hnamen
      htable (hmemory.load hload)

/-- All permitted orders of the three nested calls produce the same rounded weighted sample. -/
theorem weighted_sample_read_eval (ge : GlobalEnv) (frame : IntegratorFrame) (memory : Mem)
    (ctx : SourceTableFunctions ge) (callback : Val) (function : FunDef)
    (f : Floats.Float → Floats.Float) (n i : Nat) (accumulator weight node : Floats.Float)
    (hn : n ≤ 10) (hi : i ≤ 10)
    (state : IntegratorState frame memory callback n i accumulator)
    (contract : CallbackCorrect ge callback function f)
    (hweight : Mem.load .Mfloat64 memory ctx.weights
      (8 * Binary64.Clight.tableOffset n i : Nat) = some (.Vfloat weight))
    (hnode : Mem.load .Mfloat64 memory ctx.nodes
      (8 * Binary64.Clight.tableOffset n i : Nat) = some (.Vfloat node)) :
    ReadEval ge frame.locals memory .RV weightedSample
      (.value (.Vfloat (Model.mul weight (f node)))) := by
  apply ReadEval.binop (leftValue := .Vfloat weight) (rightValue := .Vfloat (f node))
  · exact accessor_read_eval ge frame memory _gauss_weight _gauss_wts ctx.weight ctx.weights
      callback n i accumulator weight hn hi state rfl (by decide +kernel) (by decide +kernel)
      ctx.weight_symbol ctx.weight_function ctx.weights_symbol hweight
  · apply ReadEval.call (pointer := callback) (parameters := [tdouble])
      (returnType := tdouble) (cc := cc_default) (function := function)
      (values := [.Vfloat node])
    · exact .local ge _ memory _f (tptr callbackType) frame.callback Mptr callback
        rfl rfl rfl state.callback_load
    · exact .cons _ _ _ _ _ _ _
        (accessor_read_eval ge frame memory _gauss_point _gauss_pts ctx.point ctx.nodes
          callback n i accumulator node hn hi state rfl (by decide +kernel)
          (by decide +kernel) ctx.point_symbol ctx.point_function ctx.nodes_symbol hnode)
        (fun _ _ => rfl) .nil
    · exact contract.function_eq
    · exact contract.type_eq
    · rfl
    · intro current _
      exact contract.execution current node
  · intro current _
    rfl

end Quadrature.CSource.C
