import Quadrature.CSource.Integrator.Return

/-!
# Calling the original C integrator end to end

`integrator_call` composes entry, the source body, the return cast and local
freeing into an `EvalFuncall` of the typed integrator, returning the exact
binary64 fold for up to ten stored samples and satisfying `CallMemory`. Table
lookup and callback execution are explicit hypotheses (`SourceTableFunctions`,
`TableCells`, `SourceCallbackContract`). No store, local load, loop execution
or free success is assumed. `integrate_call` identifies the function with the
one elaborated from the original C program.
-/

namespace Quadrature.CSource.C

open CC

variable [ExternalCalls]

/-- Assume `SourceTableFunctions`, a callback pointer meeting `SourceCallbackContract` for `f`,
and the `TableCells` of `terms` (at most ten) in tables older than the call. Then calling
`Typed.integrate` with the pointer and `terms.length` returns `Vfloat (integrate f terms)`
silently in a memory satisfying `CallMemory`. -/
theorem integrator_call (ge : GlobalEnv) (memory : Mem) (ctx : SourceTableFunctions ge)
    (callback : Block) (function : FunDef) (f : Floats.Float → Floats.Float)
    (terms : List (Floats.Float × Floats.Float)) (hn : terms.length ≤ 10)
    (hnodes : ctx.nodes < memory.nextblock) (hweights : ctx.weights < memory.nextblock)
    (contract : SourceCallbackContract ge (.Vptr callback Integers.Ptrofs.zero) function f)
    (cells : Binary64.Clight.TableCells memory ctx.nodes ctx.weights terms.length 0 terms) :
    ∃ final,
      EvalFuncall ge memory (.Internal Typed.integrate)
        [.Vptr callback Integers.Ptrofs.zero, .Vint (Integers.Int.repr terms.length)]
        E0 final (.Vfloat (Binary64.integrate f terms)) ∧ CallMemory memory final := by
  obtain ⟨entered, entry, parameters, storage, entryMemory⟩ :=
    integrator_entry ge.expressionEnv memory callback terms.length
  have separate := integrator_table_separation memory ctx.nodes ctx.weights hnodes hweights
  have enteredCells :=
    (LoopMemory.of_call (integratorFrame memory) entryMemory).table_cells separate cells
  obtain ⟨afterBody, body, _, bodyMemory⟩ :=
    integrator_body ge (integratorFrame memory) entered ctx
      (.Vptr callback Integers.Ptrofs.zero) function f terms hn parameters
      separate contract enteredCells
  obtain ⟨final, hfree, hmemory⟩ := integrator_free_locals ge.composites memory afterBody
    (storage.after_loop bodyMemory) (integrator_body_memory entryMemory bodyMemory)
  exact ⟨final, entry.eval_funcall body ⟨by decide, rfl⟩ hfree, hmemory⟩

end Quadrature.CSource.C

namespace Quadrature.CSource.Typed

open CC

variable [ExternalCalls]

/-- `integrator_call` restated for the function that parsing and elaborating the original C text
of `integrate` produces. -/
theorem integrate_call (ge : C.GlobalEnv) (memory : Mem) (ctx : C.SourceTableFunctions ge)
    (callback : Block) (function : C.FunDef) (f : Floats.Float → Floats.Float)
    (terms : List (Floats.Float × Floats.Float)) (hn : terms.length ≤ 10)
    (hnodes : ctx.nodes < memory.nextblock) (hweights : ctx.weights < memory.nextblock)
    (contract : C.SourceCallbackContract ge (.Vptr callback Integers.Ptrofs.zero) function f)
    (cells : Binary64.Clight.TableCells memory ctx.nodes ctx.weights terms.length 0 terms) :
    ∃ final,
      SourceFunctionCall CSourceData.source "integrate" ge
        [.Vptr callback Integers.Ptrofs.zero, .Vint (Integers.Int.repr terms.length)]
        memory E0 final (.Vfloat (Binary64.integrate f terms)) ∧ C.CallMemory memory final := by
  obtain ⟨final, hcall, hmemory⟩ :=
    C.integrator_call ge memory ctx callback function f terms hn hnodes hweights contract cells
  exact ⟨final, ⟨integrate, integrate_elaboration, hcall⟩, hmemory⟩

end Quadrature.CSource.Typed
