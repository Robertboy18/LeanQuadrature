import Quadrature.CSource.Integrator.Function
import Quadrature.CSource.Integrator.TotalLoop
import Quadrature.CSource.Semantics.ScalarAssignment

/-!
# Total correctness of the complete C integrator call

`integrator_call_correct` starts at a function call, allocates and initializes
the local variables, executes every loop iteration, returns the binary64
fold, and frees the local storage. Every C evaluation order terminates
correctly. The callback and table contents are the reusable interface;
the initialized library discharges them for the concrete quadrature code.
-/

namespace Quadrature.CSource.C

open CC hiding State Cont Step
open Binary64.ClightSource SmallStep

variable [ExternalCalls]

/-- Every call of the integrator on at most ten stored samples returns the exact binary64 fold,
with no stuck or infinite execution and no changes to the caller's existing memory. -/
theorem integrator_call_correct (ge : GlobalEnv) (memory : Mem) (ctx : SourceTableFunctions ge)
    (callback : Block) (callee : FunDef) (f : Floats.Float → Floats.Float)
    (terms : List (Floats.Float × Floats.Float)) (hn : terms.length ≤ 10)
    (hnodes : ctx.nodes < memory.nextblock) (hweights : ctx.weights < memory.nextblock)
    (contract : CallbackCorrect ge (.Vptr callback Integers.Ptrofs.zero) callee f)
    (cells : Binary64.Clight.TableCells memory ctx.nodes ctx.weights terms.length 0 terms) :
    CallCorrect ge memory (.Internal Typed.integrate)
      [.Vptr callback Integers.Ptrofs.zero, .Vint (Integers.Int.repr terms.length)]
      (.Vfloat (Binary64.integrate f terms)) := by
  intro cont hcont
  obtain ⟨entered, entry, parameters, storage, entryMemory⟩ :=
    integrator_entry ge.expressionEnv memory callback terms.length
  have separate := integrator_table_separation memory ctx.nodes ctx.weights hnodes hweights
  have enteredCells :=
    (LoopMemory.of_call (integratorFrame memory) entryMemory).table_cells separate cells
  obtain ⟨summed, ready, hsum, hindex, readyState, initializedMemory⟩ :=
    integrator_initialization_memory (integratorFrame memory) entered
      (.Vptr callback Integers.Ptrofs.zero) terms.length parameters
  apply Total.internal (by simp [Typed.integrate]; constructor <;> rfl) entry
  rw [integrator_body_syntax]
  apply Total.statement (.seq _ _ _ _ _ _)
  apply (assign_constant_total ge (integratorFrame memory).locals entered summed
    _s (integratorFrame memory).accumulator tdouble .Mfloat64 (.Vfloat Binary64.zero)
    rfl rfl rfl rfl hsum Typed.integrate _).bind
  rintro _ rfl
  apply Total.statement (.skip_seq _ _ _ _ _)
  apply Total.statement (.seq _ _ _ _ _ _)
  apply Total.statement (.for_start _ _ _ _ _ _ _ _ (by intro h; cases h))
  apply (assign_constant_total ge (integratorFrame memory).locals summed ready
    _i (integratorFrame memory).index tint .Mint32 (.Vint (Integers.Int.repr 0))
    rfl rfl rfl rfl hindex Typed.integrate _).bind
  rintro _ rfl
  apply Total.statement (.skip_seq _ _ _ _ _)
  apply (integrator_loop_total ge (integratorFrame memory) ready ctx
    (.Vptr callback Integers.Ptrofs.zero) callee f terms.length hn terms 0 Binary64.zero
    (Nat.zero_add _) readyState separate contract
    (initializedMemory.table_cells separate enteredCells) Typed.integrate _).bind
  rintro _ ⟨afterBody, rfl, finalState, loopMemory⟩
  have bodyMemory := initializedMemory.trans loopMemory
  obtain ⟨final, hfree, hmemory⟩ := integrator_free_locals ge.composites memory afterBody
    (storage.after_loop bodyMemory) (integrator_body_memory entryMemory bodyMemory)
  apply Total.statement (.skip_seq _ _ _ _ _)
  apply Total.statement (.return_start _ _ _ _ _)
  apply ((read_local ge.expressionEnv (integratorFrame memory).locals afterBody _s tdouble
    (integratorFrame memory).accumulator .Mfloat64 _ rfl rfl rfl
    finalState.accumulator_load).total Typed.integrate _).bind
  rintro _ rfl
  apply Total.value (.return_finish _ _ _ _ _ _ _ _ rfl hfree)
  exact .done ⟨final, by rw [Cont.callCont_eq hcont]; rfl, hmemory⟩

end Quadrature.CSource.C
