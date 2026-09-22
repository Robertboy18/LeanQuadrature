import Quadrature.CSource.Semantics.Control

/-!
# Total correctness of the C table accessors

`accessor_call_correct` covers all expression evaluation orders as well as
allocation, parameter stores, the return cast and freeing. It requires the
requested table cell and the original index bounds.
-/

namespace Quadrature.CSource.C

open CC hiding State Cont Step
open Binary64.ClightSource SmallStep

variable [ExternalCalls]

/-- Every permitted execution of a table accessor returns its loaded binary64 cell and
preserves all memory that existed before the call. -/
theorem accessor_call_correct (ge : GlobalEnv) (memory : Mem)
    (table : Ident) (tableBlock : Block) (n i : Nat) (value : Floats.Float)
    (hn : n ≤ 10) (hi : i ≤ 10) (hnamei : table ≠ _i) (hnamen : table ≠ _npts)
    (hsym : Genv.findSymbol ge.globals table = some tableBlock)
    (hload : Mem.load .Mfloat64 memory tableBlock
      (8 * Binary64.Clight.tableOffset n i : Nat) = some (.Vfloat value)) :
    CallCorrect ge memory (.Internal (Typed.accessor table))
      [.Vint (Integers.Int.repr i), .Vint (Integers.Int.repr n)] (.Vfloat value) := by
  intro cont hcont
  obtain ⟨entered, hentry⟩ := accessor_initialization_exists ge.expressionEnv memory n i
  have hread := accessor_read_in_c_environment ge entered
    memory.nextblock.succ memory.nextblock tableBlock table n i value hn hi
    hnamei hnamen hsym hentry.count_load hentry.index_load (hentry.preserve_load hload)
  apply Total.internal (by simp [Typed.accessor]; rfl)
    (hentry.function_entry table)
  apply Total.statement (.return_start _ _ _ _ _)
  apply (hread.total (Typed.accessor table) _).bind
  rintro state rfl
  apply Total.value (.return_finish _ _ _ _ _ _ _ _ rfl hentry.free_locals)
  exact .done ⟨accessorReturnedMemory memory entered,
    by rw [Cont.callCont_eq hcont], hentry.call_memory⟩

end Quadrature.CSource.C
