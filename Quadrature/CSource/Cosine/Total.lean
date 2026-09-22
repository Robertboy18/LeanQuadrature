import Quadrature.CSource.Cosine.Function
import Quadrature.CSource.Semantics.ReadVariables

/-!
# Total correctness of the internal C cosine

`call_correct` proves that every execution permitted by the full C machine
terminates with the FloatLib polynomial's value. It includes parameter
allocation, evaluation in any operand order, the square's store, Horner
evaluation, and freeing the parameter block.
-/

namespace Quadrature.CSource.Cosine

open CC hiding State Cont Step
open Binary64 FloatLib.Floats.Formats.BinaryInterchange Binary64.ClightSource
open C.SmallStep

variable [ExternalCalls]

/-- Every execution of the internal cosine returns its specified binary64 polynomial value
and preserves the caller's memory. -/
theorem call_correct (ge : C.GlobalEnv) (memory : Mem) (x : Floats.Float) :
    CallCorrect ge memory (.Internal function) [.Vfloat x]
      (.Vfloat (Polynomial.cosine x)) := by
  intro cont hcont
  obtain ⟨entered, hentry, hload, hfreeable, hentryMemory⟩ :=
    C.testfun_entry ge.expressionEnv memory x
  have hfunctionEntry :
      C.FunctionEntry ge.expressionEnv function [.Vfloat x]
        memory (C.testfunLocals memory.nextblock) entered :=
    ⟨hentry.names_unique, hentry.allocated_and_bound⟩
  have hread := C.ReadEval.local ge (C.testfunLocals memory.nextblock) entered
    _x tdouble memory.nextblock .Mfloat64 (.Vfloat x) rfl rfl rfl hload
  have hsquare :
      C.StoreExpr ge (C.testfunLocals memory.nextblock) entered
        memory.nextblock Integers.Ptrofs.zero tdouble
        (.Vfloat (Model.mul x x)) squareAssignment :=
    .assign _ _ _ (.var_local _ _ _ rfl)
      (.binop _ _ _ _ _ _ _ hread hread (fun _ _ => rfl)) rfl (fun _ _ => rfl)
  have hwrite : Mem.validAccess entered .Mfloat64 memory.nextblock 0 .Writable = true := by
    have h := Mem.rangePerm_implies hfreeable
      (show permOrder .Freeable .Writable = true from rfl)
    simpa [Mem.validAccess, sizeChunk, alignChunk] using h
  have hstores : ∀ before, C.CallMemory entered before → ∃ after,
      Mem.storev .Mfloat64 before (.Vptr memory.nextblock Integers.Ptrofs.zero)
        (.Vfloat (Model.mul x x)) = some after := by
    intro before hbefore
    have hw := (hbefore.valid_access .Mfloat64 memory.nextblock 0 .Writable
      (C.block_valid_of_load hload)).trans hwrite
    change ∃ after,
      Mem.store .Mfloat64 before memory.nextblock 0 (.Vfloat (Model.mul x x)) = some after
    simp only [Mem.store, hw, ite_true]
    exact ⟨_, rfl⟩
  apply Total.internal (by simp [function]; rfl) hfunctionEntry
  apply Total.statement (.seq _ _ _ _ _ _)
  apply Total.statement (.do_start _ _ _ _ _)
  apply (hsquare.total (.refl _) rfl rfl hstores function _).bind
  rintro state ⟨before, squared, hbefore, hstore, rfl⟩
  have hsquareLoad := Mem.load_store_same hstore
  have hsquareFree : Mem.rangePerm squared memory.nextblock 0 8 .Cur .Freeable = true := by
    rw [Mem.rangePerm_store_eq hstore]
    exact hbefore.range_perm (C.block_valid_of_load hload) hfreeable
  have hsquareMemory := (hentryMemory.trans hbefore).store_fresh hstore (Nat.le_refl _)
  have hreturn := horner_value ge.expressionEnv squared memory.nextblock
    (Model.mul x x) coefficients hsquareLoad
  rw [coefficient_values] at hreturn
  obtain ⟨final, hfree, hmemory⟩ :=
    C.testfun_free ge.composites memory squared squared (Model.mul x x)
      hsquareLoad hsquareFree hsquareMemory (.refl _)
  apply Total.value (.do_finish _ _ _ _ _ _)
  apply Total.statement (.skip_seq _ _ _ _ _)
  apply Total.statement (.return_start _ _ _ _ _)
  apply (hreturn.total function _).bind
  rintro state rfl
  apply Total.value (.return_finish _ _ _ _ _ _ _ _ rfl hfree)
  exact .done ⟨final, by rw [Cont.callCont_eq hcont]; rfl, hmemory⟩

end Quadrature.CSource.Cosine
