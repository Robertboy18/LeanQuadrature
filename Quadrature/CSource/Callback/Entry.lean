import Quadrature.CSource.Integrator.Calls
import Quadrature.CSource.Semantics.LocalFree

/-!
# Entry and exit storage for the original callback

The callback's single `double` parameter `x` occupies a fresh eight-byte block.
`testfun_entry` shows allocation supplies its write permission and the
argument store establishes the load the body uses. `testfun_free` shows a
nested call satisfying `CallMemory` leaves the block freeable.
-/

namespace Quadrature.CSource.C

open CC Binary64.ClightSource

/-- The environment of the callback: its one parameter `x` in `block`, no other locals. -/
def testfunLocals (block : Block) : Env :=
  emptyEnv.set _x (block, tdouble)

/-- The single eight-byte range to free at callback return. -/
theorem testfun_blocks (ce : CompositeEnv) (block : Block) :
    blocksOfEnv ce (testfunLocals block) = [(block, 0, 8)] := rfl

/-- For any memory and argument `x`, some `entered` memory gives the `FunctionEntry` of
`Typed.testfun`, with `x` loaded from the fresh block, that block freeable, and `CallMemory`. -/
theorem testfun_entry (ge : ExpressionEnv) (memory : Mem) (x : Floats.Float) :
    ∃ entered,
      FunctionEntry ge Typed.testfun [.Vfloat x]
        memory (testfunLocals memory.nextblock) entered ∧
      Mem.load .Mfloat64 entered memory.nextblock 0 = some (.Vfloat x) ∧
      Mem.rangePerm entered memory.nextblock 0 8 .Cur .Freeable = true ∧
      CallMemory memory entered := by
  let allocated := (Mem.alloc memory 0 8).1
  have hfree : Mem.rangePerm allocated memory.nextblock 0 8 .Cur .Freeable = true :=
    Mem.rangePerm_intro allocated memory.nextblock 0 8 .Cur .Freeable
      (fun ofs hlo hhi => Mem.perm_alloc_same memory 0 8 ofs .Cur hlo hhi)
  have hwrite : Mem.validAccess allocated .Mfloat64 memory.nextblock 0 .Writable = true := by
    have hw := Mem.rangePerm_implies hfree
      (show permOrder .Freeable .Writable = true from rfl)
    simpa [Mem.validAccess, sizeChunk, alignChunk] using hw
  obtain ⟨entered, hstore⟩ : ∃ entered,
      Mem.store .Mfloat64 allocated memory.nextblock 0 (.Vfloat x) = some entered := by
    simp only [Mem.store, hwrite, ite_true]
    exact ⟨_, rfl⟩
  refine ⟨entered, ?_, Mem.load_store_same hstore, ?_,
    (CallMemory.alloc memory 0 8).store_fresh hstore (Nat.le_refl _)⟩
  · refine ⟨by simp [Typed.testfun], allocated, ?_, ?_⟩
    · exact CC.AllocVariables.cons _ _ _ _ _ _ _ _ _ rfl (.nil _ _)
    · exact BindParameters.cons _ _ _ _ _ _ _ _ _ _ rfl
        (AssignLoc.value _ .Mfloat64 _ rfl rfl hstore) (.nil _)
  · rw [Mem.rangePerm_store_eq hstore]
    exact hfree

/-- After a body satisfying `CallMemory` from the entered memory, freeing the parameter block
succeeds and the result satisfies `CallMemory` from the caller's memory. -/
theorem testfun_free (ce : CompositeEnv) (initial entered afterBody : Mem)
    (x : Floats.Float)
    (hload : Mem.load .Mfloat64 entered initial.nextblock 0 = some (.Vfloat x))
    (hfree : Mem.rangePerm entered initial.nextblock 0 8 .Cur .Freeable = true)
    (hentry : CallMemory initial entered) (hbody : CallMemory entered afterBody) :
    ∃ final,
      Mem.freeList afterBody (blocksOfEnv ce (testfunLocals initial.nextblock)) =
        some final ∧ CallMemory initial final := by
  rw [testfun_blocks]
  apply free_fresh_locals initial afterBody [(initial.nextblock, 0, 8)]
    (hentry.trans hbody) (by simp)
  · intro entry he
    simp only [List.mem_singleton] at he
    subst entry
    exact Nat.le_refl _
  · intro entry he
    simp only [List.mem_singleton] at he
    subst entry
    apply Mem.rangePerm_intro
    intro offset hlo hhi
    rw [hbody.permissions _ _ _ _ (block_valid_of_load hload)]
    exact Mem.rangePerm_perm entered initial.nextblock 0 8 .Cur .Freeable
      hfree offset hlo hhi

end Quadrature.CSource.C
