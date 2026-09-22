import Quadrature.CSource.Integrator.Body

/-!
# Entering the original C integrator

`integrator_entry` allocates the four variables `f`, `n`, `i`, `s` in
declaration order and stores the pointer and integer arguments into the two
parameter blocks. The two locals stay uninitialized until the body assigns
them. All four allocated ranges are freeable (`IntegratorStorage`), the body
entry conditions `IntegratorParameters` hold, and the caller's memory is
preserved (`CallMemory`).
-/

namespace Quadrature.CSource.C

open CC Binary64.ClightSource

/-- The frame allocated from `memory`: `f`, `n`, `i` and `s` in the four consecutive blocks from
`memory.nextblock`. -/
def integratorFrame (memory : Mem) : IntegratorFrame where
  callback := memory.nextblock
  count := memory.nextblock.succ
  index := memory.nextblock.succ.succ
  accumulator := memory.nextblock.succ.succ.succ
  distinct := by
    have hne (i j : Block) (hij : i.toNat ≠ j.toNat) : i ≠ j :=
      fun h => hij (congrArg Positive.toNat h)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
      List.nodup_nil, not_false_eq_true, and_true]
    repeat' constructor
    all_goals apply hne; simp only [Positive.toNat_succ]; omega

/-- The memory after allocating the four blocks of 8, 4, 4 and 8 bytes from `memory`. -/
def integratorAllocatedMemory (memory : Mem) : Mem :=
  (Mem.alloc (Mem.alloc (Mem.alloc (Mem.alloc memory 0 8).1 0 4).1 0 4).1 0 8).1

/-- `IntegratorStorage frame memory`: all four local ranges of the frame, including the two
parameter blocks, are freeable in `memory`. -/
structure IntegratorStorage (frame : IntegratorFrame) (memory : Mem) : Prop where
  callback : Mem.rangePerm memory frame.callback 0 8 .Cur .Freeable = true
  count : Mem.rangePerm memory frame.count 0 4 .Cur .Freeable = true
  index : Mem.rangePerm memory frame.index 0 4 .Cur .Freeable = true
  accumulator : Mem.rangePerm memory frame.accumulator 0 8 .Cur .Freeable = true

/-- A store does not change freeability. -/
theorem IntegratorStorage.after_store {frame : IntegratorFrame} {initial final : Mem}
    (storage : IntegratorStorage frame initial) {chunk : Chunk} {block : Block}
    {offset : Z} {value : Val}
    (hstore : Mem.store chunk initial block offset value = some final) :
    IntegratorStorage frame final := by
  constructor <;> rw [Mem.rangePerm_store_eq hstore]
  · exact storage.callback
  · exact storage.count
  · exact storage.index
  · exact storage.accumulator

private theorem allocated_range (memory final : Mem) (size : Z)
    (h : CallMemory (Mem.alloc memory 0 size).1 final) :
    Mem.rangePerm final memory.nextblock 0 size .Cur .Freeable = true := by
  apply Mem.rangePerm_intro
  intro offset hlo hhi
  rw [h.permissions _ _ _ _ (by
    simp only [Mem.alloc_nextblock, Positive.lt_iff, Positive.toNat_succ]
    omega)]
  exact Mem.perm_alloc_same memory 0 size offset .Cur hlo hhi

/-- Allocating the integrator's parameters and locals from `memory` yields
`(integratorFrame memory).locals` and `integratorAllocatedMemory memory`. -/
theorem integrator_allocation (ge : ExpressionEnv) (memory : Mem) :
    AllocVariables ge emptyEnv memory (Typed.integrate.fn_params ++ Typed.integrate.fn_vars)
      (integratorFrame memory).locals (integratorAllocatedMemory memory) := by
  apply CC.AllocVariables.cons _ _ _ _ _ _ _ _ _ rfl
  apply CC.AllocVariables.cons _ _ _ _ _ _ _ _ _ rfl
  apply CC.AllocVariables.cons _ _ _ _ _ _ _ _ _ rfl
  apply CC.AllocVariables.cons _ _ _ _ _ _ _ _ _ rfl
  exact CC.AllocVariables.nil _ _

/-- All four freshly allocated ranges are freeable. -/
theorem integrator_allocated_storage (memory : Mem) :
    IntegratorStorage (integratorFrame memory) (integratorAllocatedMemory memory) := by
  let first := (Mem.alloc memory 0 8).1
  let second := (Mem.alloc first 0 4).1
  let third := (Mem.alloc second 0 4).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact allocated_range memory _ 8
      ((CallMemory.alloc first 0 4).trans
        ((CallMemory.alloc second 0 4).trans (CallMemory.alloc third 0 8)))
  · exact allocated_range first _ 4
      ((CallMemory.alloc second 0 4).trans (CallMemory.alloc third 0 8))
  · exact allocated_range second _ 4 (CallMemory.alloc third 0 8)
  · exact allocated_range third _ 8 (.refl _)

/-- The four allocations satisfy `CallMemory`. -/
theorem integrator_allocation_memory (memory : Mem) :
    CallMemory memory (integratorAllocatedMemory memory) :=
  (CallMemory.alloc memory 0 8).trans
    ((CallMemory.alloc _ 0 4).trans
      ((CallMemory.alloc _ 0 4).trans (CallMemory.alloc _ 0 8)))

private theorem writable_of_freeable (memory : Mem) (block : Block) (chunk : Chunk)
    (h : Mem.rangePerm memory block 0 (sizeChunk chunk) .Cur .Freeable = true) :
    Mem.validAccess memory chunk block 0 .Writable = true := by
  have hw := Mem.rangePerm_implies h
    (show permOrder .Freeable .Writable = true from rfl)
  simpa [Mem.validAccess] using hw

/-- For any memory, callback block and count `n`, some `entered` memory gives the `FunctionEntry`
of `Typed.integrate`, together with `IntegratorParameters`, `IntegratorStorage` and
`CallMemory`. The stores succeed because allocation supplies writable storage. -/
theorem integrator_entry (ge : ExpressionEnv) (memory : Mem) (callback : Block) (n : Nat) :
    ∃ entered,
      FunctionEntry ge Typed.integrate
        [.Vptr callback Integers.Ptrofs.zero, .Vint (Integers.Int.repr n)]
        memory (integratorFrame memory).locals entered ∧
      IntegratorParameters (integratorFrame memory) entered
        (.Vptr callback Integers.Ptrofs.zero) n ∧
      IntegratorStorage (integratorFrame memory) entered ∧
      CallMemory memory entered := by
  let frame := integratorFrame memory
  let allocated := integratorAllocatedMemory memory
  have storage := integrator_allocated_storage memory
  have hf : Mem.validAccess allocated Mptr frame.callback 0 .Writable = true :=
    writable_of_freeable allocated frame.callback Mptr storage.callback
  obtain ⟨bound, hsf⟩ : ∃ bound, Mem.store Mptr allocated frame.callback 0
      (.Vptr callback Integers.Ptrofs.zero) = some bound := by
    simp only [Mem.store, hf, ite_true]
    exact ⟨_, rfl⟩
  have boundStorage := storage.after_store hsf
  have hn : Mem.validAccess bound .Mint32 frame.count 0 .Writable = true :=
    writable_of_freeable bound frame.count .Mint32 boundStorage.count
  obtain ⟨entered, hsn⟩ : ∃ entered,
      Mem.store .Mint32 bound frame.count 0 (.Vint (Integers.Int.repr n)) =
        some entered := by
    simp only [Mem.store, hn, ite_true]
    exact ⟨_, rfl⟩
  have enteredStorage := boundStorage.after_store hsn
  refine ⟨entered, ?_, ?_, enteredStorage, ?_⟩
  · refine ⟨?_, allocated, integrator_allocation ge memory, ?_⟩
    · change [_f, _n, _i, _s].Nodup
      decide +kernel
    · apply BindParameters.cons _ _ _ _ _ _ _ _ _ _ rfl
        (AssignLoc.value _ Mptr _ rfl rfl hsf)
      exact BindParameters.cons _ _ _ _ _ _ _ _ _ _ rfl
        (AssignLoc.value _ .Mint32 _ rfl rfl hsn) (.nil _)
  · refine ⟨?_, Mem.load_store_same hsn,
      writable_of_freeable entered frame.index .Mint32 enteredStorage.index,
      writable_of_freeable entered frame.accumulator .Mfloat64 enteredStorage.accumulator⟩
    have hne : frame.callback ≠ frame.count := by
      intro heq
      have hh := congrArg Positive.toNat heq
      simp only [frame, integratorFrame, Positive.toNat_succ] at hh
      omega
    rw [Mem.load_store_other hsn Mptr frame.callback 0 (Or.inl hne)]
    exact Mem.load_store_same hsf
  · apply ((integrator_allocation_memory memory).store_fresh hsf (Nat.le_refl _)).store_fresh
      hsn
    simp only [frame, integratorFrame, Positive.toNat_succ]
    omega

end Quadrature.CSource.C
