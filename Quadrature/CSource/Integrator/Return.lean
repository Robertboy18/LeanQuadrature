import Quadrature.CSource.Integrator.Entry
import Quadrature.CSource.Semantics.LocalFree

/-!
# Returning from the original C integrator

The loop preserves permissions on the four local blocks, so they stay freeable
(`IntegratorStorage.after_loop`). Its two updated blocks are fresh relative to
the caller, so the whole body satisfies `CallMemory` from the caller's memory
(`integrator_body_memory`), and all four local ranges can then be freed
(`integrator_free_locals`).
-/

namespace Quadrature.CSource.C

open CC

/-- The blocks to free at integrator return, in the order `blocksOfEnv` enumerates the frame's
environment: `f` (8 bytes), `n` (4), `i` (4), `s` (8). -/
theorem integrator_blocks (composites : CompositeEnv) (frame : IntegratorFrame) :
    blocksOfEnv composites frame.locals =
      [(frame.callback, 0, 8), (frame.count, 0, 4),
        (frame.index, 0, 4), (frame.accumulator, 0, 8)] := by
  rfl

private theorem freeable_after_loop {frame : IntegratorFrame} {initial final : Mem}
    (hloop : LoopMemory frame initial final) (block : Block) (lo hi : Z)
    (h : Mem.rangePerm initial block lo hi .Cur .Freeable = true) :
    Mem.rangePerm final block lo hi .Cur .Freeable = true := by
  apply Mem.rangePerm_intro
  intro offset hlo hhi
  have hp := Mem.rangePerm_perm initial block lo hi .Cur .Freeable h offset hlo hhi
  rw [hloop.permissions _ _ _ _ (Mem.perm_valid_block initial block offset .Cur .Freeable hp)]
  exact hp

/-- `LoopMemory` preserves the freeability of the four local ranges. -/
theorem IntegratorStorage.after_loop {frame : IntegratorFrame} {initial final : Mem}
    (storage : IntegratorStorage frame initial) (hloop : LoopMemory frame initial final) :
    IntegratorStorage frame final :=
  ⟨freeable_after_loop hloop _ _ _ storage.callback,
    freeable_after_loop hloop _ _ _ storage.count,
    freeable_after_loop hloop _ _ _ storage.index,
    freeable_after_loop hloop _ _ _ storage.accumulator⟩

private theorem old_block_ne_locals (initial : Mem) (block : Block)
    (hb : block < initial.nextblock) :
    block ≠ (integratorFrame initial).index ∧
      block ≠ (integratorFrame initial).accumulator := by
  constructor <;> intro heq
  all_goals
    have hh := congrArg Positive.toNat heq
    simp only [integratorFrame, Positive.toNat_succ] at hh
    simp only [Positive.lt_iff] at hb
    omega

/-- Tables allocated before the call are separate from the frame allocated by the call. -/
theorem integrator_table_separation (initial : Mem) (nodes weights : Block)
    (hnodes : nodes < initial.nextblock) (hweights : weights < initial.nextblock) :
    TableSeparation (integratorFrame initial) nodes weights :=
  ⟨(old_block_ne_locals initial nodes hnodes).1,
    (old_block_ne_locals initial nodes hnodes).2,
    (old_block_ne_locals initial weights hweights).1,
    (old_block_ne_locals initial weights hweights).2⟩

/-- Entry satisfying `CallMemory` followed by a body satisfying `LoopMemory` for the frame
allocated by that entry satisfies `CallMemory` from the caller's memory, since the two updated
blocks are fresh. -/
theorem integrator_body_memory {initial entered final : Mem}
    (hentry : CallMemory initial entered)
    (hbody : LoopMemory (integratorFrame initial) entered final) :
    CallMemory initial final := by
  refine ⟨hentry.nextblock.trans hbody.nextblock, ?_, ?_⟩
  · intro chunk block offset hb
    have hne := old_block_ne_locals initial block hb
    exact (hbody.loads chunk block offset (Nat.lt_of_lt_of_le hb hentry.nextblock)
      hne.1 hne.2).trans (hentry.loads chunk block offset hb)
  · intro block offset kind permission hb
    exact (hbody.permissions block offset kind permission
      (Nat.lt_of_lt_of_le hb hentry.nextblock)).trans
      (hentry.permissions block offset kind permission hb)

/-- Given `IntegratorStorage` and `CallMemory` from the caller's memory, freeing the frame's four
ranges succeeds and the result still satisfies `CallMemory`. -/
theorem integrator_free_locals (composites : CompositeEnv) (initial memory : Mem)
    (storage : IntegratorStorage (integratorFrame initial) memory)
    (hmem : CallMemory initial memory) :
    ∃ final,
      Mem.freeList memory (blocksOfEnv composites (integratorFrame initial).locals) =
        some final ∧ CallMemory initial final := by
  apply free_fresh_locals initial memory _ hmem
  · rw [integrator_blocks]
    exact (integratorFrame initial).distinct
  · rw [integrator_blocks]
    intro entry he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    all_goals simp only [integratorFrame, Positive.toNat_succ]; omega
  · rw [integrator_blocks]
    intro entry he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact storage.callback
    · exact storage.count
    · exact storage.index
    · exact storage.accumulator

end Quadrature.CSource.C
