import Quadrature.CSource.Semantics.CallMemory

/-!
# Freeing fresh local blocks

`free_fresh_locals` releases a list of distinct freeable local ranges in
environment order. Every free succeeds, and memory allocated before the
enclosing call is preserved (`CallMemory`).
-/

namespace Quadrature.CSource.C

open CC

/-- Freeing a range in a block allocated during the call preserves `CallMemory`. -/
theorem CallMemory.free_fresh {initial middle : Mem} (h : CallMemory initial middle)
    (block : Block) (lo hi : Z) (hfresh : initial.nextblock.toNat ≤ block.toNat) :
    CallMemory initial (Mem.uncheckedFree middle block lo hi) := by
  refine ⟨h.nextblock, ?_, ?_⟩
  · intro chunk readBlock offset hb
    have hne : readBlock ≠ block := by
      intro heq
      subst readBlock
      exact (Nat.not_lt_of_ge hfresh) hb
    exact (Mem.load_free_other middle block lo hi chunk readBlock hne offset).trans
      (h.loads chunk readBlock offset hb)
  · intro readBlock offset kind permission hb
    have hne : readBlock ≠ block := by
      intro heq
      subst readBlock
      exact (Nat.not_lt_of_ge hfresh) hb
    exact (Mem.perm_free_other middle block lo hi readBlock hne offset kind permission).trans
      (h.permissions readBlock offset kind permission hb)

/-- Given `CallMemory initial memory` and a list of distinct, freeable ranges in blocks allocated
since `initial`, `Mem.freeList` succeeds on all of them and the result satisfies
`CallMemory initial`. -/
theorem free_fresh_locals (initial memory : Mem) (blocks : List (Block × Z × Z))
    (hmem : CallMemory initial memory)
    (hdistinct : (blocks.map Prod.fst).Nodup)
    (hfresh : ∀ entry ∈ blocks, initial.nextblock.toNat ≤ entry.1.toNat)
    (hfreeable : ∀ entry ∈ blocks,
      Mem.rangePerm memory entry.1 entry.2.1 entry.2.2 .Cur .Freeable = true) :
    ∃ final, Mem.freeList memory blocks = some final ∧ CallMemory initial final := by
  induction blocks generalizing memory with
  | nil => exact ⟨memory, rfl, hmem⟩
  | cons entry entries ih =>
    rcases entry with ⟨block, lo, hi⟩
    simp only [List.map_cons, List.nodup_cons] at hdistinct
    have hfree := hfreeable (block, lo, hi) (by simp)
    have hnext := hmem.free_fresh block lo hi (hfresh (block, lo, hi) (by simp))
    have hrest : ∀ entry ∈ entries,
        Mem.rangePerm (Mem.uncheckedFree memory block lo hi)
          entry.1 entry.2.1 entry.2.2 .Cur .Freeable = true := by
      intro entry he
      have hne : entry.1 ≠ block := by
        intro heq
        apply hdistinct.1
        exact List.mem_map.mpr ⟨entry, he, heq⟩
      apply Mem.rangePerm_intro
      intro offset hlo hhi
      rw [Mem.perm_free_other _ _ _ _ _ hne]
      exact Mem.rangePerm_perm memory entry.1 entry.2.1 entry.2.2 .Cur .Freeable
        (hfreeable entry (by simp [he])) offset hlo hhi
    obtain ⟨final, hfinish, hfinal⟩ := ih _ hnext hdistinct.2
      (fun entry he => hfresh entry (by simp [he])) hrest
    refine ⟨final, ?_, hfinal⟩
    rw [Mem.freeList, Mem.free_isSome hfree]
    exact hfinish

end Quadrature.CSource.C
