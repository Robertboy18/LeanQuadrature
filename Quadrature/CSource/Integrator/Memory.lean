import Quadrature.CSource.Integrator.State

/-!
# Memory outside the two updated integrator locals

The loop writes only the index and accumulator blocks. `LoopMemory` records
that every load from any other previously allocated block and every permission
on previously allocated blocks are unchanged. The relation composes across
local stores and nested calls, and it carries `TableCells` along the loop.
-/

namespace Quadrature.CSource.C

open CC

/-- `LoopMemory frame initial final`: `nextblock` did not decrease, every load from a block
allocated before `initial` other than the index and accumulator blocks is unchanged, and every
permission on blocks allocated before `initial` is unchanged. -/
structure LoopMemory (frame : IntegratorFrame) (initial final : Mem) : Prop where
  nextblock : initial.nextblock.toNat ≤ final.nextblock.toNat
  loads : ∀ chunk block offset, block < initial.nextblock →
    block ≠ frame.index → block ≠ frame.accumulator →
    Mem.load chunk final block offset = Mem.load chunk initial block offset
  permissions : ∀ block offset kind permission, block < initial.nextblock →
    Mem.perm final block offset kind permission = Mem.perm initial block offset kind permission

/-- `LoopMemory` is reflexive. -/
theorem LoopMemory.refl (frame : IntegratorFrame) (memory : Mem) :
    LoopMemory frame memory memory :=
  ⟨Nat.le_refl _, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

/-- A nested call satisfying `CallMemory` satisfies `LoopMemory`. -/
theorem LoopMemory.of_call {initial final : Mem} (frame : IntegratorFrame)
    (h : CallMemory initial final) : LoopMemory frame initial final :=
  ⟨h.nextblock, fun chunk block offset hb _ _ => h.loads chunk block offset hb,
    h.permissions⟩

/-- `LoopMemory` is transitive. -/
theorem LoopMemory.trans {frame : IntegratorFrame} {initial middle final : Mem}
    (first : LoopMemory frame initial middle) (second : LoopMemory frame middle final) :
    LoopMemory frame initial final := by
  refine ⟨first.nextblock.trans second.nextblock, ?_, ?_⟩
  · intro chunk block offset hb hi hs
    exact (second.loads chunk block offset
      (Nat.lt_of_lt_of_le hb first.nextblock) hi hs).trans
      (first.loads chunk block offset hb hi hs)
  · intro block offset kind permission hb
    exact (second.permissions block offset kind permission
      (Nat.lt_of_lt_of_le hb first.nextblock)).trans
      (first.permissions block offset kind permission hb)

/-- A store into the index block or the accumulator block satisfies `LoopMemory`. -/
theorem LoopMemory.of_store {frame : IntegratorFrame} {initial final : Mem}
    {chunk : Chunk} {block : Block} {offset : Z} {value : Val}
    (hstore : Mem.store chunk initial block offset value = some final)
    (hblock : block = frame.index ∨ block = frame.accumulator) :
    LoopMemory frame initial final := by
  refine ⟨?_, ?_, fun b position kind permission _ =>
    Mem.perm_store hstore b position kind permission⟩
  · rw [Mem.store_nextblock hstore]
  · intro readChunk readBlock readOffset _ hi hs
    apply Mem.load_store_other hstore
    left
    rcases hblock with rfl | rfl
    · exact hi
    · exact hs

/-- A load from a block other than the two updated locals survives the loop with its value. -/
theorem LoopMemory.load {frame : IntegratorFrame} {initial final : Mem}
    (h : LoopMemory frame initial final) {chunk : Chunk} {block : Block}
    {offset : Z} {value : Val}
    (hload : Mem.load chunk initial block offset = some value)
    (hi : block ≠ frame.index) (hs : block ≠ frame.accumulator) :
    Mem.load chunk final block offset = some value := by
  rw [h.loads chunk block offset (block_valid_of_load hload) hi hs]
  exact hload

/-- `TableSeparation frame nodes weights`: neither table block is the index or accumulator block.
Established in `IntegratorReturn` from the tables being older than the call. -/
structure TableSeparation (frame : IntegratorFrame) (nodes weights : Block) : Prop where
  nodes_index : nodes ≠ frame.index
  nodes_accumulator : nodes ≠ frame.accumulator
  weights_index : weights ≠ frame.index
  weights_accumulator : weights ≠ frame.accumulator

/-- A call that preserves existing memory preserves every initialized quadrature table cell. -/
theorem CallMemory.table_cells {initial final : Mem} {nodes weights : Block}
    {n i : Nat} {terms : List (Floats.Float × Floats.Float)} (h : CallMemory initial final)
    (cells : Binary64.Clight.TableCells initial nodes weights n i terms) :
    Binary64.Clight.TableCells final nodes weights n i terms := by
  induction terms generalizing i with
  | nil => trivial
  | cons term terms ih =>
      exact ⟨h.load cells.1, h.load cells.2.1, ih cells.2.2⟩

/-- Under `TableSeparation`, `TableCells` survive the loop. -/
theorem LoopMemory.table_cells {frame : IntegratorFrame} {initial final : Mem}
    {nodes weights : Block} {n i : Nat} {terms : List (Floats.Float × Floats.Float)}
    (h : LoopMemory frame initial final) (separate : TableSeparation frame nodes weights)
    (cells : Binary64.Clight.TableCells initial nodes weights n i terms) :
    Binary64.Clight.TableCells final nodes weights n i terms := by
  induction terms generalizing i with
  | nil => trivial
  | cons term terms ih =>
    exact ⟨h.load cells.1 separate.weights_index separate.weights_accumulator,
      h.load cells.2.1 separate.nodes_index separate.nodes_accumulator, ih cells.2.2⟩

end Quadrature.CSource.C
