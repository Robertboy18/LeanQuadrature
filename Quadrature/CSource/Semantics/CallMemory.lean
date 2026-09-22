import Quadrature.CSource.Accessors.Calls

/-!
# Memory preserved by nested C calls

The integrator keeps its locals in memory while evaluating nested accessor and
callback calls. Load preservation alone is not enough: the accumulator and
index must stay writable afterwards. `CallMemory initial final` therefore
records loads and permissions on every block allocated before the call,
together with a monotone allocation counter (vocabulary: see
`Quadrature.CSource.Semantics.Strategy`). `accessor_call_memory` proves the relation for
a full accessor call from its allocation, stores and frees, with no
memory-preservation assumption on the accessors.
-/

namespace Quadrature.CSource.C

open CC

/-- `CallMemory initial final`: `nextblock` did not decrease, and every load and every permission
on a block allocated before the call (`block < initial.nextblock`) is the same in `final` as in
`initial`. Fresh blocks may be allocated and changed freely. -/
structure CallMemory (initial final : Mem) : Prop where
  nextblock : initial.nextblock.toNat ≤ final.nextblock.toNat
  loads : ∀ chunk block offset, block < initial.nextblock →
    Mem.load chunk final block offset = Mem.load chunk initial block offset
  permissions : ∀ block offset kind permission, block < initial.nextblock →
    Mem.perm final block offset kind permission = Mem.perm initial block offset kind permission

/-- `CallMemory` is reflexive. -/
theorem CallMemory.refl (memory : Mem) : CallMemory memory memory :=
  ⟨Nat.le_refl _, fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

/-- `CallMemory` is transitive: a block old for the first call is old for the second. -/
theorem CallMemory.trans {initial middle final : Mem}
    (first : CallMemory initial middle) (second : CallMemory middle final) :
    CallMemory initial final := by
  refine ⟨first.nextblock.trans second.nextblock, ?_, ?_⟩
  · intro chunk block offset hb
    exact (second.loads chunk block offset (Nat.lt_of_lt_of_le hb first.nextblock)).trans
      (first.loads chunk block offset hb)
  · intro block offset kind permission hb
    exact (second.permissions block offset kind permission
      (Nat.lt_of_lt_of_le hb first.nextblock)).trans
      (first.permissions block offset kind permission hb)

/-- A load that succeeds before the call succeeds with the same value after it. -/
theorem CallMemory.load {initial final : Mem} (h : CallMemory initial final)
    {chunk : Chunk} {block : Block} {offset : Z} {value : Val}
    (hload : Mem.load chunk initial block offset = some value) :
    Mem.load chunk final block offset = some value := by
  rw [h.loads chunk block offset (block_valid_of_load hload)]
  exact hload

/-- Access validity on a block older than the call is unchanged by it. -/
theorem CallMemory.valid_access {initial final : Mem} (h : CallMemory initial final)
    (chunk : Chunk) (block : Block) (offset : Z) (permission : Permission)
    (hb : block < initial.nextblock) :
    Mem.validAccess final chunk block offset permission =
      Mem.validAccess initial chunk block offset permission :=
  Mem.validAccess_congr (fun position => h.permissions block position .Cur permission hb)

/-- Allocating one fresh block satisfies `CallMemory`. -/
theorem CallMemory.alloc (memory : Mem) (lo hi : Z) :
    CallMemory memory (Mem.alloc memory lo hi).1 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Mem.alloc_nextblock, Positive.toNat_succ]
    omega
  · intro chunk block offset hb
    exact Mem.load_alloc_other memory lo hi chunk block
      (fun heq => by subst block; exact Nat.lt_irrefl _ hb) offset
  · intro block offset kind permission hb
    exact Mem.perm_alloc_other memory lo hi block
      (fun heq => by subst block; exact Nat.lt_irrefl _ hb) offset kind permission

/-- A store into a block allocated during the call (`initial.nextblock ≤ block`) preserves
`CallMemory`. -/
theorem CallMemory.store_fresh {initial middle final : Mem}
    (h : CallMemory initial middle) {chunk : Chunk} {block : Block} {offset : Z} {value : Val}
    (hstore : Mem.store chunk middle block offset value = some final)
    (hfresh : initial.nextblock.toNat ≤ block.toNat) : CallMemory initial final := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Mem.store_nextblock hstore]
    exact h.nextblock
  · intro readChunk readBlock readOffset hb
    have hne : readBlock ≠ block := by
      intro heq
      subst readBlock
      exact (Nat.not_lt_of_ge hfresh) hb
    exact (Mem.load_store_other hstore readChunk readBlock readOffset (Or.inl hne)).trans
      (h.loads readChunk readBlock readOffset hb)
  · intro readBlock readOffset kind permission hb
    exact (Mem.perm_store hstore readBlock readOffset kind permission).trans
      (h.permissions readBlock readOffset kind permission hb)

/-- After an accessor returns, permissions on blocks older than the call are unchanged. -/
theorem AccessorInitialization.returned_permissions {ge : ExpressionEnv}
    {initial entered : Mem} {n i : Nat}
    (h : AccessorInitialization ge initial n i entered)
    (block : Block) (offset : Z) (kind : PermKind) (permission : Permission)
    (hb : block < initial.nextblock) :
    Mem.perm (accessorReturnedMemory initial entered) block offset kind permission =
      Mem.perm initial block offset kind permission := by
  have hi : block ≠ initial.nextblock := by
    intro heq
    subst block
    exact Nat.lt_irrefl _ hb
  have hn : block ≠ initial.nextblock.succ := by
    intro heq
    have hh := congrArg Positive.toNat heq
    simp only [Positive.toNat_succ] at hh
    simp only [Positive.lt_iff] at hb
    omega
  rw [accessorReturnedMemory, Mem.perm_free_other _ _ _ _ _ hi,
    Mem.perm_free_other _ _ _ _ _ hn, h.perm]
  exact (Mem.perm_alloc_other (Mem.alloc initial 0 4).1 0 4 block hn
    offset kind permission).trans
    (Mem.perm_alloc_other initial 0 4 block hi offset kind permission)

/-- A full accessor call (allocate, bind, free) satisfies `CallMemory`. -/
theorem AccessorInitialization.call_memory {ge : ExpressionEnv}
    {initial entered : Mem} {n i : Nat}
    (h : AccessorInitialization ge initial n i entered) :
    CallMemory initial (accessorReturnedMemory initial entered) := by
  refine ⟨?_, h.returned_loads, h.returned_permissions⟩
  rw [h.returned_nextblock, Positive.toNat_succ, Positive.toNat_succ]
  omega

variable [ExternalCalls]

/-- Assume `table` resolves to `tableBlock` and memory holds `value` at `8 * tableOffset n i`
there, with `n, i ≤ 10`. Then calling `Typed.accessor table` with `i` and `n` returns
`Vfloat value` silently in a memory satisfying `CallMemory` and `AccessorExit`. -/
theorem accessor_call_memory (ge : GlobalEnv) (memory : Mem) (table : Ident) (tableBlock : Block)
    (n i : Nat) (value : Floats.Float) (hn : n ≤ 10) (hi : i ≤ 10)
    (hnamei : table ≠ Binary64.ClightSource._i)
    (hnamen : table ≠ Binary64.ClightSource._npts)
    (hsym : Genv.findSymbol ge.globals table = some tableBlock)
    (hload : Mem.load .Mfloat64 memory tableBlock
      (8 * Binary64.Clight.tableOffset n i : Nat) = some (.Vfloat value)) :
    ∃ final,
      EvalFuncall ge memory (.Internal (Typed.accessor table))
        [.Vint (Integers.Int.repr i), .Vint (Integers.Int.repr n)]
        E0 final (.Vfloat value) ∧
      CallMemory memory final ∧ AccessorExit memory final := by
  obtain ⟨entered, hentry⟩ := accessor_initialization_exists ge.expressionEnv memory n i
  refine ⟨accessorReturnedMemory memory entered, ?_, hentry.call_memory, hentry.exit_state⟩
  apply hentry.eval_funcall
  exact accessor_read_in_c_environment ge entered memory.nextblock.succ memory.nextblock
    tableBlock table n i value hn hi hnamei hnamen hsym hentry.count_load hentry.index_load
    (hentry.preserve_load hload)

end Quadrature.CSource.C
