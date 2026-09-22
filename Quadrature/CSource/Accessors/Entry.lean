import CCLib.MemoryLemmas
import Quadrature.CSource.Frontend.TypedFunctions
import Quadrature.CSource.Semantics.Entry

/-!
# Initializing the original accessor parameters

Both accessors declare `i` before `npts`. Entry allocates two four-byte blocks
in that order and stores the arguments into them.
`accessor_initialization_exists` shows the stores succeed in arbitrary entry
memory and establish the two integer loads used by
`Quadrature.CSource.Accessors.TableExpressions`, while every load from a previously
allocated block is preserved. The final theorems combine source-text
elaboration, entry and return-expression evaluation. The return statement and
the exit are executed in `Quadrature.CSource.Accessors.Return`.
-/

namespace Quadrature.CSource.C

open CC Binary64.ClightSource

/-- The memory after the two four-byte allocations of an accessor call from `memory`, in
parameter order: `i`, then `npts`. -/
def accessorAllocatedMemory (memory : Mem) : Mem :=
  (Mem.alloc (Mem.alloc memory 0 4).1 0 4).1

/-- The accessor environment after allocating from `memory`: `i` in `memory.nextblock` and `npts`
in the following block. -/
def accessorEntryLocals (memory : Mem) : Env :=
  accessorLocals memory.nextblock.succ memory.nextblock

/-- Allocating the accessor's two parameters from `memory` yields `accessorEntryLocals memory`
and `accessorAllocatedMemory memory`. -/
theorem accessor_allocation (ge : ExpressionEnv) (memory : Mem) :
    AllocVariables ge emptyEnv memory [(_i, tint), (_npts, tint)]
      (accessorEntryLocals memory) (accessorAllocatedMemory memory) := by
  apply CC.AllocVariables.cons _ _ _ _ _ _ _ _ _ rfl
  apply CC.AllocVariables.cons _ _ _ _ _ _ _ _ _ rfl
  exact CC.AllocVariables.nil _ _

private theorem block_ne_succ (block : Block) : block ≠ block.succ := by
  intro h
  have hn := congrArg Positive.toNat h
  simp only [Positive.toNat_succ] at hn
  omega

private theorem fresh_int_access (memory : Mem) :
    Mem.validAccess (Mem.alloc memory 0 4).1 .Mint32 memory.nextblock 0 .Writable =
      true := by
  have hr := Mem.rangePerm_intro (Mem.alloc memory 0 4).1 memory.nextblock
    0 4 .Cur .Freeable (fun ofs hlo hhi =>
      Mem.perm_alloc_same memory 0 4 ofs .Cur hlo hhi)
  have hw := Mem.rangePerm_implies hr (show permOrder .Freeable .Writable = true
    from rfl)
  simpa [Mem.validAccess, sizeChunk, alignChunk] using hw

/-- `AccessorInitialization ge initial n i entered`: from `accessorAllocatedMemory initial`, the
arguments `i` and `n` were bound into their blocks giving `entered`. Both parameter loads hold
in `entered`, loads from blocks older than `initial.nextblock` are unchanged, and exactly two
blocks were allocated. Established by `accessor_initialization_exists`. -/
structure AccessorInitialization (ge : ExpressionEnv) (initial : Mem) (n i : Nat)
    (entered : Mem) : Prop where
  parameters : BindParameters ge (accessorEntryLocals initial)
    (accessorAllocatedMemory initial) [(_i, tint), (_npts, tint)]
    [.Vint (Integers.Int.repr i), .Vint (Integers.Int.repr n)] entered
  index_load : Mem.load .Mint32 entered initial.nextblock 0 =
    some (.Vint (Integers.Int.repr i))
  count_load : Mem.load .Mint32 entered initial.nextblock.succ 0 =
    some (.Vint (Integers.Int.repr n))
  old_loads : ∀ chunk block offset, block < initial.nextblock →
    Mem.load chunk entered block offset = Mem.load chunk initial block offset
  nextblock : entered.nextblock = initial.nextblock.succ.succ

/-- For any memory and arguments `n`, `i`, some `entered` satisfies `AccessorInitialization`:
allocation supplies the writable storage, so both parameter stores succeed. -/
theorem accessor_initialization_exists (ge : ExpressionEnv) (memory : Mem) (n i : Nat) :
    ∃ entered, AccessorInitialization ge memory n i entered := by
  let first := (Mem.alloc memory 0 4).1
  let allocated := accessorAllocatedMemory memory
  have hne : memory.nextblock ≠ first.nextblock := block_ne_succ _
  have hx : Mem.validAccess allocated .Mint32 memory.nextblock 0 .Writable = true := by
    rw [show Mem.validAccess allocated .Mint32 memory.nextblock 0 .Writable =
        Mem.validAccess first .Mint32 memory.nextblock 0 .Writable from
      Mem.validAccess_congr (fun ofs =>
        Mem.perm_alloc_other first 0 4 memory.nextblock hne ofs .Cur .Writable)]
    exact fresh_int_access memory
  obtain ⟨indexed, hsx⟩ : ∃ indexed,
      Mem.store .Mint32 allocated memory.nextblock 0 (.Vint (Integers.Int.repr i)) =
        some indexed := by
    simp only [Mem.store, hx, ite_true]
    exact ⟨_, rfl⟩
  have hn : Mem.validAccess indexed .Mint32 memory.nextblock.succ 0 .Writable = true := by
    rw [Mem.validAccess_store_eq hsx]
    exact fresh_int_access first
  obtain ⟨entered, hsn⟩ : ∃ entered,
      Mem.store .Mint32 indexed memory.nextblock.succ 0 (.Vint (Integers.Int.repr n)) =
        some entered := by
    simp only [Mem.store, hn, ite_true]
    exact ⟨_, rfl⟩
  refine ⟨entered, ?_, ?_, ?_, ?_, ?_⟩
  · apply BindParameters.cons _ _ _ _ _ _ _ _ _ _ (by rfl)
      (AssignLoc.value _ .Mint32 _ rfl rfl hsx)
    exact BindParameters.cons _ _ _ _ _ _ _ _ _ _ (by rfl)
      (AssignLoc.value _ .Mint32 _ rfl rfl hsn) (.nil _)
  · rw [Mem.load_store_other hsn .Mint32 memory.nextblock 0 (Or.inl hne)]
    exact Mem.load_store_same hsx
  · exact Mem.load_store_same hsn
  · intro chunk block offset hb
    have hbi : block ≠ memory.nextblock := by
      intro h
      subst block
      exact (Nat.lt_irrefl _ hb)
    have hbn : block ≠ first.nextblock := by
      intro h
      have hh := congrArg Positive.toNat h
      simp only [first, Mem.alloc_nextblock, Positive.toNat_succ] at hh
      simp only [Positive.lt_iff] at hb
      omega
    rw [Mem.load_store_other hsn chunk block offset (Or.inl hbn),
      Mem.load_store_other hsx chunk block offset (Or.inl hbi)]
    exact (Mem.load_alloc_other first 0 4 chunk block hbn offset).trans
      (Mem.load_alloc_other memory 0 4 chunk block hbi offset)
  · rw [Mem.store_nextblock hsn, Mem.store_nextblock hsx]
    rfl

/-- An `AccessorInitialization` gives the `FunctionEntry` of `Typed.accessor table` with arguments
`i` and `n`, for either table. -/
theorem AccessorInitialization.function_entry {ge : ExpressionEnv} {initial entered : Mem}
    {n i : Nat} (h : AccessorInitialization ge initial n i entered) (table : Ident) :
    FunctionEntry ge (Typed.accessor table)
      [.Vint (Integers.Int.repr i), .Vint (Integers.Int.repr n)]
      initial (accessorEntryLocals initial) entered := by
  refine ⟨?_, accessorAllocatedMemory initial, ?_, h.parameters⟩
  · change [_i, _npts].Nodup
    decide +kernel
  · exact accessor_allocation ge initial

/-- A successful load reads a block below `nextblock`, that is, an allocated block. -/
theorem block_valid_of_load {chunk : Chunk} {memory : Mem} {block : Block}
    {offset : Z} {value : Val} (hload : Mem.load chunk memory block offset = some value) :
    block < memory.nextblock := by
  have ha : Mem.validAccess memory chunk block offset .Readable = true := by
    unfold Mem.load at hload
    split at hload
    · assumption
    · simp at hload
  simp only [Mem.validAccess, Bool.and_eq_true] at ha
  have hp := Mem.rangePerm_perm memory block offset (offset + sizeChunk chunk)
    .Cur .Readable ha.1 offset (by rfl) (by cases chunk <;> simp [sizeChunk])
  exact Mem.perm_valid_block memory block offset .Cur .Readable hp

/-- A load that succeeds before entry succeeds with the same value after entry. -/
theorem AccessorInitialization.preserve_load {ge : ExpressionEnv} {initial entered : Mem}
    {n i : Nat} (h : AccessorInitialization ge initial n i entered)
    {chunk : Chunk} {block : Block} {offset : Z} {value : Val}
    (hload : Mem.load chunk initial block offset = some value) :
    Mem.load chunk entered block offset = some value := by
  rw [h.old_loads chunk block offset (block_valid_of_load hload)]
  exact hload

end Quadrature.CSource.C

namespace Quadrature.CSource.Typed

open CC Binary64.ClightSource

/-- `SourceFunctionEntry source name ge arguments initial locals entered`: the function `name` in
`source` elaborates to some typed function whose `FunctionEntry` with `arguments` from `initial`
gives `locals` and `entered`. The body has not run yet. -/
def SourceFunctionEntry (source : List Char) (name : String) (ge : C.ExpressionEnv)
    (arguments : List Val) (initial : Mem) (locals : Env) (entered : Mem) : Prop :=
  ∃ function, typedSourceFunction source name = some function ∧
    C.FunctionEntry ge function arguments initial locals entered

private theorem accessor_entry_and_return_expression (source : List Char) (name : String)
    (table : Ident) (hfunction : typedSourceFunction source name = some (accessor table))
    (hnamei : table ≠ _i) (hnamen : table ≠ _npts)
    (ge : CGenv) (memory : Mem) (tableBlock : Block) (n i : Nat) (value : Floats.Float)
    (hn : n ≤ 10) (hi : i ≤ 10)
    (hsym : Genv.findSymbol ge.genv_genv table = some tableBlock)
    (hload : Mem.load .Mfloat64 memory tableBlock (8 * Binary64.Clight.tableOffset n i : Nat) =
      some (.Vfloat value)) :
    ∃ entered,
      SourceFunctionEntry source name (.ofClight ge)
        [.Vint (Integers.Int.repr i), .Vint (Integers.Int.repr n)]
        memory (C.accessorEntryLocals memory) entered ∧
      ReturnExpressionEvaluates source name (.ofClight ge)
        (C.accessorEntryLocals memory) entered (.Vfloat value) ∧
      C.AccessorInitialization (.ofClight ge) memory n i entered := by
  obtain ⟨entered, hentry⟩ := C.accessor_initialization_exists (.ofClight ge) memory n i
  refine ⟨entered, ⟨accessor table, hfunction, hentry.function_entry table⟩, ?_, hentry⟩
  refine ⟨C.accessorRead table, ?_, ?_⟩
  · simp [sourceReturnExpression, hfunction, accessor]
  · exact C.table_read_from_memory ge entered memory.nextblock.succ memory.nextblock
      tableBlock table n i value hn hi hnamei hnamen hsym hentry.count_load hentry.index_load
      (hentry.preserve_load hload)

/-- Consider the node accessor of the C text, with `gauss_pts` at `tableBlock` holding `value` at
`8 * tableOffset n i` and `n, i ≤ 10`. Entry from any memory succeeds, the return expression
evaluates to `Vfloat value` in the entered memory, and `AccessorInitialization` holds. -/
theorem gauss_point_entry_and_return_expression (ge : CGenv) (memory : Mem)
    (tableBlock : Block) (n i : Nat) (value : Floats.Float) (hn : n ≤ 10) (hi : i ≤ 10)
    (hsym : Genv.findSymbol ge.genv_genv _gauss_pts = some tableBlock)
    (hload : Mem.load .Mfloat64 memory tableBlock (8 * Binary64.Clight.tableOffset n i : Nat) =
      some (.Vfloat value)) :
    ∃ entered,
      SourceFunctionEntry CSourceData.source "gauss_point" (.ofClight ge)
        [.Vint (Integers.Int.repr i), .Vint (Integers.Int.repr n)]
        memory (C.accessorEntryLocals memory) entered ∧
      ReturnExpressionEvaluates CSourceData.source "gauss_point" (.ofClight ge)
        (C.accessorEntryLocals memory) entered (.Vfloat value) ∧
      C.AccessorInitialization (.ofClight ge) memory n i entered :=
  accessor_entry_and_return_expression CSourceData.source "gauss_point" _gauss_pts
    gauss_point_elaboration (by decide +kernel) (by decide +kernel)
    ge memory tableBlock n i value hn hi hsym hload

/-- The same statement for the weight accessor and the `gauss_wts` table. -/
theorem gauss_weight_entry_and_return_expression (ge : CGenv) (memory : Mem)
    (tableBlock : Block) (n i : Nat) (value : Floats.Float) (hn : n ≤ 10) (hi : i ≤ 10)
    (hsym : Genv.findSymbol ge.genv_genv _gauss_wts = some tableBlock)
    (hload : Mem.load .Mfloat64 memory tableBlock (8 * Binary64.Clight.tableOffset n i : Nat) =
      some (.Vfloat value)) :
    ∃ entered,
      SourceFunctionEntry CSourceData.source "gauss_weight" (.ofClight ge)
        [.Vint (Integers.Int.repr i), .Vint (Integers.Int.repr n)]
        memory (C.accessorEntryLocals memory) entered ∧
      ReturnExpressionEvaluates CSourceData.source "gauss_weight" (.ofClight ge)
        (C.accessorEntryLocals memory) entered (.Vfloat value) ∧
      C.AccessorInitialization (.ofClight ge) memory n i entered :=
  accessor_entry_and_return_expression CSourceData.source "gauss_weight" _gauss_wts
    gauss_weight_elaboration (by decide +kernel) (by decide +kernel)
    ge memory tableBlock n i value hn hi hsym hload

end Quadrature.CSource.Typed
