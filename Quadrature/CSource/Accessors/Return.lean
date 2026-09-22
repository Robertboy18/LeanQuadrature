import Quadrature.CSource.Accessors.Entry
import Quadrature.CSource.Semantics.Strategy

/-!
# Returning from the original C table accessors

Binding two integer parameters preserves permissions, so both freshly allocated
blocks stay freeable. The return expression `accessorRead table` has no side
effects, its value passes the double-to-double return cast, and freeing the
locals preserves every load from a block that existed before entry.
`AccessorInitialization.eval_funcall` assembles these into an `EvalFuncall` of
the typed accessor.
-/

namespace Quadrature.CSource.C

open CC Binary64.ClightSource

private theorem assign_int_perm {ge : ExpressionEnv} {m m' : Mem} {block : Block}
    {ofs : Integers.Ptrofs} {v result : Val}
    (h : AssignLoc ge tint m block ofs .Full v E0 m' result)
    (b : Block) (offset : Z) (kind : PermKind) (permission : Permission) :
    Mem.perm m' b offset kind permission = Mem.perm m b offset kind permission := by
  cases h with
  | value _ chunk _ hmode _ hstore =>
    have hchunk : chunk = .Mint32 := by simpa [tint, accessMode] using hmode.symm
    subst chunk
    exact Mem.perm_store hstore b offset kind permission
  | volatile _ _ _ _ _ hvolatile _ => cases hvolatile
  | copy _ _ _ _ hmode _ _ _ _ _ => cases hmode

/-- Binding parameters of type `int` leaves every permission unchanged, since each binding is a
plain 32-bit store. -/
theorem BindParameters.perm_of_int_params {ge : ExpressionEnv} {locals : Env}
    {m m' : Mem} {params : List (Ident × Ty)} {values : List Val}
    (h : BindParameters ge locals m params values m')
    (htypes : ∀ parameter ∈ params, parameter.2 = tint)
    (block : Block) (offset : Z) (kind : PermKind) (permission : Permission) :
    Mem.perm m' block offset kind permission = Mem.perm m block offset kind permission := by
  induction h with
  | nil => rfl
  | cons m name ty params value values result b m₁ m₂ _ hstore _ ih =>
    have hty : ty = tint := htypes (name, ty) (by simp)
    subst ty
    rw [ih (fun parameter hp => htypes parameter (by simp [hp]))]
    exact assign_int_perm hstore block offset kind permission

/-- Permissions after binding the accessor's parameters equal those right after allocation. -/
theorem AccessorInitialization.perm {ge : ExpressionEnv} {initial entered : Mem}
    {n i : Nat} (h : AccessorInitialization ge initial n i entered)
    (block : Block) (offset : Z) (kind : PermKind) (permission : Permission) :
    Mem.perm entered block offset kind permission =
      Mem.perm (accessorAllocatedMemory initial) block offset kind permission :=
  h.parameters.perm_of_int_params (by simp) block offset kind permission

private theorem block_ne_succ (block : Block) : block ≠ block.succ := by
  intro h
  have hn := congrArg Positive.toNat h
  simp only [Positive.toNat_succ] at hn
  omega

/-- The blocks to free at accessor return, in the order `blocksOfEnv` enumerates the environment:
the `npts` block, then the `i` block, each of four bytes. -/
theorem accessor_blocks (composites : CompositeEnv) (initial : Mem) :
    blocksOfEnv composites (accessorEntryLocals initial) =
      [(initial.nextblock.succ, 0, 4), (initial.nextblock, 0, 4)] := by
  rfl

/-- The memory after freeing the accessor's two parameter blocks from `entered`: the `npts` block
`initial.nextblock.succ` first, then the `i` block `initial.nextblock`. -/
def accessorReturnedMemory (initial entered : Mem) : Mem :=
  Mem.uncheckedFree (Mem.uncheckedFree entered initial.nextblock.succ 0 4)
    initial.nextblock 0 4

/-- Freeing the accessor's locals from `entered` succeeds and gives `accessorReturnedMemory`. The
freeability of both blocks comes from allocation, not from a hypothesis. -/
theorem AccessorInitialization.free_locals {ge : ExpressionEnv} {initial entered : Mem}
    {n i : Nat} (h : AccessorInitialization ge initial n i entered) :
    Mem.freeList entered (blocksOfEnv ge.composites (accessorEntryLocals initial)) =
      some (accessorReturnedMemory initial entered) := by
  have hn : Mem.rangePerm entered initial.nextblock.succ 0 4 .Cur .Freeable = true := by
    apply Mem.rangePerm_intro
    intro offset hlo hhi
    rw [h.perm]
    exact Mem.perm_alloc_same (Mem.alloc initial 0 4).1 0 4 offset .Cur hlo hhi
  have hi : Mem.rangePerm
      (Mem.uncheckedFree entered initial.nextblock.succ 0 4)
      initial.nextblock 0 4 .Cur .Freeable = true := by
    apply Mem.rangePerm_intro
    intro offset hlo hhi
    rw [Mem.perm_free_other _ _ _ _ _ (block_ne_succ _) _ _ _, h.perm]
    rw [show Mem.perm (accessorAllocatedMemory initial) initial.nextblock offset
          .Cur .Freeable =
        Mem.perm (Mem.alloc initial 0 4).1 initial.nextblock offset .Cur .Freeable from
      Mem.perm_alloc_other _ _ _ _ (block_ne_succ _) _ _ _]
    exact Mem.perm_alloc_same initial 0 4 offset .Cur hlo hhi
  rw [accessor_blocks, Mem.freeList, Mem.free_isSome hn]
  change Mem.freeList (Mem.uncheckedFree entered initial.nextblock.succ 0 4)
    [(initial.nextblock, 0, 4)] = _
  rw [Mem.freeList, Mem.free_isSome hi]
  rfl

/-- After the accessor returns, loads from blocks older than the call are unchanged. -/
theorem AccessorInitialization.returned_loads {ge : ExpressionEnv} {initial entered : Mem}
    {n i : Nat} (h : AccessorInitialization ge initial n i entered)
    (chunk : Chunk) (block : Block) (offset : Z) (hb : block < initial.nextblock) :
    Mem.load chunk (accessorReturnedMemory initial entered) block offset =
      Mem.load chunk initial block offset := by
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
  rw [accessorReturnedMemory, Mem.load_free_other _ _ _ _ _ _ hi,
    Mem.load_free_other _ _ _ _ _ _ hn, h.old_loads chunk block offset hb]

/-- Freeing does not lower `nextblock`: after return it is two past the entry value. -/
theorem AccessorInitialization.returned_nextblock {ge : ExpressionEnv}
    {initial entered : Mem} {n i : Nat}
    (h : AccessorInitialization ge initial n i entered) :
    (accessorReturnedMemory initial entered).nextblock = initial.nextblock.succ.succ :=
  h.nextblock

variable [ExternalCalls]

/-- `accessorRead table` has no effects: the effect phase leaves it unchanged, with empty trace and
the same memory. -/
theorem accessor_read_effects (ge : GlobalEnv) (locals : Env) (memory : Mem) (table : Ident) :
    EvalExpr ge locals memory .RV (accessorRead table) E0 memory (accessorRead table) := by
  unfold accessorRead accessorAddress accessorIndex
  repeat' first
    | apply EvalExpr.valof
    | apply EvalExpr.deref
    | apply EvalExpr.binop (t₁ := E0) (t₂ := E0) (m₁ := memory)
    | exact EvalExpr.var _ _ _ _
    | exact EvalExpr.value _ _ _ _
    | rfl

/-- Given an `AccessorInitialization` and a pure-phase evaluation of `accessorRead table` to
`Vfloat value` in the entered memory, the call of `Typed.accessor table` with `i` and `n`
returns `Vfloat value` silently in `accessorReturnedMemory`. -/
theorem AccessorInitialization.eval_funcall {ge : GlobalEnv} {initial entered : Mem}
    {n i : Nat} (h : AccessorInitialization ge.expressionEnv initial n i entered)
    (table : Ident) (value : Floats.Float)
    (hread : EvalRvalue ge.expressionEnv (accessorEntryLocals initial) entered
      (accessorRead table) (.Vfloat value)) :
    EvalFuncall ge initial (.Internal (Typed.accessor table))
      [.Vint (Integers.Int.repr i), .Vint (Integers.Int.repr n)]
      E0 (accessorReturnedMemory initial entered) (.Vfloat value) := by
  apply (h.function_entry table).eval_funcall
  · exact .return_some _ _ _ _ _ _
      (.intro _ _ _ _ _ _ _ (accessor_read_effects ge _ _ table) hread)
  · constructor
    · intro heq
      cases heq
    · rfl
  · exact h.free_locals

end Quadrature.CSource.C
