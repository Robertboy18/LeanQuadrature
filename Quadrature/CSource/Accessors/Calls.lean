import Quadrature.CSource.Accessors.Return

/-!
# Calls obtained from the original C source

`gauss_point_call` and `gauss_weight_call` execute the two accessor bodies of
the original C program in the strategy semantics: allocation, argument stores,
return evaluation, the return cast and freeing. The caller supplies only the
table symbol, the table load and the bounds `n ≤ 10` and `i ≤ 10`.

`table_read_from_memory` was stated for a Clight `CGenv`. `expressionView`
builds a `CGenv` from a C `GlobalEnv` with the same symbols and globals and
empty function bodies, so that lemma applies to the C environment.
-/

namespace Quadrature.CSource.C

open CC Binary64.ClightSource

private def expressionViewFunction : FunDef → CC.FunDef
  | .Internal f => .Internal {
      fn_return := f.fn_return
      fn_callconv := f.fn_callconv
      fn_params := f.fn_params
      fn_vars := f.fn_vars
      fn_temps := []
      fn_body := .Sskip }
  | .External ef args res cc => .External ef args res cc

private def expressionViewDefinition : GlobDef FunDef Ty → GlobDef CC.FunDef Ty
  | .Gfun f => .Gfun (expressionViewFunction f)
  | .Gvar v => .Gvar v

private def expressionView (ge : GlobalEnv) : CGenv where
  genv_cenv := ge.composites
  genv_genv := {
    genv_public := ge.globals.genv_public
    genv_symb := ge.globals.genv_symb
    genv_defs := ge.globals.genv_defs.map1 expressionViewDefinition
    genv_next := ge.globals.genv_next }

private theorem get_map1 {α β : Type} (f : α → β) (tree : PTree α) (key : Ident) :
    (tree.map1 f).get key = (tree.get key).map f := by
  induction tree generalizing key with
  | Leaf => cases key <;> rfl
  | Node left value right ihl ihr =>
    cases key <;> simp [PTree.get, PTree.map1, ihl, ihr]

private theorem expression_view_env (ge : GlobalEnv) :
    ExpressionEnv.ofClight (expressionView ge) = ge.expressionEnv := by
  unfold ExpressionEnv.ofClight GlobalEnv.expressionEnv expressionView
  congr 1
  unfold Genv.toSenv
  congr 1
  funext block
  simp only [Genv.blockIsVolatile, Genv.findVarInfo, Genv.findDef, get_map1]
  cases ge.globals.genv_defs.get block with
  | none => rfl
  | some definition => cases definition <;> rfl

/-- `table_read_from_memory` restated for a C `GlobalEnv`: with `n` and `i` in their blocks and
`value` in the table, `accessorRead table` evaluates in the pure phase to `Vfloat value`. -/
theorem accessor_read_in_c_environment (ge : GlobalEnv) (memory : Mem)
    (count index tableBlock : Block) (table : Ident) (n i : Nat) (value : Floats.Float)
    (hn : n ≤ 10) (hi : i ≤ 10) (hnamei : table ≠ _i) (hnamen : table ≠ _npts)
    (hsym : Genv.findSymbol ge.globals table = some tableBlock)
    (hc : Mem.load .Mint32 memory count 0 = some (.Vint (Integers.Int.repr n)))
    (hx : Mem.load .Mint32 memory index 0 = some (.Vint (Integers.Int.repr i)))
    (hload : Mem.load .Mfloat64 memory tableBlock (8 * Binary64.Clight.tableOffset n i : Nat) =
      some (.Vfloat value)) :
    EvalRvalue ge.expressionEnv (accessorLocals count index) memory
      (accessorRead table) (.Vfloat value) := by
  rw [← expression_view_env ge]
  exact table_read_from_memory (expressionView ge) memory count index tableBlock table n i
    value hn hi hnamei hnamen hsym hc hx hload

/-- `AccessorExit initial final`: loads from blocks older than the call are unchanged, exactly two
blocks were allocated, and the two parameter blocks have no permissions left after freeing. -/
structure AccessorExit (initial final : Mem) : Prop where
  old_loads : ∀ chunk block offset, block < initial.nextblock →
    Mem.load chunk final block offset = Mem.load chunk initial block offset
  nextblock : final.nextblock = initial.nextblock.succ.succ
  index_permissions : ∀ offset kind permission, 0 ≤ offset → offset < 4 →
    Mem.perm final initial.nextblock offset kind permission = false
  count_permissions : ∀ offset kind permission, 0 ≤ offset → offset < 4 →
    Mem.perm final initial.nextblock.succ offset kind permission = false

/-- The memory returned by an accessor satisfies `AccessorExit`. -/
theorem AccessorInitialization.exit_state {ge : ExpressionEnv} {initial entered : Mem}
    {n i : Nat} (h : AccessorInitialization ge initial n i entered) :
    AccessorExit initial (accessorReturnedMemory initial entered) := by
  refine ⟨h.returned_loads, h.returned_nextblock, ?_, ?_⟩
  · intro offset kind permission hlo hhi
    exact Mem.perm_free_inside _ _ _ _ _ _ _ hlo hhi
  · intro offset kind permission hlo hhi
    have hne : initial.nextblock.succ ≠ initial.nextblock := by
      intro heq
      have hn := congrArg Positive.toNat heq
      simp only [Positive.toNat_succ] at hn
      omega
    rw [accessorReturnedMemory, Mem.perm_free_other _ _ _ _ _ hne]
    exact Mem.perm_free_inside _ _ _ _ _ _ _ hlo hhi

end Quadrature.CSource.C

namespace Quadrature.CSource.Typed

open CC Binary64.ClightSource

variable [ExternalCalls]

/-- `SourceFunctionCall source name ge arguments initial trace final value`: the function `name`
in `source` elaborates to some typed function whose call with `arguments` from `initial`
evaluates (`EvalFuncall`) to `value` in `final` with trace `trace`. -/
def SourceFunctionCall (source : List Char) (name : String) (ge : C.GlobalEnv)
    (arguments : List Val) (initial : Mem) (trace : Trace) (final : Mem) (value : Val) : Prop :=
  ∃ function, typedSourceFunction source name = some function ∧
    C.EvalFuncall ge initial (.Internal function) arguments trace final value

private theorem accessor_call (source : List Char) (name : String) (table : Ident)
    (hfunction : typedSourceFunction source name = some (accessor table))
    (hnamei : table ≠ _i) (hnamen : table ≠ _npts)
    (ge : C.GlobalEnv) (memory : Mem) (tableBlock : Block) (n i : Nat) (value : Floats.Float)
    (hn : n ≤ 10) (hi : i ≤ 10)
    (hsym : Genv.findSymbol ge.globals table = some tableBlock)
    (hload : Mem.load .Mfloat64 memory tableBlock (8 * Binary64.Clight.tableOffset n i : Nat) =
      some (.Vfloat value)) :
    ∃ final,
      SourceFunctionCall source name ge
        [.Vint (Integers.Int.repr i), .Vint (Integers.Int.repr n)]
        memory E0 final (.Vfloat value) ∧ C.AccessorExit memory final := by
  obtain ⟨entered, hentry⟩ := C.accessor_initialization_exists ge.expressionEnv memory n i
  refine ⟨C.accessorReturnedMemory memory entered, ?_, hentry.exit_state⟩
  refine ⟨accessor table, hfunction, hentry.eval_funcall table value ?_⟩
  exact C.accessor_read_in_c_environment ge entered memory.nextblock.succ memory.nextblock
    tableBlock table n i value hn hi hnamei hnamen hsym hentry.count_load hentry.index_load
    (hentry.preserve_load hload)

/-- Assume `gauss_pts` resolves to `tableBlock` and memory holds `value` at `8 * tableOffset n i`
there, with `n, i ≤ 10`. Then calling the node accessor of the C text with `i` and `n` returns
`Vfloat value` silently and satisfies `AccessorExit`. -/
theorem gauss_point_call (ge : C.GlobalEnv) (memory : Mem) (tableBlock : Block)
    (n i : Nat) (value : Floats.Float) (hn : n ≤ 10) (hi : i ≤ 10)
    (hsym : Genv.findSymbol ge.globals _gauss_pts = some tableBlock)
    (hload : Mem.load .Mfloat64 memory tableBlock (8 * Binary64.Clight.tableOffset n i : Nat) =
      some (.Vfloat value)) :
    ∃ final,
      SourceFunctionCall CSourceData.source "gauss_point" ge
        [.Vint (Integers.Int.repr i), .Vint (Integers.Int.repr n)]
        memory E0 final (.Vfloat value) ∧ C.AccessorExit memory final :=
  accessor_call CSourceData.source "gauss_point" _gauss_pts gauss_point_elaboration
    (by decide +kernel) (by decide +kernel) ge memory tableBlock n i value hn hi hsym hload

/-- The same statement for the weight accessor and the `gauss_wts` table. -/
theorem gauss_weight_call (ge : C.GlobalEnv) (memory : Mem) (tableBlock : Block)
    (n i : Nat) (value : Floats.Float) (hn : n ≤ 10) (hi : i ≤ 10)
    (hsym : Genv.findSymbol ge.globals _gauss_wts = some tableBlock)
    (hload : Mem.load .Mfloat64 memory tableBlock (8 * Binary64.Clight.tableOffset n i : Nat) =
      some (.Vfloat value)) :
    ∃ final,
      SourceFunctionCall CSourceData.source "gauss_weight" ge
        [.Vint (Integers.Int.repr i), .Vint (Integers.Int.repr n)]
        memory E0 final (.Vfloat value) ∧ C.AccessorExit memory final :=
  accessor_call CSourceData.source "gauss_weight" _gauss_wts gauss_weight_elaboration
    (by decide +kernel) (by decide +kernel) ge memory tableBlock n i value hn hi hsym hload

end Quadrature.CSource.Typed
