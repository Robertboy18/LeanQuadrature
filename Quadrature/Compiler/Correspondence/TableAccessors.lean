import Quadrature.Compiler.Correspondence.CallbackFunction

/-!
# Corresponding node and weight lookups

Relates the Clight and Cminor table accessors (`gauss_point`, `gauss_weight`) for the ten
programs, by `LocalsAgree` under `accessorRename` and `BlocksAgree` on the table blocks.
Read `TableKind.call_correspondence` first: both accessors compute the same triangular-table
offset, the target converting it to a 64-bit byte offset explicitly, and return the same
binary64 cell from mapped table blocks. The results cover the indices used by the ten
programs, with count and index at most ten.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Compiler

open CC
open Binary64.Clight
open Binary64.ClightSource

/-- The target identifier of the accessor's index parameter `i`. -/
def accessorIndex : Ident := Positive.ofNat 82
/-- The target identifier of the accessor's count parameter `npts`. -/
def accessorCount : Ident := Positive.ofNat 24237655
/-- The target identifier receiving the loaded cell. -/
def accessorResult : Ident := Positive.ofNat 128

/-- The signed 32-bit offset `npts * (npts - 1) / 2 + i` computed by both imported accessors. -/
def accessorTargetIndex : Cminor.Expr :=
  .Ebinop .Oadd
    (.Ebinop .Odiv
      (.Ebinop .Omul (.Evar accessorCount)
        (.Ebinop .Osub (.Evar accessorCount) (.Econst (.Ointconst (Integers.Int.repr 1)))))
      (.Econst (.Ointconst (Integers.Int.repr 2))))
    (.Evar accessorIndex)

/-- Convert an element index to a 64-bit byte offset before pointer addition. -/
def accessorTargetAddress (id : Ident) : Cminor.Expr :=
  .Ebinop .Oaddl (.Econst (.Oaddrsymbol id Integers.Ptrofs.zero))
    (.Ebinop .Omull (.Econst (.Olongconst (Integers.Int64.repr 8)))
      (.Eunop .Olongofint accessorTargetIndex))

/-- The common target body, parameterized by the table symbol. -/
def accessorTarget (id : Ident) : Cminor.Function where
  fn_sig := mksignature [.Xint, .Xint] .Xfloat cc_default
  fn_params := [accessorIndex, accessorCount]
  fn_vars := [accessorResult]
  fn_stackspace := 0
  fn_body :=
    .Sseq (.Sassign accessorResult (.Eload .Mfloat64 (accessorTargetAddress id)))
      (.Sreturn (some (.Evar accessorResult)))

/-- The Clight node accessor is `tableAccessor` at the node table. -/
theorem point_source_definition : f_gauss_point = tableAccessor _gauss_pts := rfl

/-- The Clight weight accessor is `tableAccessor` at the weight table. -/
theorem weight_source_definition : f_gauss_weight = tableAccessor _gauss_wts := rfl

/-- Global 60 of the imported program is the node accessor. -/
theorem point_target_definition :
    Cminor.Imported.global60.2 =
      .Gfun (.Internal (accessorTarget (Positive.ofNat 26025026242339472))) := rfl

/-- Global 62 of the imported program is the weight accessor. -/
theorem weight_target_definition :
    Cminor.Imported.global62.2 =
      .Gfun (.Internal (accessorTarget (Positive.ofNat 26025507278676624))) := rfl

/-- The Clight accessor's temporaries at entry with count `n` and index `i`. -/
def accessorSourceLocals (n i : Nat) : TempEnv :=
  (((PTree.empty : TempEnv).set _t'1 .Vundef).set _i
    (.Vint (Integers.Int.repr i))).set _npts (.Vint (Integers.Int.repr n))

/-- The Cminor accessor's variables at entry with count `n` and index `i`. -/
def accessorTargetLocals (n i : Nat) : Cminor.Env :=
  (((PTree.empty : Cminor.Env).set accessorResult .Vundef).set accessorIndex
    (.Vint (Integers.Int.repr i))).set accessorCount (.Vint (Integers.Int.repr n))

/-- The renaming of the accessor's two parameters. The result temporary is fixed. -/
def accessorRename : Ident ≃ Ident :=
  (Equiv.swap _i accessorIndex).trans (Equiv.swap _npts accessorCount)

/-- The renaming sends `_i` to `accessorIndex`. -/
theorem accessor_rename_index : accessorRename _i = accessorIndex := by decide +kernel

/-- The renaming sends `_npts` to `accessorCount`. -/
theorem accessor_rename_count : accessorRename _npts = accessorCount := by decide +kernel

/-- The renaming fixes `_t'1`, which equals `accessorResult`. -/
theorem accessor_rename_result : accessorRename _t'1 = accessorResult := by decide +kernel

/-- The entry environments agree under `accessorRename`. -/
theorem accessor_locals_agree (mapping : BlockMap) (n i : Nat) :
    LocalsAgree mapping accessorRename (accessorSourceLocals n i) (accessorTargetLocals n i) := by
  have h := (((LocalsAgree.empty mapping accessorRename).set
    accessorRename.injective _t'1 .undef).set accessorRename.injective _i
      (.int (Integers.Int.repr i))).set accessorRename.injective _npts
        (.int (Integers.Int.repr n))
  simpa only [accessorSourceLocals, accessorTargetLocals, accessor_rename_index,
    accessor_rename_count, accessor_rename_result] using h

/-- Entering the imported accessor with `i` and `n` binds exactly `accessorTargetLocals n i`. -/
theorem accessor_entry_locals (id : Ident) (n i : Nat) :
    Cminor.setLocals (accessorTarget id).fn_vars
      (Cminor.setParams [.Vint (Integers.Int.repr i), .Vint (Integers.Int.repr n)]
        (accessorTarget id).fn_params) = accessorTargetLocals n i := rfl

/-- The target index expression evaluates to `tableOffset n i` for counts `hn` at most ten. -/
theorem accessor_target_index_eval (ge : Cminor.Genv) (sp : Val)
    (le : Cminor.Env) (m : Mem) (n i : Nat) (hn : n ≤ 10) (_hi : i ≤ 10)
    (hc : le.get accessorCount = some (.Vint (Integers.Int.repr n)))
    (hx : le.get accessorIndex = some (.Vint (Integers.Int.repr i))) :
    Cminor.evalExpr ge sp le m accessorTargetIndex =
      some (.Vint (Integers.Int.repr (tableOffset n i))) := by
  simp only [accessorTargetIndex, Cminor.evalExpr, hc, hx, bind, Option.bind_some]
  change (Val.divs
    (.Vint (Integers.Int.mul (Integers.Int.repr n)
      (Integers.Int.sub (Integers.Int.repr n) (Integers.Int.repr 1))))
    (.Vint (Integers.Int.repr 2)) >>= fun v ↦
      some (Val.add v (.Vint (Integers.Int.repr i)))) = _
  rw [Val.divs_two]
  exact congrArg (fun x ↦ some (Val.Vint x)) (table_offset_repr n i hn)

/-- The target address expression evaluates to the table pointer at byte offset
`8 * tableOffset n i`. -/
theorem accessor_target_address_eval (ge : Cminor.Genv) (sp : Val)
    (le : Cminor.Env) (m : Mem) (id : Ident) (b : Block)
    (n i : Nat) (hn : n ≤ 10) (hi : i ≤ 10)
    (hsym : Genv.findSymbol ge id = some b)
    (hc : le.get accessorCount = some (.Vint (Integers.Int.repr n)))
    (hx : le.get accessorIndex = some (.Vint (Integers.Int.repr i))) :
    Cminor.evalExpr ge sp le m (accessorTargetAddress id) =
      some (.Vptr b (Integers.Ptrofs.repr (8 * tableOffset n i))) := by
  have hindex := accessor_target_index_eval ge sp le m n i hn hi hc hx
  simp only [accessorTargetAddress, Cminor.evalExpr, hindex, Cminor.evalConstant,
    Genv.symbolAddress, hsym, bind, Option.bind_some]
  have hsigned := Integers.Int.signed_repr_nat (tableOffset n i) (by
    have := table_offset_le n i hn hi
    omega)
  change some (Val.Vptr b (0#64 + BitVec.ofInt 64
    (((BitVec.ofInt 64 8 * BitVec.ofInt 64
      (Integers.Int.signed (Integers.Int.repr (tableOffset n i))))).toNat : Int))) = _
  rw [hsigned, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.zero_add, ← BitVec.ofInt_mul]
  congr 2

/-- Both address expressions produce pointers with equal offsets in mapped table blocks. -/
theorem accessor_addresses_agree (sourceGe : CGenv) (targetGe : Cminor.Genv)
    (sourceLocals : TempEnv) (targetLocals : Cminor.Env) (sp : Val)
    (sourceMemory targetMemory : Mem) (sourceId targetId : Ident)
    {mapping : BlockMap} {sourceBlock targetBlock : Block}
    (hb : mapping sourceBlock = some targetBlock)
    (n i : Nat) (hn : n ≤ 10) (hi : i ≤ 10)
    (hsymbol : Genv.findSymbol sourceGe.genv_genv sourceId = some sourceBlock)
    (htsymbol : Genv.findSymbol targetGe targetId = some targetBlock)
    (hsc : sourceLocals.get _npts = some (.Vint (Integers.Int.repr n)))
    (hsi : sourceLocals.get _i = some (.Vint (Integers.Int.repr i)))
    (htc : targetLocals.get accessorCount = some (.Vint (Integers.Int.repr n)))
    (hti : targetLocals.get accessorIndex = some (.Vint (Integers.Int.repr i))) :
    ∃ sourcePointer targetPointer,
      doEvalExpr sourceGe emptyEnv sourceLocals sourceMemory
        (.Ebinop .Oadd (.Evar sourceId (tarray tdouble 55))
          (tableIndex (.Etempvar _npts tint) (.Etempvar _i tint)) (tptr tdouble)) =
        some sourcePointer ∧
      Cminor.evalExpr targetGe sp targetLocals targetMemory (accessorTargetAddress targetId) =
        some targetPointer ∧
      ValuesAgree mapping sourcePointer targetPointer :=
  ⟨_, _, table_address _ _ _ _ _ n i hn hi hsymbol hsc hsi,
    accessor_target_address_eval _ _ _ _ _ _ n i hn hi htsymbol htc hti, .ptr _ hb⟩

/-- The target reads the source cell through the memory correspondence. -/
theorem accessor_target_load_eval (ge : Cminor.Genv) (sp : Val) (le : Cminor.Env)
    (id : Ident) {mapping : BlockMap} {sourceMemory targetMemory : Mem}
    (hm : BlocksAgree mapping sourceMemory targetMemory) {sourceBlock targetBlock : Block}
    (hb : mapping sourceBlock = some targetBlock)
    (n i : Nat) (hn : n ≤ 10) (hi : i ≤ 10) (value : Binary64.Value)
    (hsym : Genv.findSymbol ge id = some targetBlock)
    (hc : le.get accessorCount = some (.Vint (Integers.Int.repr n)))
    (hx : le.get accessorIndex = some (.Vint (Integers.Int.repr i)))
    (hload : Mem.load .Mfloat64 sourceMemory sourceBlock (8 * tableOffset n i : Nat) =
      some (.Vfloat value)) :
    Cminor.evalExpr ge sp le targetMemory (.Eload .Mfloat64 (accessorTargetAddress id)) =
      some (.Vfloat value) := by
  rw [Cminor.evalExpr, accessor_target_address_eval ge sp le targetMemory id targetBlock
    n i hn hi hsym hc hx]
  change Mem.load .Mfloat64 targetMemory targetBlock
    (Integers.Ptrofs.repr (8 * tableOffset n i)).unsigned = _
  rw [table_offset_unsigned n i hn hi, ← hm.load hb]
  exact hload

/-- Run the generated body, including allocation and freeing of its empty stack frame. -/
theorem accessor_target_execution [ExternalCalls]
    (ge : Cminor.Genv) (id : Ident) {mapping : BlockMap}
    {sourceMemory targetMemory : Mem} (hm : BlocksAgree mapping sourceMemory targetMemory)
    {sourceBlock targetBlock : Block} (hb : mapping sourceBlock = some targetBlock)
    (n i : Nat) (hn : n ≤ 10) (hi : i ≤ 10) (value : Binary64.Value) (k : Cminor.Cont)
    (hsym : Genv.findSymbol ge id = some targetBlock)
    (hload : Mem.load .Mfloat64 sourceMemory sourceBlock (8 * tableOffset n i : Nat) =
      some (.Vfloat value)) :
    ∃ targetMemory',
      Cminor.Steps ge
        (.Callstate (.Internal (accessorTarget id))
          [.Vint (Integers.Int.repr i), .Vint (Integers.Int.repr n)] k targetMemory)
        E0 (.Returnstate (.Vfloat value) (Cminor.callCont k) targetMemory') ∧
      BlocksAgree mapping sourceMemory targetMemory' ∧
      targetMemory'.nextblock = targetMemory.nextblock.succ := by
  obtain ⟨targetMemory', hfree, hrelated, hnext⟩ := hm.alloc_free_target_exists 0 0
  let sp : Val := .Vptr targetMemory.nextblock Integers.Ptrofs.zero
  let le := accessorTargetLocals n i
  have hentry : Cminor.Step ge
      (.Callstate (.Internal (accessorTarget id))
        [.Vint (Integers.Int.repr i), .Vint (Integers.Int.repr n)] k targetMemory) E0
      (.Running (accessorTarget id) (accessorTarget id).fn_body k sp le
        (Mem.alloc targetMemory 0 0).1) :=
    .internal_function _ _ _ _ _ _ _ (.cons trivial (.cons trivial .nil)) rfl
      (accessor_entry_locals id n i)
  refine ⟨targetMemory', Cminor.Steps.cons hentry ?_, hrelated, hnext⟩
  refine Cminor.Steps.cons (.seq ..) (Cminor.Steps.cons
    (.assign _ _ _ _ _ _ _ (.Vfloat value) ?_) ?_)
  · exact Cminor.eval_expr_sound (accessor_target_load_eval ge sp le id
      (hm.alloc_target 0 0) hb n i hn hi value hsym (by rfl) (by rfl) hload)
  refine Cminor.Steps.cons (.skip_seq ..) ?_
  exact Cminor.steps_single (.return_some _ _ _ _ _ _ _ _
    (Cminor.eval_expr_sound (by rfl)) hfree)

/-- The two stored tables share an accessor shape but have different symbols and blocks. -/
inductive TableKind where
  | node
  | weight
  deriving DecidableEq

namespace TableKind

/-- The Clight symbol of the table. -/
def sourceSymbol : TableKind → Ident
  | .node => _gauss_pts
  | .weight => _gauss_wts

/-- The Cminor symbol of the table. -/
def targetSymbol : TableKind → Ident
  | .node => Positive.ofNat 26025026242339472
  | .weight => Positive.ofNat 26025507278676624

/-- The Clight block of the table. -/
def sourceBlock : TableKind → Block
  | .node => Positive.ofNat 1
  | .weight => Positive.ofNat 2

/-- The Cminor block of the table. -/
def targetBlock : TableKind → Block
  | .node => Positive.ofNat 60
  | .weight => Positive.ofNat 62

/-- The Clight accessor of the table. -/
def sourceFunction : TableKind → Function
  | .node => f_gauss_point
  | .weight => f_gauss_weight

/-- The Cminor accessor of the table. -/
def targetFunction (kind : TableKind) : Cminor.Function := accessorTarget kind.targetSymbol

/-- The Clight block of the accessor. -/
def sourceFunctionBlock : TableKind → Block
  | .node => Positive.ofNat 3
  | .weight => Positive.ofNat 4

/-- The Cminor block of the accessor. -/
def targetFunctionBlock : TableKind → Block
  | .node => Positive.ofNat 61
  | .weight => Positive.ofNat 63

/-- The cell of a stored (weight, node) pair for this table: the second component for `.node`
and the first for `.weight`. -/
def select : TableKind → Binary64.Value × Binary64.Value → Binary64.Value
  | .node, term => term.2
  | .weight, term => term.1

/-- Each Clight accessor is `tableAccessor` at its table symbol. -/
theorem source_definition (kind : TableKind) :
    kind.sourceFunction = tableAccessor kind.sourceSymbol := by cases kind <;> rfl

/-- `globalBlockMap` sends each table's source block to its target block. -/
theorem blocks_mapped (kind : TableKind) :
    globalBlockMap kind.sourceBlock = some kind.targetBlock := by cases kind <;> decide +kernel

/-- Both symbol environments resolve the table symbol to its block in every program. -/
theorem global_symbols (kind : TableKind) (n : Nat) :
    Genv.findSymbol (Binary64.Clight.Application.program n).globalenv.genv_genv
      kind.sourceSymbol = some kind.sourceBlock ∧
    Genv.findSymbol (Cminor.Imported.program n).globalenv kind.targetSymbol =
      some kind.targetBlock := by
  have h := shared_global_symbols n (id := kind.sourceSymbol) (b := kind.sourceBlock)
    (by cases kind <;> decide +kernel)
  cases kind <;> exact h

-- Kernel unfolding of the Clight global environment at the accessor blocks.
set_option maxRecDepth 10000 in
/-- The accessor's source block holds the Clight accessor in every application program. -/
theorem source_lookup (kind : TableKind) (n : Nat) :
    Genv.findFunctPtr (Binary64.Clight.Application.program n).globalenv.genv_genv
      kind.sourceFunctionBlock = some (.Internal kind.sourceFunction) := by cases kind <;> rfl

-- Kernel evaluation of the imported global environment at the accessor blocks.
set_option maxRecDepth 100000 in
/-- The accessor's target block holds the imported accessor in every imported program. -/
theorem target_lookup (kind : TableKind) (n : Nat) :
    Genv.findFunctPtr (Cminor.Imported.program n).globalenv kind.targetFunctionBlock =
      some (.Internal kind.targetFunction) := by
  let globalsPrefix := (Cminor.Imported.program 0).prog_defs.take 72
  change Genv.findFunctPtr
    (Genv.addGlobals (Genv.emptyGenv (Cminor.Imported.program 0).prog_public)
      (globalsPrefix ++ [Cminor.Imported.mainDefinition n])) kind.targetFunctionBlock = _
  rw [find_function_before_last_global _ _ _ _ (by cases kind <;> decide +kernel)]
  cases kind <;> decide +kernel

/-- From related memories `hm` and a successful source load `hload`, both accessors return the
same cell and the memories stay related. -/
theorem call_correspondence [ExternalCalls] (kind : TableKind) (applicationOrder n i : Nat)
    {sourceMemory targetMemory : Mem}
    (hm : BlocksAgree globalBlockMap sourceMemory targetMemory)
    (hn : n ≤ 10) (hi : i ≤ 10) (value : Binary64.Value)
    (sourceCont : Cont) (targetCont : Cminor.Cont)
    (hload : Mem.load .Mfloat64 sourceMemory kind.sourceBlock (8 * tableOffset n i : Nat) =
      some (.Vfloat value)) :
    ∃ targetMemory',
      StarE0 (Step2 (Binary64.Clight.Application.program applicationOrder).globalenv)
        (.Callstate (.Internal kind.sourceFunction)
          [.Vint (Integers.Int.repr i), .Vint (Integers.Int.repr n)] sourceCont sourceMemory)
        (.Returnstate (.Vfloat value) (callCont sourceCont) sourceMemory) ∧
      Cminor.Steps (Cminor.Imported.program applicationOrder).globalenv
        (.Callstate (.Internal kind.targetFunction)
          [.Vint (Integers.Int.repr i), .Vint (Integers.Int.repr n)] targetCont targetMemory)
        E0 (.Returnstate (.Vfloat value) (Cminor.callCont targetCont) targetMemory') ∧
      BlocksAgree globalBlockMap sourceMemory targetMemory' ∧
      targetMemory'.nextblock = targetMemory.nextblock.succ := by
  obtain ⟨targetMemory', htarget, hrelated, hnext⟩ := accessor_target_execution
    (Cminor.Imported.program applicationOrder).globalenv kind.targetSymbol hm kind.blocks_mapped
    n i hn hi value targetCont (kind.global_symbols applicationOrder).2 hload
  refine ⟨targetMemory', ?_, htarget, hrelated, hnext⟩
  rw [kind.source_definition]
  exact accessor_execution _ _ _ _ n i value sourceCont hn hi
    (kind.global_symbols applicationOrder).1 hload

/-- A completed standalone source call is matched under external-call determinism. -/
theorem return_preserved [calls : ExternalCalls] [ExternalCallsDeterministic calls]
    (kind : TableKind) (applicationOrder n i : Nat)
    {sourceMemory targetMemory returnedMemory : Mem}
    (hm : BlocksAgree globalBlockMap sourceMemory targetMemory)
    (hn : n ≤ 10) (hi : i ≤ 10) (value : Binary64.Value)
    (hload : Mem.load .Mfloat64 sourceMemory kind.sourceBlock (8 * tableOffset n i : Nat) =
      some (.Vfloat value)) {returnedValue : Val} {trace : Trace}
    (hsource : Star (Step2 (Binary64.Clight.Application.program applicationOrder).globalenv)
      (.Callstate (.Internal kind.sourceFunction)
        [.Vint (Integers.Int.repr i), .Vint (Integers.Int.repr n)] .Kstop sourceMemory)
      trace (.Returnstate returnedValue .Kstop returnedMemory)) :
    ∃ targetMemory',
      Cminor.Steps (Cminor.Imported.program applicationOrder).globalenv
        (.Callstate (.Internal kind.targetFunction)
          [.Vint (Integers.Int.repr i), .Vint (Integers.Int.repr n)] .Kstop targetMemory)
        trace (.Returnstate returnedValue .Kstop targetMemory') ∧
      BlocksAgree globalBlockMap returnedMemory targetMemory' := by
  obtain ⟨targetMemory', hcanonical, htarget, hrelated, _⟩ :=
    kind.call_correspondence applicationOrder n i hm hn hi value .Kstop .Kstop hload
  obtain ⟨htrace, hremaining⟩ := silent_execution_prefix
    (Binary64.Clight.Application.program applicationOrder) hcanonical
    (return_stop_no_step _ _ _) hsource
  have heq := starE0_of_stuck hremaining (return_stop_no_step _ _ _)
  rcases State.Returnstate.inj heq with ⟨rfl, _, rfl⟩
  subst trace
  exact ⟨targetMemory', htarget, hrelated⟩

end TableKind

/-- Extract a selected node or weight from a table suffix at its absolute position. -/
theorem table_cell_lookup (kind : TableKind) (m : Mem) (nodes weights : Block) (n : Nat)
    (terms : List (Binary64.Value × Binary64.Value)) (start index : Nat)
    (term : Binary64.Value × Binary64.Value)
    (hcells : TableCells m nodes weights n start terms)
    (hget : terms[index]? = some term) :
    Mem.load .Mfloat64 m (match kind with | .node => nodes | .weight => weights)
      (8 * tableOffset n (start + index) : Nat) = some (.Vfloat (kind.select term)) := by
  induction terms generalizing start index with
  | nil => simp at hget
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst term
      cases kind
      · exact hcells.2.1
      · exact hcells.1
    | succ index =>
      have h := ih (start + 1) index hcells.2.2 hget
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 index] using h

/-- Every stored cell supplies its load premise from the initialized source program. -/
theorem initialized_table_cell (kind : TableKind) (n i : Nat) (hn : n ≤ 10)
    (term : Binary64.Value × Binary64.Value) (hget : (storedTerms n)[i]? = some term) :
    Mem.load .Mfloat64 Binary64.Clight.Application.entryMemory kind.sourceBlock
      (8 * tableOffset n i : Nat) = some (.Vfloat (kind.select term)) := by
  have h := table_cell_lookup kind _ (Positive.ofNat 1) (Positive.ofNat 2) n
    (storedTerms n) 0 i term (Binary64.Clight.Application.table_cells n hn) hget
  simp only [Nat.zero_add] at h
  cases kind <;> exact h

/-- For each of the 55 stored entries, both initialized applications return the same bits. -/
theorem initialized_accessor_correspondence [ExternalCalls] (kind : TableKind)
    (n i : Nat) (hn : n ≤ 10) (term : Binary64.Value × Binary64.Value)
    (hget : (storedTerms n)[i]? = some term) (sourceCont : Cont) (targetCont : Cminor.Cont) :
    ∃ targetMemory',
      StarE0 (Step2 (Binary64.Clight.Application.program n).globalenv)
        (.Callstate (.Internal kind.sourceFunction)
          [.Vint (Integers.Int.repr i), .Vint (Integers.Int.repr n)] sourceCont
          Binary64.Clight.Application.entryMemory)
        (.Returnstate (.Vfloat (kind.select term)) (callCont sourceCont)
          Binary64.Clight.Application.entryMemory) ∧
      Cminor.Steps (Cminor.Imported.program n).globalenv
        (.Callstate (.Internal kind.targetFunction)
          [.Vint (Integers.Int.repr i), .Vint (Integers.Int.repr n)] targetCont cminorEntryMemory)
        E0 (.Returnstate (.Vfloat (kind.select term)) (Cminor.callCont targetCont) targetMemory') ∧
      BlocksAgree globalBlockMap Binary64.Clight.Application.entryMemory targetMemory' ∧
      targetMemory'.nextblock = cminorEntryMemory.nextblock.succ := by
  have hi : i < n := by
    obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hget
    simpa only [stored_terms_length n hn] using hi
  exact kind.call_correspondence n n i initialized_globals_agree hn (by omega)
    (kind.select term) sourceCont targetCont (initialized_table_cell kind n i hn term hget)

end Quadrature.Compiler
