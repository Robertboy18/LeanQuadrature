import Quadrature.CSource.Semantics.SimpleRefinement
import Quadrature.Clight.Loop

/-!
# Table lookups with the accessor parameters stored in memory

The original accessors compute `table[(npts * (npts - 1)) / 2 + i]`.
`table_read_from_memory` evaluates the same address and loaded value in the
pure phase of the strategy semantics, with `npts` and `i` read from their
memory blocks. The proof transfers the Clight evaluation of
`Quadrature.Clight.Loop` through `evalRvalue_of_clight`, discharging its
`LocalMatch` invariant from the two integer loads.
-/

namespace Quadrature.CSource.C

open CC Quadrature.Binary64.ClightSource

private def accessorTypes : PTree Ty :=
  (PTree.empty.set _npts tint).set _i tint

/-- The C environment of either accessor: `npts` in block `count` and `i` in block `index`, both of
type `int`. -/
def accessorLocals (count index : Block) : Env :=
  (PTree.empty.set _npts (count, tint)).set _i (index, tint)

private def accessorValues (n i : Nat) : TempEnv :=
  (PTree.empty.set _npts (.Vint (Integers.Int.repr n))).set _i
    (.Vint (Integers.Int.repr i))

private theorem get_set {α : Type} (tree : PTree α) (key name : Ident) (value : α) :
    (tree.set key value).get name = if name = key then some value else tree.get name := by
  by_cases h : name = key
  · subst name
    simp
  · rw [ite_eq_right h]
    exact PTree.gso key name value tree (Ne.symm h)

private theorem index_ne_count : _i ≠ _npts := by decide +kernel

private theorem accessor_locals_match (m : Mem) (count index : Block) (n i : Nat)
    (hc : Mem.load .Mint32 m count 0 = some (.Vint (Integers.Int.repr n)))
    (hi : Mem.load .Mint32 m index 0 = some (.Vint (Integers.Int.repr i))) :
    LocalMatch accessorTypes (accessorLocals count index) emptyEnv (accessorValues n i) m := by
  constructor
  · intro name ht
    by_cases hx : name = _i
    · simp [accessorTypes, hx] at ht
    · by_cases hn : name = _npts
      · simp [accessorTypes, get_set, hn, index_ne_count.symm] at ht
      · simp [accessorLocals, emptyEnv, get_set, hx, hn]
  · intro name ty ht v hv
    by_cases hx : name = _i
    · subst name
      have hty : ty = tint := by simpa [accessorTypes] using ht.symm
      subst ty
      have hvalue : v = .Vint (Integers.Int.repr i) := by
        simpa [accessorValues] using hv.symm
      subst v
      refine ⟨index, by simp [accessorLocals], .value .Mint32 _ rfl ?_⟩
      exact hi
    · by_cases hn : name = _npts
      · subst name
        have hty : ty = tint := by
          simpa [accessorTypes, get_set, hx] using ht.symm
        subst ty
        have hvalue : v = .Vint (Integers.Int.repr n) := by
          simpa [accessorValues, get_set, hx] using hv.symm
        subst v
        refine ⟨count, by simp [accessorLocals, get_set, hx], .value .Mint32 _ rfl ?_⟩
        exact hc
      · simp [accessorTypes, get_set, hx, hn] at ht

private def clightTableAddress (table : Ident) : CC.Expr :=
  .Ebinop .Oadd (.Evar table (tarray tdouble 55))
    (Binary64.Clight.tableIndex (.Etempvar _npts tint) (.Etempvar _i tint))
    (tptr tdouble)

/-- The typed C index expression `npts * (npts - 1) / 2 + i`, in signed `int` arithmetic with
explicit reads of both parameters. -/
def accessorIndex : Expr :=
  .Ebinop .Oadd
    (.Ebinop .Odiv
      (.Ebinop .Omul (.Evalof (.Evar _npts tint) tint)
        (.Ebinop .Osub (.Evalof (.Evar _npts tint) tint)
          (.Eval (.Vint (Integers.Int.repr 1)) tint) tint) tint)
      (.Eval (.Vint (Integers.Int.repr 2)) tint) tint)
    (.Evalof (.Evar _i tint) tint) tint

/-- The typed C address `table + accessorIndex`, of type pointer to `double`. -/
def accessorAddress (table : Ident) : Expr :=
  .Ebinop .Oadd (.Evalof (.Evar table (tarray tdouble 55)) (tarray tdouble 55))
    accessorIndex (tptr tdouble)

/-- The typed C read `*(table + accessorIndex)`, the return expression of both accessors. -/
def accessorRead (table : Ident) : Expr :=
  .Evalof (.Ederef (accessorAddress table) tdouble) tdouble

private theorem reify_table_address (table : Ident) :
    reifyExpr true (clightTableAddress table) = accessorAddress table := rfl

private theorem table_address_supported (table : Ident)
    (hi : table ≠ _i) (hn : table ≠ _npts) :
    Supported accessorTypes (clightTableAddress table) := by
  simp [clightTableAddress, Binary64.Clight.tableIndex, Supported, accessorTypes,
    get_set, hi, hn, index_ne_count.symm, typeIsVolatile, accessMode, tint,
    tdouble, tarray, noattr, Ty.attr]

/-- With `n` in block `count` and `i` in block `index` (both at most 10), `accessorAddress table`
evaluates in the pure phase to `Vptr tableBlock (8 * tableOffset n i)` when `table` resolves to
`tableBlock`. The table name must differ from `i` and `npts`. -/
theorem table_address_from_memory (ge : CGenv) (m : Mem)
    (count index tableBlock : Block) (table : Ident) (n i : Nat)
    (hn : n ≤ 10) (hi : i ≤ 10) (hnamei : table ≠ _i) (hnamen : table ≠ _npts)
    (hsym : Genv.findSymbol ge.genv_genv table = some tableBlock)
    (hc : Mem.load .Mint32 m count 0 = some (.Vint (Integers.Int.repr n)))
    (hx : Mem.load .Mint32 m index 0 = some (.Vint (Integers.Int.repr i))) :
    EvalRvalue (.ofClight ge) (accessorLocals count index) m (accessorAddress table)
      (.Vptr tableBlock (Integers.Ptrofs.repr (8 * Binary64.Clight.tableOffset n i))) := by
  rw [← reify_table_address]
  apply evalRvalue_of_clight (accessor_locals_match m count index n i hc hx)
  · apply doEvalExpr_sound
    exact Binary64.Clight.table_address ge (accessorValues n i) m table tableBlock n i
      hn hi hsym (by simp [accessorValues, get_set, index_ne_count.symm])
      (by simp [accessorValues])
  · exact table_address_supported table hnamei hnamen

/-- Under the hypotheses of `table_address_from_memory`, and with `value` stored at that
address, `accessorRead table` evaluates in the pure phase to `Vfloat value`. -/
theorem table_read_from_memory (ge : CGenv) (m : Mem)
    (count index tableBlock : Block) (table : Ident) (n i : Nat) (value : Floats.Float)
    (hn : n ≤ 10) (hi : i ≤ 10) (hnamei : table ≠ _i) (hnamen : table ≠ _npts)
    (hsym : Genv.findSymbol ge.genv_genv table = some tableBlock)
    (hc : Mem.load .Mint32 m count 0 = some (.Vint (Integers.Int.repr n)))
    (hx : Mem.load .Mint32 m index 0 = some (.Vint (Integers.Int.repr i)))
    (hload : Mem.load .Mfloat64 m tableBlock (8 * Binary64.Clight.tableOffset n i : Nat) =
      some (.Vfloat value)) :
    EvalRvalue (.ofClight ge) (accessorLocals count index) m (accessorRead table)
      (.Vfloat value) := by
  apply EvalRvalue.rvalof tableBlock _ .Full _ tdouble (.Vfloat value)
  · exact .deref _ tdouble tableBlock _
      (table_address_from_memory ge m count index tableBlock table n i hn hi
        hnamei hnamen hsym hc hx)
  · rfl
  · rfl
  · apply DerefLoc.value .Mfloat64 (.Vfloat value) rfl rfl
    change Mem.load .Mfloat64 m tableBlock
      (Integers.Ptrofs.repr (8 * Binary64.Clight.tableOffset n i)).unsigned = _
    rw [Binary64.Clight.table_offset_unsigned n i hn hi]
    exact hload

end Quadrature.CSource.C
