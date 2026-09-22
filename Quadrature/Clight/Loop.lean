import Quadrature.Clight.Library
import Quadrature.Compiler.Execution.IntegerArithmetic

/-!
# Execution of table-backed quadrature rules

`stored_library_execution` proves that the imported Clight loop `f_integrate`
returns `Vfloat (integrate f terms)` with unchanged memory for any list `terms`
of at most ten (weight, node) pairs, given a `StoredLibraryContext` (symbols,
accessor bodies and table cells) and a callback satisfying
`LibraryCallbackContract`. The loop invariant `LoopTemps` tracks the callback,
node count, index and rounded accumulator in the temporary environment, and
induction on the remaining samples composes the Clight executions of the
iterations. The `stored_library_*` theorems form the total-correctness package
(vocabulary: see `Quadrature.Clight.Execution`). These are execution theorems
about the stored bit patterns. The accuracy of the stored nodes and weights is
the subject of `Quadrature.Clight.StoredAccuracy`.
-/

namespace Quadrature.Binary64.Clight

open FloatLib.Floats.Formats.BinaryInterchange
open ClightSource

private theorem small_compare (ge : CC.CGenv) (m : CC.Mem) (i n : Nat)
    (hi : i ≤ 10) (hn : n ≤ 10) :
    CC.Cop.semBinaryOperation ge.genv_cenv .Olt
      (.Vint (CC.Integers.Int.repr i)) CC.tint
      (.Vint (CC.Integers.Int.repr n)) CC.tint m =
      some (CC.Val.ofBool (decide (i < n))) := by
  change some (CC.Val.ofBool (BitVec.slt _ _)) = _
  change some (CC.Val.ofBool (decide (CC.Integers.Int.signed (CC.Integers.Int.repr i) <
    CC.Integers.Int.signed (CC.Integers.Int.repr n)))) = _
  rw [CC.Integers.Int.signed_repr_nat i (by omega),
    CC.Integers.Int.signed_repr_nat n (by omega)]
  simp

private theorem int_increment (i : Nat) :
    CC.Integers.Int.add (CC.Integers.Int.repr i) (CC.Integers.Int.repr 1) =
      CC.Integers.Int.repr (i + 1) := by
  change BitVec.ofInt 32 (i : Int) + BitVec.ofInt 32 1 =
    BitVec.ofInt 32 ((i + 1 : Nat) : Int)
  rw [← BitVec.ofInt_add]
  simp

private def integrateFirst : CC.Stmt :=
  match f_integrate.fn_body with
  | .Ssequence _ (.Ssequence (.Ssequence _ (.Sloop first _)) _) => first
  | _ => .Sskip

private def integrateSecond : CC.Stmt :=
  match f_integrate.fn_body with
  | .Ssequence _ (.Ssequence (.Ssequence _ (.Sloop _ second)) _) => second
  | _ => .Sskip

private def integrateExit : CC.Stmt := .Sreturn (some (.Etempvar _s CC.tdouble))

private def loopState (le : CC.TempEnv) (k : CC.Cont) (m : CC.Mem) : CC.State :=
  .State f_integrate (.Sloop integrateFirst integrateSecond)
    (.Kseq integrateExit k) CC.emptyEnv le m

private structure LoopTemps (le : CC.TempEnv) (ptr : CC.Val) (n i : Nat) (acc : Value) : Prop where
  callback : le.get _f = some ptr
  count : le.get _n = some (.Vint (CC.Integers.Int.repr n))
  index : le.get _i = some (.Vint (CC.Integers.Int.repr i))
  accumulator : le.get _s = some (.Vfloat acc)


set_option maxRecDepth 20000 in
set_option maxHeartbeats 100000 in
private theorem loop_exit [CC.ExternalCalls] (ge : CC.CGenv) (m : CC.Mem)
    (le : CC.TempEnv) (ptr : CC.Val) (n : Nat) (acc : Value) (k : CC.Cont)
    (hn : n ≤ 10) (temps : LoopTemps le ptr n n acc) :
    CC.StarE0 (CC.Step2 ge) (loopState le k m)
      (.Returnstate (.Vfloat acc) (CC.callCont k) m) := by
  have hguard : CC.doEvalExpr ge CC.emptyEnv le m
      (.Ebinop .Olt (.Etempvar _i CC.tint) (.Etempvar _n CC.tint) CC.tint) =
      some (CC.Val.ofBool false) := by
    simp only [CC.doEvalExpr, temps.index, temps.count, CC.typeof]
    simpa using small_compare ge m n n hn hn
  have hret : CC.Step2 ge
      (.State f_integrate integrateExit k CC.emptyEnv le m) CC.E0
      (.Returnstate (.Vfloat acc) (CC.callCont k) m) := by
    apply CC.Step.return_1
    · exact CC.doEvalExpr_sound _ _ _ _ _ _ temps.accumulator
    · rfl
    · rfl
  repeat'
    first
    | exact CC.StarE0.step _ _ _ hret (.refl _)
    | refine CC.StarE0.step _ _ _ (CC.Step.ifthenelse _ _ _ _ _ _ _ _ _ _
        (CC.doEvalExpr_sound _ _ _ _ _ _ hguard) (by rfl)) ?_
    | refine CC.StarE0.step _ _ _ (CC.doStep_sound _ _ _ _ (by rfl)) ?_

/-- The Clight expression `count * (count - 1) / 2 + index` in signed 32-bit arithmetic, the
table index as clightgen emits it in both accessors. -/
def tableIndex (count index : CC.Expr) : CC.Expr :=
  .Ebinop .Oadd
    (.Ebinop .Odiv
      (.Ebinop .Omul count
        (.Ebinop .Osub count (.Econst_int (CC.Integers.Int.repr 1) CC.tint) CC.tint)
        CC.tint)
      (.Econst_int (CC.Integers.Int.repr 2) CC.tint) CC.tint)
    index CC.tint

/-- `tableOffset n i = n(n-1)/2 + i`, the zero-based position of node or weight `i` of the
`n`-node rule in the triangular tables. -/
def tableOffset (n i : Nat) : Nat := n * (n - 1) / 2 + i

/-- For `n, i ≤ 10`, `tableOffset n i ≤ 55`. The claims that the index fits its signed and
pointer representations are `table_offset_repr` and `table_offset_unsigned`. -/
theorem table_offset_le (n i : Nat) (hn : n ≤ 10) (hi : i ≤ 10) :
    tableOffset n i ≤ 55 := by
  have hprod : n * (n - 1) ≤ 10 * 9 := Nat.mul_le_mul hn (by omega)
  unfold tableOffset
  omega

/-- For `n ≤ 10`, the signed 32-bit arithmetic of `tableIndex` on `repr n` and `repr i` computes
`repr (tableOffset n i)`, without overflow or a negative intermediate. -/
theorem table_offset_repr (n i : Nat) (hn : n ≤ 10) :
    CC.Integers.Int.add
      (CC.Integers.Int.divs
        (CC.Integers.Int.mul (CC.Integers.Int.repr n)
          (CC.Integers.Int.sub (CC.Integers.Int.repr n) (CC.Integers.Int.repr 1)))
        (CC.Integers.Int.repr 2)) (CC.Integers.Int.repr i) =
      CC.Integers.Int.repr (tableOffset n i) := by
  have hprod : n * (n - 1) ≤ 10 * 9 := Nat.mul_le_mul hn (by omega)
  rw [CC.Integers.Int.mul_pred_repr_nat, CC.Integers.Int.divs_repr_nat_two _ (by omega)]
  change BitVec.ofInt 32 ((n * (n - 1) / 2 : Nat) : Int) +
    BitVec.ofInt 32 (i : Int) = BitVec.ofInt 32 (tableOffset n i : Int)
  rw [← BitVec.ofInt_add, tableOffset, Nat.cast_add]

private theorem table_index (ge : CC.CGenv) (le : CC.TempEnv) (m : CC.Mem)
    (n i : Nat) (hn : n ≤ 10)
    (hc : le.get _npts = some (.Vint (CC.Integers.Int.repr n)))
    (hx : le.get _i = some (.Vint (CC.Integers.Int.repr i))) :
    CC.doEvalExpr ge CC.emptyEnv le m
      (tableIndex (.Etempvar _npts CC.tint) (.Etempvar _i CC.tint)) =
      some (.Vint (CC.Integers.Int.repr (tableOffset n i))) := by
  simp only [tableIndex, CC.doEvalExpr, hc, hx, CC.typeof]
  have hsub : CC.Cop.semBinaryOperation ge.genv_cenv .Osub
      (.Vint (CC.Integers.Int.repr n)) CC.tint
      (.Vint (CC.Integers.Int.repr 1)) CC.tint m =
      some (.Vint (CC.Integers.Int.sub
        (CC.Integers.Int.repr n) (CC.Integers.Int.repr 1))) := rfl
  have hmul (a b : CC.Integers.Int) : CC.Cop.semBinaryOperation ge.genv_cenv .Omul
      (.Vint a) CC.tint (.Vint b) CC.tint m =
      some (.Vint (CC.Integers.Int.mul a b)) := rfl
  have hdiv (a : CC.Integers.Int) : CC.Cop.semBinaryOperation ge.genv_cenv .Odiv
      (.Vint a) CC.tint (.Vint (CC.Integers.Int.repr 2)) CC.tint m =
      some (.Vint (CC.Integers.Int.divs a (CC.Integers.Int.repr 2))) := CC.Val.divs_two a
  simp only [hsub, hmul, hdiv]
  exact congrArg (fun x ↦ some (CC.Val.Vint x)) (table_offset_repr n i hn)

/-- With `npts ↦ n` and `i ↦ i` in the temporaries, the address expression `id + tableIndex`
evaluates to `Vptr b (8 * tableOffset n i)`, the eight-byte cell of sample `i`, when the table
symbol `id` resolves to `b`. -/
theorem table_address (ge : CC.CGenv) (le : CC.TempEnv) (m : CC.Mem)
    (id : CC.Ident) (b : CC.Block) (n i : Nat) (hn : n ≤ 10) (hi : i ≤ 10)
    (hsym : CC.Genv.findSymbol ge.genv_genv id = some b)
    (hc : le.get _npts = some (.Vint (CC.Integers.Int.repr n)))
    (hx : le.get _i = some (.Vint (CC.Integers.Int.repr i))) :
    CC.doEvalExpr ge CC.emptyEnv le m
      (.Ebinop .Oadd (.Evar id (CC.tarray CC.tdouble 55))
        (tableIndex (.Etempvar _npts CC.tint) (.Etempvar _i CC.tint))
        (CC.tptr CC.tdouble)) =
      some (.Vptr b (CC.Integers.Ptrofs.repr (8 * tableOffset n i))) := by
  rw [CC.doEvalExpr, global_reference ge le m id _ b (by rfl) hsym,
    table_index ge le m n i hn hc hx]
  have hsigned := CC.Integers.Int.signed_repr_nat (tableOffset n i) (by
    have := table_offset_le n i hn hi
    omega)
  change some (CC.Val.Vptr b (0#64 + BitVec.ofInt 64 8 *
    BitVec.ofInt 64 (CC.Integers.Int.signed (CC.Integers.Int.repr (tableOffset n i))))) = _
  rw [hsigned, BitVec.zero_add, ← BitVec.ofInt_mul]
  congr 2

/-- For `n, i ≤ 10`, the pointer offset `8 * tableOffset n i` reads back unchanged from its
`Ptrofs` representation. -/
theorem table_offset_unsigned (n i : Nat) (hn : n ≤ 10) (hi : i ≤ 10) :
    (CC.Integers.Ptrofs.repr (8 * tableOffset n i)).unsigned =
      (8 * tableOffset n i : Nat) := by
  have hbound := table_offset_le n i hn hi
  change ((BitVec.ofInt 64 ((8 * tableOffset n i : Nat) : Int)).toNat : Int) = _
  rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- The Clight function body common to both accessors, parameterized by the table symbol `id`.
`f_gauss_point` and `f_gauss_weight` are its instances at `gauss_pts` and `gauss_wts`. -/
def tableAccessor (id : CC.Ident) : CC.Function where
  fn_return := CC.tdouble
  fn_callconv := CC.cc_default
  fn_params := [(_i, CC.tint), (_npts, CC.tint)]
  fn_vars := []
  fn_temps := [(_t'1, CC.tdouble)]
  fn_body :=
    .Ssequence
      (.Sset _t'1 (.Ederef
        (.Ebinop .Oadd (.Evar id (CC.tarray CC.tdouble 55))
          (tableIndex (.Etempvar _npts CC.tint) (.Etempvar _i CC.tint))
          (CC.tptr CC.tdouble)) CC.tdouble))
      (.Sreturn (some (.Etempvar _t'1 CC.tdouble)))

-- Step the accessor body: compute the address, load the cell into `_t'1`, return it.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- Calling `tableAccessor id` with arguments `i` and `n` (both at most 10) returns
`Vfloat value` silently with memory unchanged, when `id` resolves to `b` and memory holds
`value` at `8 * tableOffset n i` in `b`. -/
theorem accessor_execution [CC.ExternalCalls] (ge : CC.CGenv) (m : CC.Mem)
    (id : CC.Ident) (b : CC.Block) (n i : Nat) (value : Value) (k : CC.Cont)
    (hn : n ≤ 10) (hi : i ≤ 10)
    (hsym : CC.Genv.findSymbol ge.genv_genv id = some b)
    (hload : CC.Mem.load .Mfloat64 m b (8 * tableOffset n i : Nat) =
      some (.Vfloat value)) :
    CC.StarE0 (CC.Step2 ge)
      (.Callstate (.Internal (tableAccessor id))
        [.Vint (CC.Integers.Int.repr i), .Vint (CC.Integers.Int.repr n)] k m)
      (.Returnstate (.Vfloat value) (CC.callCont k) m) := by
  have hload' : CC.Mem.load .Mfloat64 m b
      (CC.Integers.Ptrofs.repr (8 * tableOffset n i)).unsigned = some (.Vfloat value) := by
    rw [table_offset_unsigned n i hn hi]
    exact hload
  repeat'
    first
    | (guard_target =~ CC.StarE0 _ (.Returnstate _ (CC.callCont k) _) _
       exact CC.StarE0.refl _)
    | refine CC.StarE0.step _ _ _ (set_float_load
        (table_address _ _ _ id b n i hn hi hsym (by rfl) (by rfl)) hload') ?_
    | refine CC.StarE0.step _ _ _ (CC.doStep_sound _ _ _ _ (by rfl)) ?_

/-- `TableFunctions ge`: the symbols `gauss_pts`, `gauss_wts`, `gauss_point` and `gauss_weight`
resolve to blocks, and the two accessor pointers are bound to the imported accessor bodies. -/
structure TableFunctions (ge : CC.CGenv) where
  nodes : CC.Block
  weights : CC.Block
  point : CC.Block
  weight : CC.Block
  nodes_symbol : CC.Genv.findSymbol ge.genv_genv _gauss_pts = some nodes
  weights_symbol : CC.Genv.findSymbol ge.genv_genv _gauss_wts = some weights
  point_symbol : CC.Genv.findSymbol ge.genv_genv _gauss_point = some point
  weight_symbol : CC.Genv.findSymbol ge.genv_genv _gauss_weight = some weight
  point_function : CC.Genv.findFunct ge.genv_genv (.Vptr point CC.Integers.Ptrofs.zero) =
    some (.Internal f_gauss_point)
  weight_function : CC.Genv.findFunct ge.genv_genv (.Vptr weight CC.Integers.Ptrofs.zero) =
    some (.Internal f_gauss_weight)

private def iterationTemps (le : CC.TempEnv) (i : Nat) (acc w x y : Value) : CC.TempEnv :=
  (((((le.set _t'1 (.Vfloat w)).set _t'2 (.Vfloat x)).set _t'3 (.Vfloat y)).set
    _s (.Vfloat (Model.add acc (Model.mul w y)))).set _i
      (.Vint (CC.Integers.Int.repr (i + 1 : Nat))))

private theorem iteration_temps (le : CC.TempEnv) (ptr : CC.Val) (n i : Nat)
    (acc w x y : Value) (temps : LoopTemps le ptr n i acc) :
    LoopTemps (iterationTemps le i acc w x y) ptr n (i + 1)
      (Model.add acc (Model.mul w y)) := by
  constructor <;>
    simp (disch := decide) only [iterationTemps, CC.PTree.gss, CC.PTree.gso]
  · exact temps.callback
  · exact temps.count

private theorem accessor_arguments (ge : CC.CGenv) (le : CC.TempEnv) (m : CC.Mem) (n i : Nat)
    (hc : le.get _n = some (.Vint (CC.Integers.Int.repr n)))
    (hx : le.get _i = some (.Vint (CC.Integers.Int.repr i))) :
    CC.doEvalExprlist ge CC.emptyEnv le m
      [.Etempvar _i CC.tint, .Etempvar _n CC.tint] [CC.tint, CC.tint] =
      some [.Vint (CC.Integers.Int.repr i), .Vint (CC.Integers.Int.repr n)] := by
  simp only [CC.doEvalExprlist, CC.doEvalExpr, hc, hx, CC.typeof]
  rfl

private theorem accumulator_expression (ge : CC.CGenv) (le : CC.TempEnv) (m : CC.Mem)
    (acc w y : Value)
    (hs : le.get _s = some (.Vfloat acc))
    (hw : le.get _t'1 = some (.Vfloat w))
    (hy : le.get _t'3 = some (.Vfloat y)) :
    CC.doEvalExpr ge CC.emptyEnv le m
      (.Ebinop .Oadd (.Etempvar _s CC.tdouble)
        (.Ebinop .Omul (.Etempvar _t'1 CC.tdouble) (.Etempvar _t'3 CC.tdouble)
          CC.tdouble) CC.tdouble) =
      some (.Vfloat (Model.add acc (Model.mul w y))) := by
  simp only [CC.doEvalExpr, hs, hw, hy, CC.typeof]
  rfl

private theorem increment_expression (ge : CC.CGenv) (le : CC.TempEnv) (m : CC.Mem) (i : Nat)
    (hx : le.get _i = some (.Vint (CC.Integers.Int.repr i))) :
    CC.doEvalExpr ge CC.emptyEnv le m
      (.Ebinop .Oadd (.Etempvar _i CC.tint)
        (.Econst_int (CC.Integers.Int.repr 1) CC.tint) CC.tint) =
      some (.Vint (CC.Integers.Int.repr (i + 1 : Nat))) := by
  simp only [CC.doEvalExpr, hx, CC.typeof]
  change some (CC.Val.Vint (CC.Integers.Int.add
    (CC.Integers.Int.repr i) (CC.Integers.Int.repr 1))) = _
  rw [int_increment]
  simp

-- Evaluate the imported body once, so that the suffix induction can reuse this execution.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem loop_iteration [CC.ExternalCalls] (ge : CC.CGenv) (m : CC.Mem)
    (ctx : TableFunctions ge) (le : CC.TempEnv) (ptr : CC.Val) (fd : CC.FunDef)
    (f : Value → Value) (n i : Nat) (acc w x : Value) (k : CC.Cont)
    (hn : n ≤ 10) (hi : i < n)
    (temps : LoopTemps le ptr n i acc)
    (contract : LibraryCallbackContract ge m ptr fd f)
    (hweight : CC.Mem.load .Mfloat64 m ctx.weights (8 * tableOffset n i : Nat) =
      some (.Vfloat w))
    (hnode : CC.Mem.load .Mfloat64 m ctx.nodes (8 * tableOffset n i : Nat) =
      some (.Vfloat x)) :
    CC.StarE0 (CC.Step2 ge) (loopState le k m)
      (loopState (iterationTemps le i acc w x (f x)) k m) := by
  have hi10 : i ≤ 10 := by omega
  have hguard : CC.doEvalExpr ge CC.emptyEnv le m
      (.Ebinop .Olt (.Etempvar _i CC.tint) (.Etempvar _n CC.tint) CC.tint) =
      some (CC.Val.ofBool true) := by
    simp only [CC.doEvalExpr, temps.index, temps.count, CC.typeof]
    simpa only [hi, decide_true] using small_compare ge m i n hi10 hn
  repeat'
    first
    | exact CC.StarE0.refl _
    | refine starE0_trans
        (accessor_execution ge m _gauss_wts ctx.weights n i w _
          hn hi10 ctx.weights_symbol hweight) ?_
    | refine starE0_trans
        (accessor_execution ge m _gauss_pts ctx.nodes n i x _
          hn hi10 ctx.nodes_symbol hnode) ?_
    | refine starE0_trans (contract.execution x _ (by rfl)) ?_
    | refine CC.StarE0.step _ _ _ (CC.Step.ifthenelse _ _ _ _ _ _ _ _ _ _
        (CC.doEvalExpr_sound _ _ _ _ _ _ hguard) (by rfl)) ?_
    | refine CC.StarE0.step _ _ _ (call_step (by rfl)
        (global_reference _ _ _ _ _ _ (by rfl) ctx.weight_symbol)
        (accessor_arguments _ _ _ n i
          (by simpa (disch := decide) only [CC.setOpttemp, CC.PTree.gso] using temps.count)
          (by simpa (disch := decide) only [CC.setOpttemp, CC.PTree.gso] using temps.index))
        ctx.weight_function (by rfl)) ?_
    | refine CC.StarE0.step _ _ _ (call_step (by rfl)
        (global_reference _ _ _ _ _ _ (by rfl) ctx.point_symbol)
        (accessor_arguments _ _ _ n i
          (by simpa (disch := decide) only [CC.setOpttemp, CC.PTree.gso] using temps.count)
          (by simpa (disch := decide) only [CC.setOpttemp, CC.PTree.gso] using temps.index))
        ctx.point_function (by rfl)) ?_
    | refine CC.StarE0.step _ _ _ (call_step (by rfl)
        (by simpa (disch := decide) only [CC.doEvalExpr, CC.setOpttemp, CC.PTree.gso]
              using temps.callback)
        (by
          simp (disch := decide) only [CC.doEvalExprlist, CC.doEvalExpr,
            CC.setOpttemp, CC.PTree.gss, CC.typeof]
          rfl)
        contract.function_eq contract.type_eq) ?_
    | refine CC.StarE0.step _ _ _ (CC.Step.set _ _ _ _ _ _ _ _
        (CC.doEvalExpr_sound _ _ _ _ _ _
          (accumulator_expression _ _ _ acc w (f x)
            (by simpa (disch := decide) only [CC.setOpttemp, CC.PTree.gso] using temps.accumulator)
            (by simp (disch := decide) only [CC.setOpttemp, CC.PTree.gso, CC.PTree.gss])
            (by simp (disch := decide) only [CC.setOpttemp, CC.PTree.gss])))) ?_
    | refine CC.StarE0.step _ _ _ (CC.Step.set _ _ _ _ _ _ _ _
        (CC.doEvalExpr_sound _ _ _ _ _ _
          (increment_expression _ _ _ i
            (by simpa (disch := decide) only [CC.setOpttemp, CC.PTree.gso] using temps.index)))) ?_
    | refine CC.StarE0.step _ _ _ (CC.doStep_sound _ _ _ _ (by rfl)) ?_

/-- `TableCells m nodes weights n i terms`: for the j-th pair `(w, x)` of `terms`, block
`weights` holds `Vfloat w` and block `nodes` holds `Vfloat x` at byte offset
`8 * tableOffset n (i + j)` in `m`. Pairs are (weight, node), as in `integrate`. -/
def TableCells (m : CC.Mem) (nodes weights : CC.Block) (n : Nat) :
    Nat → List (Value × Value) → Prop
  | _, [] => True
  | i, term :: terms =>
    CC.Mem.load .Mfloat64 m weights (8 * tableOffset n i : Nat) = some (.Vfloat term.1) ∧
    CC.Mem.load .Mfloat64 m nodes (8 * tableOffset n i : Nat) = some (.Vfloat term.2) ∧
    TableCells m nodes weights n (i + 1) terms

private theorem loop_suffix [CC.ExternalCalls] (ge : CC.CGenv) (m : CC.Mem)
    (ctx : TableFunctions ge) (ptr : CC.Val) (fd : CC.FunDef) (f : Value → Value)
    (contract : LibraryCallbackContract ge m ptr fd f)
    (n : Nat) (hn : n ≤ 10) (terms : List (Value × Value))
    (i : Nat) (le : CC.TempEnv) (acc : Value) (k : CC.Cont)
    (hlen : i + terms.length = n) (temps : LoopTemps le ptr n i acc)
    (cells : TableCells m ctx.nodes ctx.weights n i terms) :
    CC.StarE0 (CC.Step2 ge) (loopState le k m)
      (.Returnstate
        (.Vfloat ((terms.map fun term => Model.mul term.1 (f term.2)).foldl Model.add acc))
        (CC.callCont k) m) := by
  induction terms generalizing i le acc with
  | nil =>
    have hi : i = n := by simpa using hlen
    subst i
    exact loop_exit ge m le ptr n acc k hn temps
  | cons term terms ih =>
    obtain ⟨w, x⟩ := term
    obtain ⟨hweight, hnode, hrest⟩ := cells
    have hi : i < n := by simp only [List.length_cons] at hlen; omega
    refine starE0_trans
      (loop_iteration ge m ctx le ptr fd f n i acc w x k hn hi temps contract
        hweight hnode) ?_
    exact ih (i + 1) _ (Model.add acc (Model.mul w (f x)))
      (by simp only [List.length_cons] at hlen; omega)
      (iteration_temps le ptr n i acc w x (f x) temps) hrest

private def entryTemps (ptr : CC.Val) (n : Nat) : CC.TempEnv :=
  ((((CC.createUndefTemps f_integrate.fn_temps).set _f ptr).set _n
    (.Vint (CC.Integers.Int.repr n))).set _s (.Vfloat zero)).set _i
      (.Vint (CC.Integers.Int.repr 0))

private theorem entry_temps (ptr : CC.Val) (n : Nat) :
    LoopTemps (entryTemps ptr n) ptr n 0 zero := by
  constructor <;> rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 100000 in
private theorem loop_entry [CC.ExternalCalls] (ge : CC.CGenv) (m : CC.Mem)
    (ptr : CC.Val) (n : Nat) (k : CC.Cont) :
    CC.StarE0 (CC.Step2 ge)
      (.Callstate (.Internal f_integrate) [ptr, .Vint (CC.Integers.Int.repr n)] k m)
      (loopState (entryTemps ptr n) k m) := by
  repeat'
    first
    | exact CC.StarE0.refl _
    | refine CC.StarE0.step _ _ _ (CC.doStep_sound _ _ _ _ (by rfl)) ?_

/-- `StoredLibraryContext ge m terms`: a `TableFunctions ge` together with `terms.length ≤ 10`
and the table cells of `terms` for the rule with `terms.length` nodes, starting at index 0. -/
structure StoredLibraryContext (ge : CC.CGenv) (m : CC.Mem)
    (terms : List (Value × Value)) extends TableFunctions ge where
  count_bound : terms.length ≤ 10
  cells : TableCells m nodes weights terms.length 0 terms

/-- The state entering `f_integrate` with callback pointer `ptr`, node count `n`, continuation
`k` and memory `m`. -/
def storedLibraryCall (ptr : CC.Val) (n : Nat) (k : CC.Cont) (m : CC.Mem) : CC.State :=
  .Callstate (.Internal f_integrate) [ptr, .Vint (CC.Integers.Int.repr n)] k m

/-- Given a `StoredLibraryContext` for `terms` and a callback meeting `LibraryCallbackContract`,
the call with `terms.length` nodes runs silently to `Returnstate (Vfloat (integrate f terms))`
with memory `m` unchanged. -/
theorem stored_library_execution [CC.ExternalCalls] (ge : CC.CGenv) (m : CC.Mem)
    (terms : List (Value × Value)) (ctx : StoredLibraryContext ge m terms)
    (fd : CC.FunDef) (f : Value → Value) (ptr : CC.Val)
    (contract : LibraryCallbackContract ge m ptr fd f) (k : CC.Cont) :
    CC.StarE0 (CC.Step2 ge) (storedLibraryCall ptr terms.length k m)
      (.Returnstate (.Vfloat (integrate f terms)) (CC.callCont k) m) :=
  starE0_trans (loop_entry ge m ptr terms.length k)
    (loop_suffix ge m ctx.toTableFunctions ptr fd f contract terms.length ctx.count_bound
      terms 0 (entryTemps ptr terms.length) zero k (Nat.zero_add _) (entry_temps _ _) ctx.cells)

/-- Total-correctness package: every run from the call is silent and can finish with the stated
value and memory. -/
theorem stored_library_prefix [calls : CC.ExternalCalls] [CC.ExternalCallsDeterministic calls]
    (program : CC.Program) (m : CC.Mem) (terms : List (Value × Value))
    (ctx : StoredLibraryContext program.globalenv m terms)
    (fd : CC.FunDef) (f : Value → Value) (ptr : CC.Val)
    (contract : LibraryCallbackContract program.globalenv m ptr fd f)
    (trace : CC.Trace) (state : CC.State)
    (h : CC.Star (CC.Step2 program.globalenv)
      (storedLibraryCall ptr terms.length .Kstop m) trace state) :
    trace = CC.E0 ∧ CC.StarE0 (CC.Step2 program.globalenv) state
      (.Returnstate (.Vfloat (integrate f terms)) .Kstop m) :=
  silent_execution_prefix program
    (stored_library_execution program.globalenv m terms ctx fd f ptr contract .Kstop)
    (return_stop_no_step _ _ _) h

/-- Total-correctness package: every finished run ends in the stated return state. -/
theorem stored_library_return_state [calls : CC.ExternalCalls]
    [CC.ExternalCallsDeterministic calls]
    (program : CC.Program) (m : CC.Mem) (terms : List (Value × Value))
    (ctx : StoredLibraryContext program.globalenv m terms)
    (fd : CC.FunDef) (f : Value → Value) (ptr : CC.Val)
    (contract : LibraryCallbackContract program.globalenv m ptr fd f)
    (value : CC.Val) (memory : CC.Mem) (trace : CC.Trace)
    (h : CC.Star (CC.Step2 program.globalenv)
      (storedLibraryCall ptr terms.length .Kstop m) trace
      (.Returnstate value .Kstop memory)) :
    CC.State.Returnstate value .Kstop memory =
      .Returnstate (.Vfloat (integrate f terms)) .Kstop m :=
  CC.starE0_of_stuck (stored_library_prefix program m terms ctx fd f ptr contract trace _ h).2
    (return_stop_no_step _ value memory)

/-- Total-correctness package: the returned value is `Vfloat (integrate f terms)` bit for bit,
including the sign of zero and any NaN payload. -/
theorem stored_library_return_eq [calls : CC.ExternalCalls]
    [CC.ExternalCallsDeterministic calls]
    (program : CC.Program) (m : CC.Mem) (terms : List (Value × Value))
    (ctx : StoredLibraryContext program.globalenv m terms)
    (fd : CC.FunDef) (f : Value → Value) (ptr : CC.Val)
    (contract : LibraryCallbackContract program.globalenv m ptr fd f)
    (value : CC.Val) (memory : CC.Mem) (trace : CC.Trace)
    (h : CC.Star (CC.Step2 program.globalenv)
      (storedLibraryCall ptr terms.length .Kstop m) trace
      (.Returnstate value .Kstop memory)) :
    value = .Vfloat (integrate f terms) :=
  (CC.State.Returnstate.inj
    (stored_library_return_state program m terms ctx fd f ptr contract value memory trace h)).1

/-- Total-correctness package: the returned memory is the entry memory. -/
theorem stored_library_return_memory [calls : CC.ExternalCalls]
    [CC.ExternalCallsDeterministic calls]
    (program : CC.Program) (m : CC.Mem) (terms : List (Value × Value))
    (ctx : StoredLibraryContext program.globalenv m terms)
    (fd : CC.FunDef) (f : Value → Value) (ptr : CC.Val)
    (contract : LibraryCallbackContract program.globalenv m ptr fd f)
    (value : CC.Val) (memory : CC.Mem) (trace : CC.Trace)
    (h : CC.Star (CC.Step2 program.globalenv)
      (storedLibraryCall ptr terms.length .Kstop m) trace
      (.Returnstate value .Kstop memory)) :
    memory = m :=
  (CC.State.Returnstate.inj
    (stored_library_return_state program m terms ctx fd f ptr contract value memory trace h)).2.2

/-- Total-correctness package: every reachable state is the stated return state or has a silent
successor. -/
theorem stored_library_progress [calls : CC.ExternalCalls] [CC.ExternalCallsDeterministic calls]
    (program : CC.Program) (m : CC.Mem) (terms : List (Value × Value))
    (ctx : StoredLibraryContext program.globalenv m terms)
    (fd : CC.FunDef) (f : Value → Value) (ptr : CC.Val)
    (contract : LibraryCallbackContract program.globalenv m ptr fd f)
    (trace : CC.Trace) (state : CC.State)
    (h : CC.Star (CC.Step2 program.globalenv)
      (storedLibraryCall ptr terms.length .Kstop m) trace state) :
    state = .Returnstate (.Vfloat (integrate f terms)) .Kstop m ∨
      ∃ next, CC.Step2 program.globalenv state CC.E0 next := by
  have hremaining :=
    (stored_library_prefix program m terms ctx fd f ptr contract trace state h).2
  cases hremaining with
  | refl => exact Or.inl rfl
  | step _ next _ hstep _ => exact Or.inr ⟨next, hstep⟩

/-- Total-correctness package: no infinite sequence of steps starts at the call. -/
theorem stored_library_not_infinite [calls : CC.ExternalCalls]
    [CC.ExternalCallsDeterministic calls]
    (program : CC.Program) (m : CC.Mem) (terms : List (Value × Value))
    (ctx : StoredLibraryContext program.globalenv m terms)
    (fd : CC.FunDef) (f : Value → Value) (ptr : CC.Val)
    (contract : LibraryCallbackContract program.globalenv m ptr fd f)
    (states : Nat → CC.State) (traces : Nat → CC.Trace)
    (hstart : states 0 = storedLibraryCall ptr terms.length .Kstop m)
    (hsteps : ∀ n, CC.Step2 program.globalenv (states n) (traces n) (states (n + 1))) : False :=
  silent_execution_not_infinite program
    (stored_library_execution program.globalenv m terms ctx fd f ptr contract .Kstop)
    (return_stop_no_step _ _ _) states traces hstart hsteps

end Quadrature.Binary64.Clight
