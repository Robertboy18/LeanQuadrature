import Quadrature.Compiler.Correspondence.TableAccessors

/-!
# Correspondence for the quadrature loop

Relates the Clight and Cminor integrators for the ten programs, by `BlocksAgree` on the
table blocks and the loop invariant `IntegratorTemps`. Read `integrator_call_correspondence`
first: from related memories and successful source table loads, both integrators call the
two accessors and the polynomial callback in the same order and return the same binary64
fold. The table values may be any binary64 values whose loads succeed, and the count is at
most ten, as in the source execution theorem. `integrator_return_preserved` matches any
completed standalone source call under `ExternalCallsDeterministic`.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Compiler

open CC
open Binary64.Clight
open Binary64.ClightSource
open FloatLib.Floats.Formats.BinaryInterchange

/-- The imported integrator, compiler global 69 at memory block 70. -/
def integratorTarget : Cminor.Function :=
  match h : Cminor.Imported.global69.2 with
  | .Gfun (.Internal f) => f
  | .Gfun (.External _) => False.elim (by cases h)
  | .Gvar _ => False.elim (by cases h)

/-- The target identifier of the integrator's callback parameter. -/
def integratorCallback : Ident := Positive.ofNat 79
/-- The target identifier of the integrator's count parameter. -/
def integratorCount : Ident := Positive.ofNat 87
/-- The target identifier of the loop index. -/
def integratorIndex : Ident := Positive.ofNat 82
/-- The target identifier of the running sum. -/
def integratorAccumulator : Ident := Positive.ofNat 92
/-- The target identifier receiving the current weight. -/
def integratorWeight : Ident := Positive.ofNat 128
/-- The target identifier receiving the current node. -/
def integratorNode : Ident := Positive.ofNat 129
/-- The target identifier receiving the callback's value. -/
def integratorValue : Ident := Positive.ofNat 130

/-- The Cminor symbol of the accessor. -/
def TableKind.targetFunctionSymbol : TableKind → Ident
  | .node => Positive.ofNat 107641204981888049808
  | .weight => Positive.ofNat 6882081821762725733008

-- Kernel evaluation of the accessor symbols in both symbol tables.
set_option maxRecDepth 10000 in
/-- Both symbol environments resolve the accessor symbols called inside the loop, in every
program. -/
theorem TableKind.callee_symbols (kind : TableKind) (n : Nat) :
    Genv.findSymbol (Binary64.Clight.Application.program n).globalenv.genv_genv
      (match kind with | .node => _gauss_point | .weight => _gauss_weight) =
        some kind.sourceFunctionBlock ∧
    Genv.findSymbol (Cminor.Imported.program n).globalenv kind.targetFunctionSymbol =
      some kind.targetFunctionBlock := by
  cases kind
  · exact shared_global_symbols n (id := _gauss_point) (b := Positive.ofNat 3)
      (by decide +kernel)
  · exact shared_global_symbols n (id := _gauss_weight) (b := Positive.ofNat 4)
      (by decide +kernel)

/-- The imported call of an accessor on the index and count, storing into the weight or node
variable. -/
def integratorAccessorCall (kind : TableKind) : Cminor.Stmt :=
  .Scall (some (match kind with | .node => integratorNode | .weight => integratorWeight))
    (mksignature [.Xint, .Xint] .Xfloat cc_default)
    (.Econst (.Oaddrsymbol kind.targetFunctionSymbol Integers.Ptrofs.zero))
    [.Evar integratorIndex, .Evar integratorCount]

/-- The imported call of the callback pointer on the current node. -/
def integratorCallbackCall : Cminor.Stmt :=
  .Scall (some integratorValue) (mksignature [.Xfloat] .Xfloat cc_default)
    (.Evar integratorCallback) [.Evar integratorNode]

/-- The accumulator update, rounding the multiplication before the addition in source order. -/
def integratorSum : Cminor.Expr :=
  .Ebinop .Oaddf (.Evar integratorAccumulator)
    (.Ebinop .Omulf (.Evar integratorWeight) (.Evar integratorValue))

/-- The imported loop body: weight, node, callback, then the accumulator update. -/
def integratorCalls : Cminor.Stmt :=
  .Sseq
    (.Sseq (.Sseq (integratorAccessorCall .weight) (integratorAccessorCall .node))
      integratorCallbackCall)
    (.Sassign integratorAccumulator integratorSum)

/-- The imported loop guard `i < npts`, a signed comparison. -/
def integratorGuard : Cminor.Expr :=
  .Ebinop (.Ocmp .Clt) (.Evar integratorIndex) (.Evar integratorCount)

/-- The imported increment `i = i + 1`. -/
def integratorIncrement : Cminor.Stmt :=
  .Sassign integratorIndex
    (.Ebinop .Oadd (.Evar integratorIndex) (.Econst (.Ointconst (Integers.Int.repr 1))))

/-- The imported loop: the guard with `Sexit 1` on failure, the body, and the increment. -/
def integratorLoop : Cminor.Stmt :=
  .Sloop (.Sseq (.Sblock
    (.Sseq (.Sifthenelse integratorGuard .Sskip (.Sexit 1)) integratorCalls))
    integratorIncrement)

/-- The imported return of the accumulator. -/
def integratorExit : Cminor.Stmt := .Sreturn (some (.Evar integratorAccumulator))

/-- Global 69 of the imported program is `integratorTarget`. -/
theorem integrator_target_definition :
    Cminor.Imported.global69.2 = .Gfun (.Internal integratorTarget) := rfl

/-- The imported body zeroes the accumulator and index, runs `integratorLoop` in a block, and
returns. -/
theorem integrator_target_body :
    integratorTarget.fn_body =
      .Sseq (.Sassign integratorAccumulator (.Econst (.Ofloatconst Binary64.zero)))
        (.Sseq (.Sseq
          (.Sassign integratorIndex (.Econst (.Ointconst (Integers.Int.repr 0))))
          (.Sblock integratorLoop)) integratorExit) := rfl

/-- The imported integrator takes a pointer and an int and returns a float. -/
theorem integrator_target_signature :
    integratorTarget.fn_sig = mksignature [.Xptr, .Xint] .Xfloat cc_default := rfl

/-- The imported integrator has a zero-size stack frame. -/
theorem integrator_target_stackspace : integratorTarget.fn_stackspace = 0 := rfl

/-- Only these four bindings are needed at a loop boundary. -/
structure IntegratorTemps (le : Cminor.Env) (n i : Nat) (acc : Binary64.Value) : Prop where
  callback : le.get integratorCallback =
    some (.Vptr (Positive.ofNat 71) Integers.Ptrofs.zero)
  count : le.get integratorCount = some (.Vint (Integers.Int.repr n))
  index : le.get integratorIndex = some (.Vint (Integers.Int.repr i))
  accumulator : le.get integratorAccumulator = some (.Vfloat acc)

/-- The variables after one iteration at index `i`: weight `w`, node `x`, value `y`, the rounded
accumulator, and index `i + 1`. -/
def integratorIterationTemps (le : Cminor.Env) (i : Nat) (acc w x y : Binary64.Value) :
    Cminor.Env :=
  (((((le.set integratorWeight (.Vfloat w)).set integratorNode (.Vfloat x)).set
    integratorValue (.Vfloat y)).set integratorAccumulator
      (.Vfloat (Model.add acc (Model.mul w y)))).set integratorIndex
        (.Vint (Integers.Int.repr (i + 1 : Nat))))

/-- One iteration preserves the loop invariant `temps`, advancing the index and accumulator. -/
theorem integrator_iteration_temps (le : Cminor.Env) (n i : Nat)
    (acc w x y : Binary64.Value) (temps : IntegratorTemps le n i acc) :
    IntegratorTemps (integratorIterationTemps le i acc w x y) n (i + 1)
      (Model.add acc (Model.mul w y)) := by
  constructor <;>
    simp (disch := decide) only [integratorIterationTemps, PTree.gss, PTree.gso]
  · exact temps.callback
  · exact temps.count

/-- The signed comparison agrees with the natural-number loop bound. -/
theorem integrator_guard_eval (ge : Cminor.Genv) (sp : Val)
    (le : Cminor.Env) (m : Mem) (n i : Nat) (hn : n ≤ 10) (hi : i ≤ 10)
    (hc : le.get integratorCount = some (.Vint (Integers.Int.repr n)))
    (hx : le.get integratorIndex = some (.Vint (Integers.Int.repr i))) :
    Cminor.evalExpr ge sp le m integratorGuard =
      some (Val.ofBool (decide (i < n))) := by
  simp only [integratorGuard, Cminor.evalExpr, hx, hc, bind, Option.bind_some]
  change some (Val.ofBool (decide (Integers.Int.signed (Integers.Int.repr i) <
    Integers.Int.signed (Integers.Int.repr n)))) = _
  rw [Integers.Int.signed_repr_nat i (by omega), Integers.Int.signed_repr_nat n (by omega)]
  simp

private theorem integrator_int_increment (i : Nat) :
    Integers.Int.add (Integers.Int.repr i) (Integers.Int.repr 1) =
      Integers.Int.repr (i + 1) := by
  change BitVec.ofInt 32 (i : Int) + BitVec.ofInt 32 1 =
    BitVec.ofInt 32 ((i + 1 : Nat) : Int)
  rw [← BitVec.ofInt_add]
  simp

/-- The two rounded operations in the accumulator update implement the FloatLib fold. -/
theorem integrator_sum_eval (ge : Cminor.Genv) (sp : Val) (le : Cminor.Env)
    (m : Mem) (acc w y : Binary64.Value)
    (ha : le.get integratorAccumulator = some (.Vfloat acc))
    (hw : le.get integratorWeight = some (.Vfloat w))
    (hy : le.get integratorValue = some (.Vfloat y)) :
    Cminor.evalExpr ge sp le m integratorSum =
      some (.Vfloat (Model.add acc (Model.mul w y))) := by
  simp only [integratorSum, Cminor.evalExpr, ha, hw, hy, bind, Option.bind_some]
  rfl

private def integratorLoopState (le : Cminor.Env) (k : Cminor.Cont) (sp : Val)
    (m : Mem) : Cminor.State :=
  .Running integratorTarget integratorLoop (.Kblock (.Kseq integratorExit k)) sp le m

private theorem integrator_accessor_run [ExternalCalls] (kind : TableKind)
    (applicationOrder n i : Nat) {sourceMemory targetMemory : Mem}
    (hm : BlocksAgree globalBlockMap sourceMemory targetMemory)
    (hn : n ≤ 10) (hi : i ≤ 10) (value : Binary64.Value)
    (k : Cminor.Cont) (sp : Val) (le : Cminor.Env)
    (hc : le.get integratorCount = some (.Vint (Integers.Int.repr n)))
    (hx : le.get integratorIndex = some (.Vint (Integers.Int.repr i)))
    (hload : Mem.load .Mfloat64 sourceMemory kind.sourceBlock (8 * tableOffset n i : Nat) =
      some (.Vfloat value)) :
    ∃ targetMemory',
      Cminor.Steps (Cminor.Imported.program applicationOrder).globalenv
        (.Running integratorTarget (integratorAccessorCall kind) k sp le targetMemory)
        E0 (.Running integratorTarget .Sskip k sp
          (le.set (match kind with | .node => integratorNode | .weight => integratorWeight)
            (.Vfloat value)) targetMemory') ∧
      BlocksAgree globalBlockMap sourceMemory targetMemory' ∧
      targetMemory'.nextblock = targetMemory.nextblock.succ := by
  let result := match kind with | .node => integratorNode | .weight => integratorWeight
  obtain ⟨targetMemory', _, hcallee, hrelated, hnext⟩ := kind.call_correspondence
    applicationOrder n i hm hn hi value .Kstop
    (.Kcall (some result) integratorTarget sp le k) hload
  refine ⟨targetMemory', ?_, hrelated, hnext⟩
  refine Cminor.Steps.cons (.call _ _ _ _ _ _ _ _ _
    (.Vptr kind.targetFunctionBlock Integers.Ptrofs.zero)
    [.Vint (Integers.Int.repr i), .Vint (Integers.Int.repr n)]
    (.Internal kind.targetFunction) ?_ ?_ ?_ ?_) ?_
  · apply Cminor.eval_expr_sound
    simp only [Cminor.evalExpr, Cminor.evalConstant, Genv.symbolAddress,
      (kind.callee_symbols applicationOrder).2]
  · exact .cons _ _ _ _ (.var _ _ hx) (.cons _ _ _ _ (.var _ _ hc) .nil)
  · rw [find_function_at_zero_offset]
    exact kind.target_lookup applicationOrder
  · rfl
  exact Cminor.steps_trans hcallee (Cminor.steps_single (.return_to_caller ..))

private theorem integrator_callback_run [ExternalCalls] (applicationOrder : Nat)
    {sourceMemory targetMemory : Mem}
    (hm : BlocksAgree globalBlockMap sourceMemory targetMemory)
    (x : Binary64.Value) (k : Cminor.Cont) (sp : Val) (le : Cminor.Env)
    (hf : le.get integratorCallback = some (.Vptr (Positive.ofNat 71) Integers.Ptrofs.zero))
    (hx : le.get integratorNode = some (.Vfloat x)) :
    ∃ targetMemory',
      Cminor.Steps (Cminor.Imported.program applicationOrder).globalenv
        (.Running integratorTarget integratorCallbackCall k sp le targetMemory)
        E0 (.Running integratorTarget .Sskip k sp
          (le.set integratorValue (.Vfloat (Binary64.testfun Binary64.Polynomial.cosine x)))
          targetMemory') ∧
      BlocksAgree globalBlockMap sourceMemory targetMemory' ∧
      targetMemory'.nextblock = targetMemory.nextblock.succ.succ := by
  obtain ⟨targetMemory', hcallee, hrelated, hnext⟩ :=
    callback_application_target_execution applicationOrder hm x
      (.Kcall (some integratorValue) integratorTarget sp le k)
  refine ⟨targetMemory', ?_, hrelated, hnext⟩
  refine Cminor.Steps.cons (.call _ _ _ _ _ _ _ _ _
    (.Vptr (Positive.ofNat 71) Integers.Ptrofs.zero) [.Vfloat x]
    (.Internal callbackTarget) (.var _ _ hf) (.cons _ _ _ _ (.var _ _ hx) .nil)
    ?_ rfl) ?_
  · rw [find_function_at_zero_offset]
    exact callback_target_lookup applicationOrder
  exact Cminor.steps_trans hcallee (Cminor.steps_single (.return_to_caller ..))

private theorem integrator_loop_exit [ExternalCalls] (applicationOrder : Nat)
    {sourceMemory targetMemory : Mem}
    (hm : BlocksAgree globalBlockMap sourceMemory targetMemory)
    (le : Cminor.Env) (n : Nat) (acc : Binary64.Value) (k : Cminor.Cont) (sp : Block)
    (hn : n ≤ 10) (temps : IntegratorTemps le n n acc)
    (hstack : ∀ b, globalBlockMap b = some sp → False) :
    ∃ targetMemory',
      Cminor.Steps (Cminor.Imported.program applicationOrder).globalenv
        (integratorLoopState le k (.Vptr sp Integers.Ptrofs.zero) targetMemory)
        E0 (.Returnstate (.Vfloat acc) (Cminor.callCont k) targetMemory') ∧
      BlocksAgree globalBlockMap sourceMemory targetMemory' ∧
      targetMemory'.nextblock = targetMemory.nextblock := by
  have hguard : Cminor.evalExpr (Cminor.Imported.program applicationOrder).globalenv
      (.Vptr sp Integers.Ptrofs.zero) le targetMemory integratorGuard =
      some (Val.ofBool false) := by
    simpa using integrator_guard_eval _ _ _ _ n n hn hn temps.count temps.index
  have hfree := Mem.free_isSome (Mem.rangePerm_intro targetMemory sp 0 0 .Cur .Freeable
    (fun ofs hlo hhi => by omega))
  refine ⟨_, ?_, hm.free_target hfree hstack, rfl⟩
  refine Cminor.Steps.cons (.loop ..) (Cminor.Steps.cons (.seq ..)
    (Cminor.Steps.cons (.block ..) (Cminor.Steps.cons (.seq ..) ?_)))
  refine Cminor.Steps.cons (.branch _ _ _ _ _ _ _ _ (Val.ofBool false) false
    (Cminor.eval_expr_sound hguard) (.int Integers.Int.zero)) ?_
  refine Cminor.Steps.cons (.exit_seq ..) (Cminor.Steps.cons (.exit_block_succ ..)
    (Cminor.Steps.cons (.exit_seq ..) (Cminor.Steps.cons (.exit_seq ..)
      (Cminor.Steps.cons (.exit_block_zero ..) (Cminor.Steps.cons (.skip_seq ..) ?_)))))
  exact Cminor.steps_single (.return_some _ _ _ _ _ _ _ _
    (.var _ _ temps.accumulator) hfree)

private theorem integrator_loop_iteration [ExternalCalls] (applicationOrder n i : Nat)
    {sourceMemory targetMemory : Mem}
    (hm : BlocksAgree globalBlockMap sourceMemory targetMemory)
    (le : Cminor.Env) (acc w x : Binary64.Value) (k : Cminor.Cont) (sp : Val)
    (hn : n ≤ 10) (hi : i < n) (temps : IntegratorTemps le n i acc)
    (hw : Mem.load .Mfloat64 sourceMemory (Positive.ofNat 2) (8 * tableOffset n i : Nat) =
      some (.Vfloat w))
    (hx : Mem.load .Mfloat64 sourceMemory (Positive.ofNat 1) (8 * tableOffset n i : Nat) =
      some (.Vfloat x)) :
    ∃ targetMemory',
      Cminor.Steps (Cminor.Imported.program applicationOrder).globalenv
        (integratorLoopState le k sp targetMemory) E0
        (integratorLoopState
          (integratorIterationTemps le i acc w x (Binary64.testfun Binary64.Polynomial.cosine x))
          k sp targetMemory') ∧
      BlocksAgree globalBlockMap sourceMemory targetMemory' ∧
      targetMemory'.nextblock = targetMemory.nextblock.succ.succ.succ.succ := by
  let loopCont := Cminor.Cont.Kseq integratorLoop (.Kblock (.Kseq integratorExit k))
  let iterationCont := Cminor.Cont.Kblock (.Kseq integratorIncrement loopCont)
  let sumCont := Cminor.Cont.Kseq (.Sassign integratorAccumulator integratorSum) iterationCont
  let callbackCont := Cminor.Cont.Kseq integratorCallbackCall sumCont
  let nodeCont := Cminor.Cont.Kseq (integratorAccessorCall .node) callbackCont
  let le₁ := le.set integratorWeight (.Vfloat w)
  let le₂ := le₁.set integratorNode (.Vfloat x)
  let y := Binary64.testfun Binary64.Polynomial.cosine x
  let le₃ := le₂.set integratorValue (.Vfloat y)
  have hi10 : i ≤ 10 := by omega
  obtain ⟨m₁, hweight, hm₁, hn₁⟩ := integrator_accessor_run .weight
    applicationOrder n i hm hn hi10 w nodeCont sp le temps.count temps.index hw
  obtain ⟨m₂, hnode, hm₂, hn₂⟩ := integrator_accessor_run .node
    applicationOrder n i hm₁ hn hi10 x callbackCont sp le₁
    (by simpa (disch := decide) only [le₁, PTree.gso] using temps.count)
    (by simpa (disch := decide) only [le₁, PTree.gso] using temps.index) hx
  obtain ⟨m₃, hcallback, hm₃, hn₃⟩ := integrator_callback_run applicationOrder hm₂ x
    sumCont sp le₂
    (by simpa (disch := decide) only [le₂, le₁, PTree.gso] using temps.callback)
    (by exact PTree.gss ..)
  have hguard : Cminor.evalExpr (Cminor.Imported.program applicationOrder).globalenv
      sp le targetMemory integratorGuard = some (Val.ofBool true) := by
    simpa only [hi, decide_true] using
      integrator_guard_eval _ _ _ _ n i hn hi10 temps.count temps.index
  have hsum := integrator_sum_eval (Cminor.Imported.program applicationOrder).globalenv
    sp le₃ m₃ acc w y
    (by simpa (disch := decide) only [le₃, le₂, le₁, PTree.gso] using temps.accumulator)
    (by simp (disch := decide) only [le₃, le₂, le₁, PTree.gso, PTree.gss])
    (by exact PTree.gss ..)
  have hincrement : Cminor.evalExpr (Cminor.Imported.program applicationOrder).globalenv
      sp (le₃.set integratorAccumulator (.Vfloat (Model.add acc (Model.mul w y)))) m₃
      (.Ebinop .Oadd (.Evar integratorIndex) (.Econst (.Ointconst (Integers.Int.repr 1)))) =
      some (.Vint (Integers.Int.repr (i + 1))) := by
    simp (disch := decide) only [Cminor.evalExpr, le₃, le₂, le₁, PTree.gso, temps.index,
      bind, Option.bind_some, Cminor.evalConstant, Cminor.evalBinary, Val.add]
    rw [integrator_int_increment]
  refine ⟨m₃, ?_, hm₃, ?_⟩
  · refine Cminor.Steps.cons (.loop ..) (Cminor.Steps.cons (.seq ..)
      (Cminor.Steps.cons (.block ..) (Cminor.Steps.cons (.seq ..) ?_)))
    refine Cminor.Steps.cons (.branch _ _ _ _ _ _ _ _ (Val.ofBool true) true
      (Cminor.eval_expr_sound hguard) (.int Integers.Int.one)) ?_
    refine Cminor.Steps.cons (.skip_seq ..) (Cminor.Steps.cons (.seq ..)
      (Cminor.Steps.cons (.seq ..) (Cminor.Steps.cons (.seq ..) ?_)))
    refine Cminor.steps_trans hweight (Cminor.Steps.cons (.skip_seq ..) ?_)
    refine Cminor.steps_trans hnode (Cminor.Steps.cons (.skip_seq ..) ?_)
    refine Cminor.steps_trans hcallback (Cminor.Steps.cons (.skip_seq ..) ?_)
    refine Cminor.Steps.cons (.assign _ _ _ _ _ _ _ _
      (Cminor.eval_expr_sound hsum)) ?_
    refine Cminor.Steps.cons (.skip_block ..) (Cminor.Steps.cons (.skip_seq ..) ?_)
    refine Cminor.Steps.cons (.assign _ _ _ _ _ _ _ _
      (Cminor.eval_expr_sound hincrement)) ?_
    exact Cminor.steps_single (.skip_seq ..)
  · rw [hn₃, hn₂, hn₁]

private theorem integrator_loop_suffix [ExternalCalls] (applicationOrder n : Nat)
    (hn : n ≤ 10) {sourceMemory targetMemory : Mem}
    (hm : BlocksAgree globalBlockMap sourceMemory targetMemory)
    (terms : List (Binary64.Value × Binary64.Value)) (i : Nat) (le : Cminor.Env)
    (acc : Binary64.Value) (k : Cminor.Cont) (sp : Block)
    (hlen : i + terms.length = n) (temps : IntegratorTemps le n i acc)
    (cells : TableCells sourceMemory (Positive.ofNat 1) (Positive.ofNat 2) n i terms)
    (hstack : ∀ b, globalBlockMap b = some sp → False) :
    ∃ targetMemory',
      Cminor.Steps (Cminor.Imported.program applicationOrder).globalenv
        (integratorLoopState le k (.Vptr sp Integers.Ptrofs.zero) targetMemory)
        E0 (.Returnstate
          (.Vfloat ((terms.map fun term =>
            Model.mul term.1 (Binary64.testfun Binary64.Polynomial.cosine term.2)).foldl
              Model.add acc))
          (Cminor.callCont k) targetMemory') ∧
      BlocksAgree globalBlockMap sourceMemory targetMemory' ∧
      targetMemory'.nextblock.toNat = targetMemory.nextblock.toNat + 4 * terms.length := by
  induction terms generalizing i le acc targetMemory with
  | nil =>
    have hi : i = n := by simpa using hlen
    subst i
    obtain ⟨m', hrun, hm', hnext⟩ :=
      integrator_loop_exit applicationOrder hm le n acc k sp hn temps hstack
    exact ⟨m', hrun, hm', by simp [hnext]⟩
  | cons term terms ih =>
    have hi : i < n := by simp only [List.length_cons] at hlen; omega
    obtain ⟨m₁, hiteration, hm₁, hn₁⟩ := integrator_loop_iteration applicationOrder n i hm
      le acc term.1 term.2 k (.Vptr sp Integers.Ptrofs.zero) hn hi temps cells.1 cells.2.1
    obtain ⟨m₂, htail, hm₂, hn₂⟩ := ih hm₁ (i + 1) _ _ (by
      simp only [List.length_cons] at hlen; omega)
      (integrator_iteration_temps _ _ _ _ _ _ _ temps) cells.2.2
    refine ⟨m₂, Cminor.steps_trans hiteration htail, hm₂, ?_⟩
    rw [hn₂, hn₁]
    simp only [Positive.toNat_succ, List.length_cons]
    omega

/-- The integrator's variables at entry with the callback pointer and count `n`. -/
def integratorEntryTemps (n : Nat) : Cminor.Env :=
  Cminor.setLocals integratorTarget.fn_vars
    (Cminor.setParams [.Vptr (Positive.ofNat 71) Integers.Ptrofs.zero,
      .Vint (Integers.Int.repr n)] integratorTarget.fn_params)

/-- The variables at loop entry: accumulator zero and index zero. -/
def integratorInitialTemps (n : Nat) : Cminor.Env :=
  ((integratorEntryTemps n).set integratorAccumulator (.Vfloat Binary64.zero)).set
    integratorIndex (.Vint (Integers.Int.repr 0))

/-- The loop-entry variables satisfy the invariant at index zero with accumulator zero. -/
theorem integrator_initial_temps (n : Nat) :
    IntegratorTemps (integratorInitialTemps n) n 0 Binary64.zero := by
  constructor <;> rfl

private theorem integrator_loop_entry [ExternalCalls] (ge : Cminor.Genv)
    (m : Mem) (n : Nat) (k : Cminor.Cont) :
    Cminor.Steps ge
      (.Callstate (.Internal integratorTarget)
        [.Vptr (Positive.ofNat 71) Integers.Ptrofs.zero, .Vint (Integers.Int.repr n)] k m)
      E0 (integratorLoopState (integratorInitialTemps n) k
        (.Vptr m.nextblock Integers.Ptrofs.zero) (Mem.alloc m 0 0).1) := by
  have hentry : Cminor.Step ge
      (.Callstate (.Internal integratorTarget)
        [.Vptr (Positive.ofNat 71) Integers.Ptrofs.zero, .Vint (Integers.Int.repr n)] k m)
      E0 (.Running integratorTarget integratorTarget.fn_body k
        (.Vptr m.nextblock Integers.Ptrofs.zero) (integratorEntryTemps n)
        (Mem.alloc m 0 0).1) :=
    .internal_function _ _ _ _ _ _ _ (.cons trivial (.cons trivial .nil)) rfl rfl
  rw [integrator_target_body] at hentry
  refine Cminor.Steps.cons hentry (Cminor.Steps.cons (.seq ..) ?_)
  refine Cminor.Steps.cons (.assign _ _ _ _ _ _ _ _ (.constant _ _ rfl)) ?_
  refine Cminor.Steps.cons (.skip_seq ..) (Cminor.Steps.cons (.seq ..)
    (Cminor.Steps.cons (.seq ..) ?_))
  refine Cminor.Steps.cons (.assign _ _ _ _ _ _ _ _ (.constant _ _ rfl)) ?_
  exact Cminor.Steps.cons (.skip_seq ..) (Cminor.steps_single (.block ..))

/-- The imported integrator runs from related memory `hm` and successful source loads `cells` to
the binary64 fold, with related memory. The callback is the checked internal polynomial. Each
sample allocates four zero-size frames across its three calls, and the integrator one more. -/
theorem integrator_target_execution [ExternalCalls] (applicationOrder : Nat)
    {sourceMemory targetMemory : Mem}
    (hm : BlocksAgree globalBlockMap sourceMemory targetMemory)
    (terms : List (Binary64.Value × Binary64.Value)) (hn : terms.length ≤ 10)
    (cells : TableCells sourceMemory (Positive.ofNat 1) (Positive.ofNat 2)
      terms.length 0 terms) (k : Cminor.Cont) :
    ∃ targetMemory',
      Cminor.Steps (Cminor.Imported.program applicationOrder).globalenv
        (.Callstate (.Internal integratorTarget)
          [.Vptr (Positive.ofNat 71) Integers.Ptrofs.zero,
            .Vint (Integers.Int.repr terms.length)] k targetMemory)
        E0 (.Returnstate
          (.Vfloat (Binary64.integrate (Binary64.testfun Binary64.Polynomial.cosine) terms))
          (Cminor.callCont k) targetMemory') ∧
      BlocksAgree globalBlockMap sourceMemory targetMemory' ∧
      targetMemory'.nextblock.toNat =
        targetMemory.nextblock.toNat + (4 * terms.length + 1) := by
  obtain ⟨m', hloop, hm', hnext⟩ :=
    integrator_loop_suffix applicationOrder terms.length hn (hm.alloc_target 0 0)
      terms 0 (integratorInitialTemps terms.length) Binary64.zero k targetMemory.nextblock
      (Nat.zero_add _) (integrator_initial_temps _) cells
      (fun _ hb => hm.target_ne_nextblock hb rfl)
  refine ⟨m', Cminor.steps_trans (integrator_loop_entry _ _ _ _) hloop, hm', ?_⟩
  rw [hnext]
  change targetMemory.nextblock.succ.toNat + 4 * terms.length = _
  rw [Positive.toNat_succ]
  omega

/-- The Clight environment's symbols, accessor definitions, and table cells, packaged for the
source loop theorem. -/
def integratorSourceContext (applicationOrder : Nat) (m : Mem)
    (terms : List (Binary64.Value × Binary64.Value)) (hn : terms.length ≤ 10)
    (cells : TableCells m (Positive.ofNat 1) (Positive.ofNat 2) terms.length 0 terms) :
    StoredLibraryContext (Binary64.Clight.Application.program applicationOrder).globalenv
      m terms where
  nodes := Positive.ofNat 1
  weights := Positive.ofNat 2
  point := Positive.ofNat 3
  weight := Positive.ofNat 4
  nodes_symbol := (TableKind.global_symbols .node applicationOrder).1
  weights_symbol := (TableKind.global_symbols .weight applicationOrder).1
  point_symbol := (TableKind.callee_symbols .node applicationOrder).1
  weight_symbol := (TableKind.callee_symbols .weight applicationOrder).1
  point_function := by
    rw [find_function_at_zero_offset]
    exact TableKind.source_lookup .node applicationOrder
  weight_function := by
    rw [find_function_at_zero_offset]
    exact TableKind.source_lookup .weight applicationOrder
  count_bound := hn
  cells := cells

/-- The internal callback discharges the source loop contract at any entry memory. -/
theorem integrator_callback_contract [ExternalCalls] (applicationOrder : Nat) (m : Mem) :
    LibraryCallbackContract (Binary64.Clight.Application.program applicationOrder).globalenv
      m (.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero) (.Internal f_testfun)
      (Binary64.testfun Binary64.Polynomial.cosine) where
  function_eq := by
    rw [find_function_at_zero_offset]
    exact callback_source_lookup applicationOrder
  type_eq := rfl
  execution x k hk := by
    simpa only [callCont_eq_self hk] using callback_source_execution applicationOrder m x k

/-- Execute the source body with the same table values used in the target proof. -/
theorem integrator_source_execution [ExternalCalls] (applicationOrder : Nat) (m : Mem)
    (terms : List (Binary64.Value × Binary64.Value)) (hn : terms.length ≤ 10)
    (cells : TableCells m (Positive.ofNat 1) (Positive.ofNat 2) terms.length 0 terms)
    (k : Cont) :
    StarE0 (Step2 (Binary64.Clight.Application.program applicationOrder).globalenv)
      (.Callstate (.Internal f_integrate)
        [.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero,
          .Vint (Integers.Int.repr terms.length)] k m)
      (.Returnstate
        (.Vfloat (Binary64.integrate (Binary64.testfun Binary64.Polynomial.cosine) terms))
        (callCont k) m) :=
  stored_library_execution _ m terms (integratorSourceContext applicationOrder m terms hn cells)
    (.Internal f_testfun) (Binary64.testfun Binary64.Polynomial.cosine)
    (.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero) (integrator_callback_contract _ _) k

/-- The callback arguments correspond by block renaming and the counts agree exactly. -/
theorem integrator_arguments_agree (n : Nat) :
    List.Forall₂ (ValuesAgree globalBlockMap)
      [.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero, .Vint (Integers.Int.repr n)]
      [.Vptr (Positive.ofNat 71) Integers.Ptrofs.zero, .Vint (Integers.Int.repr n)] :=
  .cons (.ptr _ (by decide +kernel)) (.cons (.int _) .nil)

/-- From related memories `hm` and table cells `cells`, both integrators return the same binary64
fold and the memories stay related. The outer continuations are arbitrary. -/
theorem integrator_call_correspondence [ExternalCalls] (applicationOrder : Nat)
    {sourceMemory targetMemory : Mem}
    (hm : BlocksAgree globalBlockMap sourceMemory targetMemory)
    (terms : List (Binary64.Value × Binary64.Value)) (hn : terms.length ≤ 10)
    (cells : TableCells sourceMemory (Positive.ofNat 1) (Positive.ofNat 2)
      terms.length 0 terms) (sourceCont : Cont) (targetCont : Cminor.Cont) :
    ∃ targetMemory',
      StarE0 (Step2 (Binary64.Clight.Application.program applicationOrder).globalenv)
        (.Callstate (.Internal f_integrate)
          [.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero,
            .Vint (Integers.Int.repr terms.length)] sourceCont sourceMemory)
        (.Returnstate
          (.Vfloat (Binary64.integrate (Binary64.testfun Binary64.Polynomial.cosine) terms))
          (callCont sourceCont) sourceMemory) ∧
      Cminor.Steps (Cminor.Imported.program applicationOrder).globalenv
        (.Callstate (.Internal integratorTarget)
          [.Vptr (Positive.ofNat 71) Integers.Ptrofs.zero,
            .Vint (Integers.Int.repr terms.length)] targetCont targetMemory)
        E0 (.Returnstate
          (.Vfloat (Binary64.integrate (Binary64.testfun Binary64.Polynomial.cosine) terms))
          (Cminor.callCont targetCont) targetMemory') ∧
      BlocksAgree globalBlockMap sourceMemory targetMemory' ∧
      targetMemory'.nextblock.toNat =
        targetMemory.nextblock.toNat + (4 * terms.length + 1) := by
  obtain ⟨m', htarget, hm', hnext⟩ :=
    integrator_target_execution applicationOrder hm terms hn cells targetCont
  exact ⟨m', integrator_source_execution applicationOrder _ terms hn cells sourceCont,
    htarget, hm', hnext⟩

/-- Every completed standalone source integration has a target run with its trace and value. -/
theorem integrator_return_preserved [calls : ExternalCalls] [ExternalCallsDeterministic calls]
    (applicationOrder : Nat) {sourceMemory targetMemory returnedMemory : Mem}
    (hm : BlocksAgree globalBlockMap sourceMemory targetMemory)
    (terms : List (Binary64.Value × Binary64.Value)) (hn : terms.length ≤ 10)
    (cells : TableCells sourceMemory (Positive.ofNat 1) (Positive.ofNat 2) terms.length 0 terms)
    {value : Val} {trace : Trace}
    (hsource : Star (Step2 (Binary64.Clight.Application.program applicationOrder).globalenv)
      (.Callstate (.Internal f_integrate)
        [.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero,
          .Vint (Integers.Int.repr terms.length)] .Kstop sourceMemory)
      trace (.Returnstate value .Kstop returnedMemory)) :
    ∃ targetMemory',
      Cminor.Steps (Cminor.Imported.program applicationOrder).globalenv
        (.Callstate (.Internal integratorTarget)
          [.Vptr (Positive.ofNat 71) Integers.Ptrofs.zero,
            .Vint (Integers.Int.repr terms.length)] .Kstop targetMemory)
        trace (.Returnstate value .Kstop targetMemory') ∧
      BlocksAgree globalBlockMap returnedMemory targetMemory' := by
  obtain ⟨htrace, hremaining⟩ := silent_execution_prefix
    (Binary64.Clight.Application.program applicationOrder)
    (integrator_source_execution applicationOrder sourceMemory terms hn cells .Kstop)
    (return_stop_no_step _ _ _) hsource
  have heq := starE0_of_stuck hremaining (return_stop_no_step _ _ _)
  rcases State.Returnstate.inj heq with ⟨rfl, _, rfl⟩
  subst trace
  obtain ⟨m', htarget, hm', _⟩ :=
    integrator_target_execution applicationOrder hm terms hn cells .Kstop
  exact ⟨m', htarget, hm'⟩

-- Kernel unfolding of the Clight global environment at block 5.
set_option maxRecDepth 10000 in
/-- Source block 5 holds the Clight integrator in every application program. -/
theorem integrator_source_lookup (n : Nat) :
    Genv.findFunctPtr (Binary64.Clight.Application.program n).globalenv.genv_genv
      (Positive.ofNat 5) = some (.Internal f_integrate) := rfl

-- Kernel evaluation of the imported global environment at block 70.
set_option maxRecDepth 100000 in
/-- Target block 70 holds the imported integrator in every imported program. -/
theorem integrator_target_lookup (n : Nat) :
    Genv.findFunctPtr (Cminor.Imported.program n).globalenv
      (Positive.ofNat 70) = some (.Internal integratorTarget) := by
  let globalsPrefix := (Cminor.Imported.program 0).prog_defs.take 72
  change Genv.findFunctPtr
    (Genv.addGlobals (Genv.emptyGenv (Cminor.Imported.program 0).prog_public)
      (globalsPrefix ++ [Cminor.Imported.mainDefinition n])) (Positive.ofNat 70) = _
  rw [find_function_before_last_global _ _ _ _ (by decide +kernel)]
  decide +kernel

-- Kernel evaluation of the integrator symbol in both symbol tables.
set_option maxRecDepth 10000 in
/-- Both symbol environments resolve the integrator symbol to its block in every program. -/
theorem integrator_global_symbols (n : Nat) :
    Genv.findSymbol (Binary64.Clight.Application.program n).globalenv.genv_genv _integrate =
      some (Positive.ofNat 5) ∧
    Genv.findSymbol (Cminor.Imported.program n).globalenv (Positive.ofNat 22083307990275538) =
      some (Positive.ofNat 70) :=
  shared_global_symbols n (id := _integrate) (b := Positive.ofNat 5) (by decide +kernel)

/-- All ten initialized rules discharge the memory and count conditions of correspondence.

The zero-node case is included and returns positive zero without reading a table.
-/
theorem initialized_integrator_correspondence [ExternalCalls] (n : Nat) (hn : n ≤ 10)
    (sourceCont : Cont) (targetCont : Cminor.Cont) :
    ∃ targetMemory',
      StarE0 (Step2 (Binary64.Clight.Application.program n).globalenv)
        (.Callstate (.Internal f_integrate)
          [.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero, .Vint (Integers.Int.repr n)]
          sourceCont Binary64.Clight.Application.entryMemory)
        (.Returnstate
          (.Vfloat (Binary64.integrate (Binary64.testfun Binary64.Polynomial.cosine)
            (storedTerms n)))
          (callCont sourceCont) Binary64.Clight.Application.entryMemory) ∧
      Cminor.Steps (Cminor.Imported.program n).globalenv
        (.Callstate (.Internal integratorTarget)
          [.Vptr (Positive.ofNat 71) Integers.Ptrofs.zero, .Vint (Integers.Int.repr n)]
          targetCont cminorEntryMemory)
        E0 (.Returnstate
          (.Vfloat (Binary64.integrate (Binary64.testfun Binary64.Polynomial.cosine)
            (storedTerms n)))
          (Cminor.callCont targetCont) targetMemory') ∧
      BlocksAgree globalBlockMap Binary64.Clight.Application.entryMemory targetMemory' ∧
      targetMemory'.nextblock.toNat = cminorEntryMemory.nextblock.toNat + (4 * n + 1) := by
  have hlength := stored_terms_length n hn
  have hbound : (storedTerms n).length ≤ 10 := by rw [hlength]; exact hn
  have hcells : TableCells Binary64.Clight.Application.entryMemory
      (Positive.ofNat 1) (Positive.ofNat 2) (storedTerms n).length 0 (storedTerms n) := by
    rw [hlength]
    exact Binary64.Clight.Application.table_cells n hn
  simpa only [hlength] using
    integrator_call_correspondence n initialized_globals_agree (storedTerms n) hbound
      hcells sourceCont targetCont

end Quadrature.Compiler
