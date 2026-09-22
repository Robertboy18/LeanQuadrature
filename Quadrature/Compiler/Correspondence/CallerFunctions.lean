import Quadrature.Compiler.Cminor.StoredTotalCorrectness
import Quadrature.Compiler.Correspondence.IntegratorFunction

/-!
# The callers above the quadrature integrator

Relates the Clight and Cminor callers of the integrator for the ten programs, the two-point
wrapper `integrate_testfun` and the entry point `main`, by `BlocksAgree` on global memory.
Read `main_final_observations_iff` first: for n = 1..10, the Clight and Cminor programs have
the same observations (event trace, exit status), under `ExternalCallsDeterministic`. The
target executions compose the integrator theorem through the imported call continuations,
preserve mapped memory, and free the caller's own empty frame.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Compiler

open CC
open Binary64.Clight
open Binary64.ClightSource

/-- The original two-point wrapper, at target block 72. -/
def wrapperTarget : Cminor.Function :=
  match h : Cminor.Imported.global71.2 with
  | .Gfun (.Internal f) => f
  | .Gfun (.External _) => False.elim (by cases h)
  | .Gvar _ => False.elim (by cases h)

/-- The imported entry point of the n-node program, at target block 73. -/
def mainTarget (n : Nat) : Cminor.Function :=
  match h : (Cminor.Imported.mainDefinition n).2 with
  | .Gfun (.Internal f) => f
  | .Gfun (.External _) => False.elim (by cases h)
  | .Gvar _ => False.elim (by cases h)

/-- The imported call of the integrator on the callback symbol and count `n`, storing into
`result`. -/
def callerIntegratorCall (result : Ident) (n : Nat) : Cminor.Stmt :=
  .Scall (some result) (mksignature [.Xptr, .Xint] .Xfloat cc_default)
    (.Econst (.Oaddrsymbol (Positive.ofNat 22083307990275538) Integers.Ptrofs.zero))
    [.Econst (.Oaddrsymbol (Positive.ofNat 6011066106781) Integers.Ptrofs.zero),
     .Econst (.Ointconst (Integers.Int.repr n))]

/-- The imported wrapper's return of its result variable. -/
def wrapperReturn : Cminor.Stmt := .Sreturn (some (.Evar (Positive.ofNat 128)))

/-- The imported `quadrature-result` annotation of the result temporary. -/
def mainObservation : Cminor.Stmt :=
  .Sbuiltin none (.EF_annot (Positive.ofNat 1) "quadrature-result" [.Tfloat])
    [.Evar Application.resultTemp]

/-- The imported `return 0`. -/
def mainExit : Cminor.Stmt :=
  .Sreturn (some (.Econst (.Ointconst Integers.Int.zero)))

/-- Global 71 of the imported program is `wrapperTarget`. -/
theorem wrapper_target_definition :
    Cminor.Imported.global71.2 = .Gfun (.Internal wrapperTarget) := rfl

/-- The imported wrapper calls the integrator with count two and returns the result. -/
theorem wrapper_target_body :
    wrapperTarget.fn_body =
      .Sseq (callerIntegratorCall (Positive.ofNat 128) 2) wrapperReturn := rfl

/-- The last global of the n-node imported program is `mainTarget n`. -/
theorem main_target_definition (n : Nat) :
    (Cminor.Imported.mainDefinition n).2 = .Gfun (.Internal (mainTarget n)) := rfl

/-- The imported `main` calls the integrator with count `n`, annotates the result, and exits. -/
theorem main_target_body (n : Nat) :
    (mainTarget n).fn_body =
      .Sseq (callerIntegratorCall Application.resultTemp n)
        (.Sseq mainObservation mainExit) := rfl

-- Kernel evaluation of the callback symbol in both symbol tables.
set_option maxRecDepth 10000 in
/-- Both symbol environments resolve the callback symbol to its block in every program. -/
theorem caller_callback_symbols (n : Nat) :
    Genv.findSymbol (Application.program n).globalenv.genv_genv _testfun =
      some (Positive.ofNat 6) ∧
    Genv.findSymbol (Cminor.Imported.program n).globalenv (Positive.ofNat 6011066106781) =
      some (Positive.ofNat 71) :=
  shared_global_symbols n (id := _testfun) (b := Positive.ofNat 6) (by decide +kernel)

/-- The imported integrator call resumes its caller with the binary64 fold in `result`, from
related memory `hm` and table cells `cells`. -/
theorem caller_integrator_execution [ExternalCalls] (applicationOrder : Nat)
    {sourceMemory targetMemory : Mem}
    (hm : BlocksAgree globalBlockMap sourceMemory targetMemory)
    (terms : List (Binary64.Value × Binary64.Value)) (hn : terms.length ≤ 10)
    (cells : TableCells sourceMemory (Positive.ofNat 1) (Positive.ofNat 2)
      terms.length 0 terms)
    (f : Cminor.Function) (result : Ident) (k : Cminor.Cont)
    (sp : Val) (le : Cminor.Env) :
    ∃ targetMemory',
      Cminor.Steps (Cminor.Imported.program applicationOrder).globalenv
        (.Running f (callerIntegratorCall result terms.length) k sp le targetMemory)
        E0 (.Running f .Sskip k sp
          (le.set result
            (.Vfloat (Binary64.integrate (Binary64.testfun Binary64.Polynomial.cosine) terms)))
          targetMemory') ∧
      BlocksAgree globalBlockMap sourceMemory targetMemory' ∧
      targetMemory'.nextblock.toNat =
        targetMemory.nextblock.toNat + (4 * terms.length + 1) := by
  obtain ⟨m', hrun, hm', hnext⟩ := integrator_target_execution applicationOrder hm terms hn
    cells (.Kcall (some result) f sp le k)
  refine ⟨m', ?_, hm', hnext⟩
  refine Cminor.Steps.cons (.call _ _ _ _ _ _ _ _ _
    (.Vptr (Positive.ofNat 70) Integers.Ptrofs.zero)
    [.Vptr (Positive.ofNat 71) Integers.Ptrofs.zero, .Vint (Integers.Int.repr terms.length)]
    (.Internal integratorTarget) ?_ ?_ ?_ rfl) ?_
  · apply Cminor.eval_expr_sound
    simp only [Cminor.evalExpr, Cminor.evalConstant, Genv.symbolAddress,
      (integrator_global_symbols applicationOrder).2]
  · apply Cminor.eval_expr_list_sound
    simp only [Cminor.evalExprList, Cminor.evalExpr, Cminor.evalConstant, Genv.symbolAddress,
      (caller_callback_symbols applicationOrder).2, bind, Option.bind_some]
    rfl
  · rw [find_function_at_zero_offset]
    exact integrator_target_lookup applicationOrder
  · exact Cminor.steps_trans hrun (Cminor.steps_single (.return_to_caller ..))

/-- The target wrapper composes the two-point integrator and frees its own frame. -/
theorem wrapper_target_execution [ExternalCalls] (applicationOrder : Nat)
    {sourceMemory targetMemory : Mem}
    (hm : BlocksAgree globalBlockMap sourceMemory targetMemory)
    (terms : List (Binary64.Value × Binary64.Value)) (hlen : terms.length = 2)
    (cells : TableCells sourceMemory (Positive.ofNat 1) (Positive.ofNat 2) 2 0 terms)
    (k : Cminor.Cont) :
    ∃ targetMemory',
      Cminor.Steps (Cminor.Imported.program applicationOrder).globalenv
        (.Callstate (.Internal wrapperTarget) [] k targetMemory)
        E0 (.Returnstate
          (.Vfloat (Binary64.integrate (Binary64.testfun Binary64.Polynomial.cosine) terms))
          (Cminor.callCont k) targetMemory') ∧
      BlocksAgree globalBlockMap sourceMemory targetMemory' ∧
      targetMemory'.nextblock.toNat = targetMemory.nextblock.toNat + 10 := by
  let sp : Val := .Vptr targetMemory.nextblock Integers.Ptrofs.zero
  let le := Cminor.setLocals wrapperTarget.fn_vars
    (Cminor.setParams [] wrapperTarget.fn_params)
  obtain ⟨m', hrun, hm', hnext⟩ := caller_integrator_execution applicationOrder
    (hm.alloc_target 0 0) terms (by omega) (by simpa only [hlen] using cells)
    wrapperTarget (Positive.ofNat 128) (.Kseq wrapperReturn k) sp le
  rw [hlen] at hrun
  have hfree := Mem.free_isSome (Mem.rangePerm_intro m' targetMemory.nextblock
    0 0 .Cur .Freeable (fun ofs hlo hhi => by omega))
  refine ⟨_, ?_, hm'.free_target hfree (fun _ hb => hm.target_ne_nextblock hb rfl), ?_⟩
  · have hentry : Cminor.Step (Cminor.Imported.program applicationOrder).globalenv
        (.Callstate (.Internal wrapperTarget) [] k targetMemory) E0
        (.Running wrapperTarget wrapperTarget.fn_body k sp le (Mem.alloc targetMemory 0 0).1) :=
      .internal_function _ _ _ _ _ _ _ .nil rfl rfl
    rw [wrapper_target_body] at hentry
    refine Cminor.Steps.cons hentry (Cminor.Steps.cons (.seq ..) ?_)
    refine Cminor.steps_trans hrun (Cminor.Steps.cons (.skip_seq ..) ?_)
    exact Cminor.steps_single (.return_some _ _ _ _ _ _ _ _
      (Cminor.eval_expr_sound (by simp [Cminor.evalExpr, PTree.gss])) hfree)
  · change m'.nextblock.toNat = targetMemory.nextblock.toNat + 10
    change m'.nextblock.toNat =
      targetMemory.nextblock.succ.toNat + (4 * terms.length + 1) at hnext
    rw [Positive.toNat_succ, hlen] at hnext
    omega

private def wrapperSourceReturn : CC.Stmt :=
  .Sreturn (some (.Etempvar _t'1 tdouble))

private def wrapperSourceTemps : TempEnv := createUndefTemps [(_t'1, tdouble)]

private def wrapperSourceContinuation (k : Cont) : Cont :=
  .Kcall (some _t'1) f_integrate_testfun emptyEnv wrapperSourceTemps
    (.Kseq wrapperSourceReturn k)

/-- The source wrapper calls the same two-point integrator and returns its value unchanged. -/
theorem wrapper_source_execution [ExternalCalls] (applicationOrder : Nat) (m : Mem)
    (terms : List (Binary64.Value × Binary64.Value)) (hlen : terms.length = 2)
    (cells : TableCells m (Positive.ofNat 1) (Positive.ofNat 2) 2 0 terms) (k : Cont) :
    StarE0 (Step2 (Application.program applicationOrder).globalenv)
      (.Callstate (.Internal f_integrate_testfun) [] k m)
      (.Returnstate
        (.Vfloat (Binary64.integrate (Binary64.testfun Binary64.Polynomial.cosine) terms))
        (callCont k) m) := by
  have hrun := integrator_source_execution applicationOrder m terms (by omega)
    (by simpa only [hlen] using cells) (wrapperSourceContinuation k)
  rw [hlen] at hrun
  apply starE0_trans (b := storedLibraryCall
    (.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero) 2 (wrapperSourceContinuation k) m)
  · refine .step _ _ _ (doStep_sound _ _ _ _ (by rfl)) ?_
    refine .step _ _ _ (doStep_sound _ _ _ _ (by rfl)) ?_
    exact .step _ _ _ (doStep_sound _ _ _ _ (by rfl)) (.refl _)
  · apply starE0_trans hrun
    refine .step _ _ _ (doStep_sound _ _ _ _ (by rfl)) ?_
    refine .step _ _ _ (doStep_sound _ _ _ _ (by rfl)) ?_
    exact .step _ _ _ (doStep_sound _ _ _ _ (by rfl)) (.refl _)

/-- From related memories `hm`, both two-point wrappers return the same value and the memories
stay related. -/
theorem wrapper_call_correspondence [ExternalCalls] (applicationOrder : Nat)
    {sourceMemory targetMemory : Mem}
    (hm : BlocksAgree globalBlockMap sourceMemory targetMemory)
    (terms : List (Binary64.Value × Binary64.Value)) (hlen : terms.length = 2)
    (cells : TableCells sourceMemory (Positive.ofNat 1) (Positive.ofNat 2) 2 0 terms)
    (sourceCont : Cont) (targetCont : Cminor.Cont) :
    ∃ targetMemory',
      StarE0 (Step2 (Application.program applicationOrder).globalenv)
        (.Callstate (.Internal f_integrate_testfun) [] sourceCont sourceMemory)
        (.Returnstate
          (.Vfloat (Binary64.integrate (Binary64.testfun Binary64.Polynomial.cosine) terms))
          (callCont sourceCont) sourceMemory) ∧
      Cminor.Steps (Cminor.Imported.program applicationOrder).globalenv
        (.Callstate (.Internal wrapperTarget) [] targetCont targetMemory)
        E0 (.Returnstate
          (.Vfloat (Binary64.integrate (Binary64.testfun Binary64.Polynomial.cosine) terms))
          (Cminor.callCont targetCont) targetMemory') ∧
      BlocksAgree globalBlockMap sourceMemory targetMemory' ∧
      targetMemory'.nextblock.toNat = targetMemory.nextblock.toNat + 10 := by
  obtain ⟨m', htarget, hm', hnext⟩ :=
    wrapper_target_execution applicationOrder hm terms hlen cells targetCont
  exact ⟨m', wrapper_source_execution applicationOrder _ terms hlen cells sourceCont,
    htarget, hm', hnext⟩

/-- The imported main records the integrator's value, returns zero, and frees its frame. -/
theorem main_target_execution [ExternalCalls]
    {sourceMemory targetMemory : Mem}
    (hm : BlocksAgree globalBlockMap sourceMemory targetMemory)
    (terms : List (Binary64.Value × Binary64.Value)) (hn : terms.length ≤ 10)
    (cells : TableCells sourceMemory (Positive.ofNat 1) (Positive.ofNat 2)
      terms.length 0 terms) (k : Cminor.Cont) :
    ∃ targetMemory',
      Cminor.Steps (Cminor.Imported.program terms.length).globalenv
        (.Callstate (.Internal (mainTarget terms.length)) [] k targetMemory)
        (Application.resultTrace
          (Binary64.integrate (Binary64.testfun Binary64.Polynomial.cosine) terms))
        (.Returnstate (.Vint Integers.Int.zero) (Cminor.callCont k) targetMemory') ∧
      BlocksAgree globalBlockMap sourceMemory targetMemory' ∧
      targetMemory'.nextblock.toNat =
        targetMemory.nextblock.toNat + (4 * terms.length + 2) := by
  let sp : Val := .Vptr targetMemory.nextblock Integers.Ptrofs.zero
  let le := Cminor.setLocals (mainTarget terms.length).fn_vars
    (Cminor.setParams [] (mainTarget terms.length).fn_params)
  obtain ⟨m', hrun, hm', hnext⟩ := caller_integrator_execution terms.length
    (hm.alloc_target 0 0) terms hn cells (mainTarget terms.length) Application.resultTemp
    (.Kseq (.Sseq mainObservation mainExit) k) sp le
  have hfree := Mem.free_isSome (Mem.rangePerm_intro m' targetMemory.nextblock
    0 0 .Cur .Freeable (fun ofs hlo hhi => by omega))
  refine ⟨_, ?_, hm'.free_target hfree (fun _ hb => hm.target_ne_nextblock hb rfl), ?_⟩
  · have hentry : Cminor.Step (Cminor.Imported.program terms.length).globalenv
        (.Callstate (.Internal (mainTarget terms.length)) [] k targetMemory) E0
        (.Running (mainTarget terms.length) (mainTarget terms.length).fn_body k sp le
          (Mem.alloc targetMemory 0 0).1) :=
      .internal_function _ _ _ _ _ _ _ .nil rfl rfl
    rw [main_target_body] at hentry
    refine Cminor.Steps.cons hentry (Cminor.Steps.cons (.seq ..) ?_)
    refine Cminor.steps_trans hrun (Cminor.Steps.cons (.skip_seq ..) ?_)
    refine Cminor.Steps.cons (.seq ..) ?_
    refine Cminor.Steps.cons (first := Application.resultTrace
      (Binary64.integrate (Binary64.testfun Binary64.Polynomial.cosine) terms))
      (rest := E0) (.builtin _ _ _ _ _ _ _ _
      [.Vfloat (Binary64.integrate (Binary64.testfun Binary64.Polynomial.cosine) terms)]
      _ .Vundef m' ?_ ?_) ?_
    · exact Cminor.eval_expr_list_sound (by
        simp [Cminor.evalExprList, Cminor.evalExpr, PTree.gss])
    · exact ExtcallAnnotSem.intro _ _ _ _
        (.evl_match_cons _ _ _ _ _ _ (.ev_match_float _) .evl_match_nil)
    · refine Cminor.Steps.cons (.skip_seq ..) ?_
      exact Cminor.steps_single (.return_some _ _ _ _ _ _ _ _
        (Cminor.eval_expr_sound (by rfl)) hfree)
  · change m'.nextblock.toNat = targetMemory.nextblock.toNat + (4 * terms.length + 2)
    change m'.nextblock.toNat =
      targetMemory.nextblock.succ.toNat + (4 * terms.length + 1) at hnext
    rw [Positive.toNat_succ] at hnext
    omega

private def mainSourceObservation : CC.Stmt :=
  .Sbuiltin none (.EF_annot (Positive.ofNat 1) "quadrature-result" [.Tfloat]) [tdouble]
    [.Etempvar Application.resultTemp tdouble]

private def mainSourceExit : CC.Stmt :=
  .Sreturn (some (.Econst_int Integers.Int.zero tint))

private def mainSourceTemps : TempEnv := createUndefTemps [(Application.resultTemp, tdouble)]

private def mainSourceContinuation (n : Nat) (k : Cont) : Cont :=
  .Kcall (some Application.resultTemp) (Application.mainFunction n) emptyEnv mainSourceTemps
    (.Kseq (.Ssequence mainSourceObservation mainSourceExit) k)

/-- The Clight `main` emits the annotation of the fold and returns zero, from table cells
`cells`. -/
theorem main_source_execution [ExternalCalls] (m : Mem)
    (terms : List (Binary64.Value × Binary64.Value)) (hn : terms.length ≤ 10)
    (cells : TableCells m (Positive.ofNat 1) (Positive.ofNat 2) terms.length 0 terms)
    (k : Cont) :
    Star (Step2 (Application.program terms.length).globalenv)
      (.Callstate (.Internal (Application.mainFunction terms.length)) [] k m)
      (Application.resultTrace
        (Binary64.integrate (Binary64.testfun Binary64.Polynomial.cosine) terms))
      (.Returnstate (.Vint Integers.Int.zero) (callCont k) m) := by
  let value := Binary64.integrate (Binary64.testfun Binary64.Polynomial.cosine) terms
  let observed := State.State (Application.mainFunction terms.length) mainSourceObservation
    (.Kseq mainSourceExit k) emptyEnv
    (mainSourceTemps.set Application.resultTemp (.Vfloat value)) m
  have hbefore : StarE0 (Step2 (Application.program terms.length).globalenv)
      (.Callstate (.Internal (Application.mainFunction terms.length)) [] k m) observed := by
    apply starE0_trans (b := storedLibraryCall
      (.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero) terms.length
      (mainSourceContinuation terms.length k) m)
    · refine .step _ _ _ (doStep_sound _ _ _ _ (by rfl)) ?_
      refine .step _ _ _ (doStep_sound _ _ _ _ (by rfl)) ?_
      exact .step _ _ _ (doStep_sound _ _ _ _ (by rfl)) (.refl _)
    · apply starE0_trans (integrator_source_execution terms.length m terms hn cells
        (mainSourceContinuation terms.length k))
      refine .step _ _ _ (doStep_sound _ _ _ _ (by rfl)) ?_
      refine .step _ _ _ (doStep_sound _ _ _ _ (by rfl)) ?_
      exact .step _ _ _ (doStep_sound _ _ _ _ (by rfl)) (.refl _)
  apply star_trans (star_of_starE0 hbefore)
  refine .step _ (Application.resultTrace value)
    (.State (Application.mainFunction terms.length) .Sskip (.Kseq mainSourceExit k) emptyEnv
      (mainSourceTemps.set Application.resultTemp (.Vfloat value)) m)
    E0 _ _ ?_ ?_ (by rfl)
  · apply CC.Step.builtin (vargs := [.Vfloat value])
    · exact doEvalExprlist_sound _ _ _ _ _ _ _ (by rfl)
    · exact ExtcallAnnotSem.intro _ _ _ _
        (.evl_match_cons _ _ _ _ _ _ (.ev_match_float value) .evl_match_nil)
  · apply star_of_starE0
    refine .step _ _ _ (doStep_sound _ _ _ _ (by rfl)) ?_
    exact .step _ _ _ (doStep_sound _ _ _ _ (by rfl)) (.refl _)

/-- Caller execution preserves the observation and exit status across the two semantics. -/
theorem main_call_correspondence [ExternalCalls]
    {sourceMemory targetMemory : Mem}
    (hm : BlocksAgree globalBlockMap sourceMemory targetMemory)
    (terms : List (Binary64.Value × Binary64.Value)) (hn : terms.length ≤ 10)
    (cells : TableCells sourceMemory (Positive.ofNat 1) (Positive.ofNat 2)
      terms.length 0 terms) (sourceCont : Cont) (targetCont : Cminor.Cont) :
    ∃ targetMemory',
      Star (Step2 (Application.program terms.length).globalenv)
        (.Callstate (.Internal (Application.mainFunction terms.length)) [] sourceCont sourceMemory)
        (Application.resultTrace
          (Binary64.integrate (Binary64.testfun Binary64.Polynomial.cosine) terms))
        (.Returnstate (.Vint Integers.Int.zero) (callCont sourceCont) sourceMemory) ∧
      Cminor.Steps (Cminor.Imported.program terms.length).globalenv
        (.Callstate (.Internal (mainTarget terms.length)) [] targetCont targetMemory)
        (Application.resultTrace
          (Binary64.integrate (Binary64.testfun Binary64.Polynomial.cosine) terms))
        (.Returnstate (.Vint Integers.Int.zero) (Cminor.callCont targetCont) targetMemory') ∧
      BlocksAgree globalBlockMap sourceMemory targetMemory' ∧
      targetMemory'.nextblock.toNat =
        targetMemory.nextblock.toNat + (4 * terms.length + 2) := by
  obtain ⟨m', htarget, hm', hnext⟩ := main_target_execution hm terms hn cells targetCont
  exact ⟨m', main_source_execution _ terms hn cells sourceCont, htarget, hm', hnext⟩

-- Kernel unfolding of the Clight global environment at block 7.
set_option maxRecDepth 10000 in
/-- Source block 7 holds the Clight wrapper in every application program. -/
theorem wrapper_source_lookup (n : Nat) :
    Genv.findFunctPtr (Application.program n).globalenv.genv_genv (Positive.ofNat 7) =
      some (.Internal f_integrate_testfun) := rfl

-- Kernel evaluation of the imported global environment at block 72.
set_option maxRecDepth 100000 in
/-- Target block 72 holds the imported wrapper in every imported program. -/
theorem wrapper_target_lookup (n : Nat) :
    Genv.findFunctPtr (Cminor.Imported.program n).globalenv (Positive.ofNat 72) =
      some (.Internal wrapperTarget) := by
  let globalsPrefix := (Cminor.Imported.program 0).prog_defs.take 72
  change Genv.findFunctPtr
    (Genv.addGlobals (Genv.emptyGenv (Cminor.Imported.program 0).prog_public)
      (globalsPrefix ++ [Cminor.Imported.mainDefinition n])) (Positive.ofNat 72) = _
  rw [find_function_before_last_global _ _ _ _ (by decide +kernel)]
  decide +kernel

-- Kernel evaluation of the wrapper symbol in both symbol tables.
set_option maxRecDepth 10000 in
/-- Both symbol environments resolve the wrapper symbol to its block in every program. -/
theorem wrapper_global_symbols (n : Nat) :
    Genv.findSymbol (Application.program n).globalenv.genv_genv _integrate_testfun =
      some (Positive.ofNat 7) ∧
    Genv.findSymbol (Cminor.Imported.program n).globalenv
      (Positive.ofNat 6930287380122293369677211620818) = some (Positive.ofNat 72) :=
  shared_global_symbols n (id := _integrate_testfun) (b := Positive.ofNat 7)
    (by decide +kernel)

-- Kernel evaluation of the main symbol in both symbol tables.
set_option maxRecDepth 10000 in
/-- Both symbol environments resolve the `main` symbol to its block in every program. -/
theorem main_global_symbols (n : Nat) :
    Genv.findSymbol (Application.program n).globalenv.genv_genv Application.mainIdent =
      some (Positive.ofNat 9) ∧
    Genv.findSymbol (Cminor.Imported.program n).globalenv (Positive.ofNat 22880918) =
      some (Positive.ofNat 73) :=
  shared_global_symbols n (id := Application.mainIdent) (b := Positive.ofNat 9)
    (by decide +kernel)

private theorem caller_target_definitions (n : Nat) :
    (Cminor.Imported.program n).prog_defs =
      (Cminor.Imported.program 0).prog_defs.take 72 ++
        [(Positive.ofNat 22880918, .Gfun (.Internal (mainTarget n)))] := rfl

private theorem find_function_last_global {F V : Type} (ge : Genv F V)
    (globals : List (Ident × GlobDef F V)) (id : Ident) (f : F) (b : Block)
    (hnext : (Genv.addGlobals ge globals).genv_next = b) :
    Genv.findFunctPtr (Genv.addGlobals ge (globals ++ [(id, .Gfun f)])) b = some f := by
  change (globals.foldl Genv.addGlobal ge).genv_next = b at hnext
  simp only [Genv.addGlobals, List.foldl_append, List.foldl_cons, List.foldl_nil,
    Genv.findFunctPtr, Genv.findDef, Genv.addGlobal, hnext, PTree.gss]

-- Kernel evaluation of the next block after the 72 shared globals of the imported program.
set_option maxRecDepth 100000 in
/-- Target block 73 holds `mainTarget n` in the n-node imported program. -/
theorem main_target_lookup (n : Nat) :
    Genv.findFunctPtr (Cminor.Imported.program n).globalenv (Positive.ofNat 73) =
      some (.Internal (mainTarget n)) := by
  unfold Cminor.Program.globalenv
  rw [caller_target_definitions]
  apply find_function_last_global
  change (Genv.addGlobals (Genv.emptyGenv (Cminor.Imported.program 0).prog_public)
    ((Cminor.Imported.program 0).prog_defs.take 72)).genv_next = Positive.ofNat 73
  decide +kernel

/-- The target start state is obtained from its own initialized program and entry symbol. -/
def mainTargetInitial (n : Nat) : Cminor.State :=
  .Callstate (.Internal (mainTarget n)) [] .Kstop cminorEntryMemory

/-- `mainTargetInitial n` is the initial state of the n-node imported program. -/
theorem main_target_initial (n : Nat) :
    Cminor.InitialState (Cminor.Imported.program n) (mainTargetInitial n) :=
  .intro (Positive.ofNat 73) _ _ (cminor_program_initialized n) (main_global_symbols n).2
    (main_target_lookup n) rfl

/-- Initialization discharges every table condition for both complete application executions. -/
theorem initialized_main_correspondence [ExternalCalls] (n : Nat) (hn : n ≤ 10) :
    ∃ targetMemory',
      InitialState (Application.program n) (Application.initialState n) ∧
      Cminor.InitialState (Cminor.Imported.program n) (mainTargetInitial n) ∧
      Star (Step2 (Application.program n).globalenv) (Application.initialState n)
        (Application.resultTrace (StoredPolynomial.result n))
        (.Returnstate (.Vint Integers.Int.zero) .Kstop Application.entryMemory) ∧
      Cminor.Steps (Cminor.Imported.program n).globalenv (mainTargetInitial n)
        (Application.resultTrace (StoredPolynomial.result n))
        (.Returnstate (.Vint Integers.Int.zero) .Kstop targetMemory') ∧
      BlocksAgree globalBlockMap Application.entryMemory targetMemory' ∧
      targetMemory'.nextblock.toNat = cminorEntryMemory.nextblock.toNat + (4 * n + 2) := by
  have hlength := stored_terms_length n hn
  have hbound : (storedTerms n).length ≤ 10 := by rw [hlength]; exact hn
  have hcells : TableCells Application.entryMemory (Positive.ofNat 1) (Positive.ofNat 2)
      (storedTerms n).length 0 (storedTerms n) := by
    rw [hlength]
    exact Application.table_cells n hn
  obtain ⟨m', hsource, htarget, hm', hnext⟩ :=
    main_call_correspondence initialized_globals_agree (storedTerms n) hbound hcells .Kstop .Kstop
  rw [hlength] at hsource htarget hnext
  exact ⟨m', Application.initial_state n, main_target_initial n, hsource, htarget, hm', hnext⟩

/-- The original wrapper's two-node table conditions follow from initialization. -/
theorem initialized_wrapper_correspondence [ExternalCalls] (applicationOrder : Nat)
    (sourceCont : Cont) (targetCont : Cminor.Cont) :
    ∃ targetMemory',
      StarE0 (Step2 (Application.program applicationOrder).globalenv)
        (.Callstate (.Internal f_integrate_testfun) [] sourceCont Application.entryMemory)
        (.Returnstate (.Vfloat (StoredPolynomial.result 2))
          (callCont sourceCont) Application.entryMemory) ∧
      Cminor.Steps (Cminor.Imported.program applicationOrder).globalenv
        (.Callstate (.Internal wrapperTarget) [] targetCont cminorEntryMemory)
        E0 (.Returnstate (.Vfloat (StoredPolynomial.result 2))
          (Cminor.callCont targetCont) targetMemory') ∧
      BlocksAgree globalBlockMap Application.entryMemory targetMemory' ∧
      targetMemory'.nextblock.toNat = cminorEntryMemory.nextblock.toNat + 10 :=
  wrapper_call_correspondence applicationOrder initialized_globals_agree (storedTerms 2)
    (stored_terms_length 2 (by decide)) (Application.table_cells 2 (by decide))
    sourceCont targetCont

/-- Every completed source wrapper call has a target run with the same trace and value. -/
theorem wrapper_return_preserved [calls : ExternalCalls] [ExternalCallsDeterministic calls]
    (applicationOrder : Nat) {sourceMemory targetMemory returnedMemory : Mem}
    (hm : BlocksAgree globalBlockMap sourceMemory targetMemory)
    (terms : List (Binary64.Value × Binary64.Value)) (hlen : terms.length = 2)
    (cells : TableCells sourceMemory (Positive.ofNat 1) (Positive.ofNat 2) 2 0 terms)
    {value : Val} {trace : Trace}
    (hsource : Star (Step2 (Application.program applicationOrder).globalenv)
      (.Callstate (.Internal f_integrate_testfun) [] .Kstop sourceMemory) trace
      (.Returnstate value .Kstop returnedMemory)) :
    ∃ targetMemory',
      Cminor.Steps (Cminor.Imported.program applicationOrder).globalenv
        (.Callstate (.Internal wrapperTarget) [] .Kstop targetMemory)
        trace (.Returnstate value .Kstop targetMemory') ∧
      BlocksAgree globalBlockMap returnedMemory targetMemory' := by
  obtain ⟨htrace, hremaining⟩ := silent_execution_prefix (Application.program applicationOrder)
    (wrapper_source_execution applicationOrder sourceMemory terms hlen cells .Kstop)
    (return_stop_no_step _ _ _) hsource
  have heq := starE0_of_stuck hremaining (return_stop_no_step _ _ _)
  rcases State.Returnstate.inj heq with ⟨rfl, _, rfl⟩
  subst trace
  obtain ⟨m', htarget, hm', _⟩ :=
    wrapper_target_execution applicationOrder hm terms hlen cells .Kstop
  exact ⟨m', htarget, hm'⟩

/-- Any completed initialized source application is matched by the composed target execution. -/
theorem main_return_preserved [calls : ExternalCalls] [ExternalCallsDeterministic calls]
    (n : Nat) (hn : n ≤ 10) {start : CC.State} {trace : Trace} {value : Val} {memory : Mem}
    (hinit : InitialState (Application.program n) start)
    (hsource : Star (Step2 (Application.program n).globalenv) start trace
      (.Returnstate value .Kstop memory)) :
    ∃ targetMemory,
      Cminor.InitialState (Cminor.Imported.program n) (mainTargetInitial n) ∧
      Cminor.Steps (Cminor.Imported.program n).globalenv (mainTargetInitial n)
        trace (.Returnstate value .Kstop targetMemory) ∧
      BlocksAgree globalBlockMap memory targetMemory := by
  obtain ⟨htrace, hvalue, hmemory⟩ := Application.return_specification n hn start trace value memory
    hinit hsource
  obtain ⟨m', _, htargetInit, _, htarget, hm', _⟩ := initialized_main_correspondence n hn
  refine ⟨m', htargetInit, ?_, ?_⟩
  · simpa only [htrace, hvalue] using htarget
  · rw [hmemory]
    exact hm'

/-- For n = 1..10, the Clight and Cminor programs have the same observations (event trace, exit
status), under `ExternalCallsDeterministic`. -/
theorem main_final_observations_iff [calls : ExternalCalls] [ExternalCallsDeterministic calls]
    (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) (trace : Trace) (status : Integers.Int) :
    (∃ start memory, InitialState (Application.program n) start ∧
      Star (Step2 (Application.program n).globalenv) start trace
        (.Returnstate (.Vint status) .Kstop memory)) ↔
    (∃ start finish, Cminor.InitialState (Cminor.Imported.program n) start ∧
      Cminor.Steps (Cminor.Imported.program n).globalenv start trace finish ∧
      Cminor.FinalState finish status) := by
  constructor
  · rintro ⟨start, memory, hinit, hrun⟩
    obtain ⟨m', htargetInit, htarget, _⟩ := main_return_preserved n hhi hinit hrun
    exact ⟨mainTargetInitial n, _, htargetInit, htarget, .intro status m'⟩
  · rintro ⟨start, finish, hinit, hrun, hfinal⟩
    obtain ⟨htrace, hstatus⟩ := Cminor.StoredPrograms.maximal_execution n hlo hhi hinit hrun
      (fun _ _ => Cminor.final_state_stuck hfinal)
    have hzero := Cminor.final_state_unique hfinal hstatus
    refine ⟨Application.initialState n, Application.entryMemory, Application.initial_state n, ?_⟩
    simpa only [htrace, hzero, Application.resultTrace, Cminor.StoredPrograms.resultTrace]
      using Application.execution n hhi

end Quadrature.Compiler
