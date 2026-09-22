import Quadrature.Compiler.Correspondence.PolynomialFunction

/-!
# Correspondence for the integrand's nested polynomial call

Relates the Clight and Cminor callbacks (the integrand `testfun`) for the ten programs, by
`LocalsAgree` under the renaming `callbackRename` and `BlocksAgree` on memory. Read
`callback_call_correspondence` first: both callbacks call the internal polynomial, resume
their saved environments, evaluate the remaining rounded arithmetic, and return the same
value for every binary64 input. The target allocates two zero-size frames over the nested
call and frees both. `callback_return_preserved` matches any completed standalone source
call under `ExternalCallsDeterministic`.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Compiler

open CC
open Binary64.Clight
open Binary64.ClightSource

/-- Installing a return value preserves related locals, including discarded results. -/
theorem LocalsAgree.set_result {mapping : BlockMap} {rename : Ident → Ident}
    {source : TempEnv} {target : Cminor.Env}
    (h : LocalsAgree mapping rename source target) (hinj : Function.Injective rename)
    (result : Option Ident) {value value' : Val} (hv : ValuesAgree mapping value value') :
    LocalsAgree mapping rename (setOpttemp result value source)
      (Cminor.setOptvar (result.map rename) value' target) := by
  cases result with
  | none => exact h
  | some id => exact h.set hinj id hv

/-- The imported callback, compiler global 70 at memory block 71. -/
def callbackTarget : Cminor.Function :=
  match h : Cminor.Imported.global70.2 with
  | .Gfun (.Internal f) => f
  | .Gfun (.External _) => False.elim (by cases h)
  | .Gvar _ => False.elim (by cases h)

/-- The target identifier of the callback's parameter `x`. -/
def callbackArgument : Ident := Positive.ofNat 97
/-- The target identifier receiving the polynomial's result. -/
def callbackResult : Ident := Positive.ofNat 128

/-- The renaming of the callback's parameter. The result temporary is fixed. -/
def callbackRename : Ident ≃ Ident := Equiv.swap _x callbackArgument

/-- The renaming sends the source parameter `_x` to `callbackArgument`. -/
theorem callback_rename_argument : callbackRename _x = callbackArgument :=
  Equiv.swap_apply_left _ _

/-- The renaming sends the source temporary `_t'1` to `callbackResult`. -/
theorem callback_rename_result : callbackRename _t'1 = callbackResult := by
  decide +kernel

/-- The Clight callback's temporaries at entry with argument `x`. -/
def callbackSourceLocals (x : Binary64.Value) : TempEnv :=
  ((PTree.empty : TempEnv).set _t'1 .Vundef).set _x (.Vfloat x)

/-- The Cminor callback's variables at entry with argument `x`. -/
def callbackTargetLocals (x : Binary64.Value) : Cminor.Env :=
  ((PTree.empty : Cminor.Env).set callbackResult .Vundef).set callbackArgument (.Vfloat x)

/-- The entry environments agree under `callbackRename`. -/
theorem callback_locals_agree (mapping : BlockMap) (x : Binary64.Value) :
    LocalsAgree mapping callbackRename (callbackSourceLocals x) (callbackTargetLocals x) := by
  have h := ((LocalsAgree.empty mapping callbackRename).set
    callbackRename.injective _t'1 .undef).set callbackRename.injective _x (.float x)
  simpa only [callbackSourceLocals, callbackTargetLocals,
    callback_rename_argument, callback_rename_result] using h

/-- The imported return expression, keeping the signed-integer conversion in `1 - x`. -/
def callbackReturn : Cminor.Expr :=
  .Ebinop .Omulf
    (.Ebinop .Omulf (.Econst (.Ofloatconst Binary64.half))
      (.Ebinop .Osubf (.Eunop .Ofloatofint (.Econst (.Ointconst (Integers.Int.repr 1))))
        (.Evar callbackArgument)))
    (.Evar callbackResult)

/-- Global 70 of the imported program is `callbackTarget`. -/
theorem callback_target_definition :
    Cminor.Imported.global70.2 = .Gfun (.Internal callbackTarget) := rfl

/-- The imported body calls the polynomial symbol and returns `callbackReturn`. -/
theorem callback_target_body :
    callbackTarget.fn_body =
      .Sseq (.Scall (some callbackResult) (mksignature [.Xfloat] .Xfloat cc_default)
        (.Econst (.Oaddrsymbol (Positive.ofNat 378380) Integers.Ptrofs.zero))
        [.Evar callbackArgument])
        (.Sreturn (some callbackReturn)) := rfl

/-- The imported callback takes and returns one float. -/
theorem callback_target_signature :
    callbackTarget.fn_sig = mksignature [.Xfloat] .Xfloat cc_default := rfl

/-- The imported callback has a zero-size stack frame. -/
theorem callback_target_stackspace : callbackTarget.fn_stackspace = 0 := rfl

/-- Entering the imported callback with argument `x` binds exactly `callbackTargetLocals x`. -/
theorem callback_entry_locals (x : Binary64.Value) :
    Cminor.setLocals callbackTarget.fn_vars
      (Cminor.setParams [.Vfloat x] callbackTarget.fn_params) = callbackTargetLocals x := rfl

/-- The Clight callback's first step enters its body with `callbackSourceLocals x`. -/
theorem callback_source_entry [ExternalCalls]
    (ge : CGenv) (m : Mem) (x : Binary64.Value) (k : Cont) :
    Step2 ge (.Callstate (.Internal f_testfun) [.Vfloat x] k m) E0
      (.State f_testfun f_testfun.fn_body k emptyEnv (callbackSourceLocals x) m) :=
  doStep_sound _ _ _ _ (by rfl)

/-- Each operation, including the conversion of integer one, agrees with the model. -/
theorem callback_target_return_eval (ge : Cminor.Genv) (stack : Val)
    (le : Cminor.Env) (m : Mem) (cosine : Binary64.Value → Binary64.Value)
    (x : Binary64.Value)
    (hx : le.get callbackArgument = some (.Vfloat x))
    (hy : le.get callbackResult = some (.Vfloat (cosine x))) :
    Cminor.evalExpr ge stack le m callbackReturn =
      some (.Vfloat (Binary64.testfun cosine x)) := by
  simp only [callbackReturn, Cminor.evalExpr, hx, hy, bind, Option.bind_some]
  rfl

/-- The saved callback environments remain related after installing the polynomial result. -/
theorem callback_return_locals_agree (mapping : BlockMap) (x y : Binary64.Value) :
    LocalsAgree mapping callbackRename
      (setOpttemp (some _t'1) (.Vfloat y) (callbackSourceLocals x))
      (Cminor.setOptvar (some callbackResult) (.Vfloat y) (callbackTargetLocals x)) := by
  simpa only [Option.map_some, callback_rename_result] using
    (callback_locals_agree mapping x).set_result callbackRename.injective
      (some _t'1) (.float y)

-- Elaboration of the imported callback's step derivation at increased recursion depth.
set_option maxRecDepth 20000 in
/-- Execute the nested call and resume the callback, preserving mapped memory. -/
theorem callback_target_execution [ExternalCalls]
    (sourceGe : CGenv) (targetGe : Cminor.Genv)
    (cosBlock : Block)
    (hsymbol : Genv.findSymbol targetGe (Positive.ofNat 378380) = some cosBlock)
    (hfunction : Genv.findFunct targetGe (.Vptr cosBlock Integers.Ptrofs.zero) =
      some (.Internal polynomialTarget))
    {mapping : BlockMap} {sourceMemory targetMemory : Mem}
    (hm : BlocksAgree mapping sourceMemory targetMemory)
    (x : Binary64.Value) (k : Cminor.Cont) :
    ∃ targetMemory',
      Cminor.Steps targetGe
        (.Callstate (.Internal callbackTarget) [.Vfloat x] k targetMemory)
        E0 (.Returnstate (.Vfloat (Binary64.testfun Binary64.Polynomial.cosine x))
          (Cminor.callCont k) targetMemory') ∧
      BlocksAgree mapping sourceMemory targetMemory' ∧
      targetMemory'.nextblock = targetMemory.nextblock.succ.succ := by
  let sp : Val := .Vptr targetMemory.nextblock Integers.Ptrofs.zero
  let le := callbackTargetLocals x
  let rest := Cminor.Stmt.Sreturn (some callbackReturn)
  let frame := Cminor.Cont.Kcall (some callbackResult) callbackTarget sp le (.Kseq rest k)
  obtain ⟨calleeMemory, hcallee, hrelated, hnext⟩ := polynomial_target_execution
    sourceGe targetGe (hm.alloc_target 0 0) x frame
  have heval := callback_target_return_eval targetGe sp
    (Cminor.setOptvar (some callbackResult) (.Vfloat (Binary64.Polynomial.cosine x)) le)
    calleeMemory Binary64.Polynomial.cosine x (by rfl) (by rfl)
  have hfree := Mem.free_isSome (Mem.rangePerm_intro calleeMemory
    targetMemory.nextblock 0 0 .Cur .Freeable (fun ofs hlo hhi => by omega))
  refine ⟨_, ?_, hrelated.free_target hfree (fun _ hb => hm.target_ne_nextblock hb rfl), ?_⟩
  · have hentry : Cminor.Step targetGe
        (.Callstate (.Internal callbackTarget) [.Vfloat x] k targetMemory) E0
        (.Running callbackTarget callbackTarget.fn_body k sp le
          (Mem.alloc targetMemory 0 0).1) :=
      .internal_function _ _ _ _ _ _ _ (.cons trivial .nil) rfl (callback_entry_locals x)
    rw [callback_target_body] at hentry
    refine Cminor.Steps.cons hentry (Cminor.Steps.cons (.seq ..) ?_)
    refine Cminor.Steps.cons (.call _ _ _ _ _ _ _ _ _
      (.Vptr cosBlock Integers.Ptrofs.zero) [.Vfloat x] (.Internal polynomialTarget)
      ?_ ?_ hfunction rfl) ?_
    · apply Cminor.eval_expr_sound
      simp only [Cminor.evalExpr, Cminor.evalConstant, Genv.symbolAddress, hsymbol]
    · exact Cminor.eval_expr_list_sound (by rfl)
    refine Cminor.steps_trans hcallee ?_
    refine Cminor.Steps.cons (.return_to_caller ..) (Cminor.Steps.cons (.skip_seq ..) ?_)
    exact Cminor.steps_single (.return_some _ _ _ _ _ _ _ _
      (Cminor.eval_expr_sound heval) hfree)
  · exact hnext

/-- Both applications resolve the callback's cosine symbol to the checked polynomial. -/
theorem polynomial_global_symbols (n : Nat) :
    Genv.findSymbol (Binary64.Clight.Application.program n).globalenv.genv_genv _cos =
      some (Positive.ofNat 8) ∧
    Genv.findSymbol (Cminor.Imported.program n).globalenv (Positive.ofNat 378380) =
      some (Positive.ofNat 69) := by
  obtain ⟨hs, ht⟩ := shared_global_symbols n (id := _cos) (b := Positive.ofNat 8)
    (by decide +kernel)
  exact ⟨hs, ht⟩

/-- The source executes the internal-polynomial callback with unchanged memory. -/
theorem callback_source_execution [ExternalCalls]
    (n : Nat) (m : Mem) (x : Binary64.Value) (k : Cont) :
    StarE0 (Step2 (Binary64.Clight.Application.program n).globalenv)
      (.Callstate (.Internal f_testfun) [.Vfloat x] k m)
      (.Returnstate (.Vfloat (Binary64.testfun Binary64.Polynomial.cosine x))
        (callCont k) m) :=
  polynomial_callback_execution_in_context _ _ (Positive.ofNat 8)
    (polynomial_global_symbols n).1 (polynomial_source_lookup n) x k

-- Rewriting the imported global environment lookups at increased recursion depth.
set_option maxRecDepth 10000 in
/-- The imported callback runs to completion in every imported program, with the symbol and
function lookups discharged. -/
theorem callback_application_target_execution [ExternalCalls]
    (n : Nat) {mapping : BlockMap} {sourceMemory targetMemory : Mem}
    (hm : BlocksAgree mapping sourceMemory targetMemory)
    (x : Binary64.Value) (k : Cminor.Cont) :
    ∃ targetMemory',
      Cminor.Steps (Cminor.Imported.program n).globalenv
        (.Callstate (.Internal callbackTarget) [.Vfloat x] k targetMemory)
        E0 (.Returnstate (.Vfloat (Binary64.testfun Binary64.Polynomial.cosine x))
          (Cminor.callCont k) targetMemory') ∧
      BlocksAgree mapping sourceMemory targetMemory' ∧
      targetMemory'.nextblock = targetMemory.nextblock.succ.succ := by
  have hfunction : Genv.findFunct (Cminor.Imported.program n).globalenv
      (.Vptr (Positive.ofNat 69) Integers.Ptrofs.zero) =
      some (.Internal polynomialTarget) := by
    rw [find_function_at_zero_offset]
    exact polynomial_target_lookup n
  exact callback_target_execution (Binary64.Clight.Application.program n).globalenv
    (Cminor.Imported.program n).globalenv (Positive.ofNat 69)
    (polynomial_global_symbols n).2 hfunction hm x k

-- Kernel unfolding of the Clight global environment at block 6.
set_option maxRecDepth 10000 in
/-- Source block 6 holds the Clight callback in every application program. -/
theorem callback_source_lookup (n : Nat) :
    Genv.findFunctPtr (Binary64.Clight.Application.program n).globalenv.genv_genv
      (Positive.ofNat 6) = some (.Internal f_testfun) := rfl

-- Kernel evaluation of the imported global environment at block 71.
set_option maxRecDepth 100000 in
/-- Target block 71 holds the imported callback in every imported program. -/
theorem callback_target_lookup (n : Nat) :
    Genv.findFunctPtr (Cminor.Imported.program n).globalenv
      (Positive.ofNat 71) = some (.Internal callbackTarget) := by
  let globalsPrefix := (Cminor.Imported.program 0).prog_defs.take 72
  change Genv.findFunctPtr
    (Genv.addGlobals (Genv.emptyGenv (Cminor.Imported.program 0).prog_public)
      (globalsPrefix ++ [Cminor.Imported.mainDefinition n])) (Positive.ofNat 71) = _
  rw [find_function_before_last_global _ _ _ _ (by decide +kernel)]
  decide +kernel

/-- From related memories `hm`, both callbacks return the same value after their nested
polynomial call. -/
theorem callback_call_correspondence [ExternalCalls]
    (n : Nat) {mapping : BlockMap} {sourceMemory targetMemory : Mem}
    (hm : BlocksAgree mapping sourceMemory targetMemory) (x : Binary64.Value)
    (sourceCont : Cont) (targetCont : Cminor.Cont) :
    ∃ targetMemory',
      StarE0 (Step2 (Binary64.Clight.Application.program n).globalenv)
        (.Callstate (.Internal f_testfun) [.Vfloat x] sourceCont sourceMemory)
        (.Returnstate (.Vfloat (Binary64.testfun Binary64.Polynomial.cosine x))
          (callCont sourceCont) sourceMemory) ∧
      Cminor.Steps (Cminor.Imported.program n).globalenv
        (.Callstate (.Internal callbackTarget) [.Vfloat x] targetCont targetMemory)
        E0 (.Returnstate (.Vfloat (Binary64.testfun Binary64.Polynomial.cosine x))
          (Cminor.callCont targetCont) targetMemory') ∧
      BlocksAgree mapping sourceMemory targetMemory' := by
  obtain ⟨targetMemory', htarget, hrelated, _⟩ :=
    callback_application_target_execution n hm x targetCont
  exact ⟨targetMemory', callback_source_execution n _ _ _, htarget, hrelated⟩

/-- Every completed standalone source call has a matching target call. -/
theorem callback_return_preserved [calls : ExternalCalls]
    [ExternalCallsDeterministic calls] (n : Nat)
    {mapping : BlockMap} {sourceMemory targetMemory returnedMemory : Mem}
    (hm : BlocksAgree mapping sourceMemory targetMemory) (x : Binary64.Value)
    {value : Val} {trace : Trace}
    (hsource : Star (Step2 (Binary64.Clight.Application.program n).globalenv)
      (.Callstate (.Internal f_testfun) [.Vfloat x] .Kstop sourceMemory)
      trace (.Returnstate value .Kstop returnedMemory)) :
    ∃ targetMemory',
      Cminor.Steps (Cminor.Imported.program n).globalenv
        (.Callstate (.Internal callbackTarget) [.Vfloat x] .Kstop targetMemory)
        trace (.Returnstate value .Kstop targetMemory') ∧
      BlocksAgree mapping returnedMemory targetMemory' := by
  obtain ⟨htrace, hremaining⟩ := silent_execution_prefix
    (Binary64.Clight.Application.program n)
    (callback_source_execution n sourceMemory x .Kstop)
    (return_stop_no_step _ _ _) hsource
  have heq := starE0_of_stuck hremaining (return_stop_no_step _ _ _)
  rcases State.Returnstate.inj heq with ⟨rfl, _, rfl⟩
  subst trace
  obtain ⟨targetMemory', htarget, hrelated, _⟩ :=
    callback_application_target_execution n hm x .Kstop
  exact ⟨targetMemory', htarget, hrelated⟩

end Quadrature.Compiler
