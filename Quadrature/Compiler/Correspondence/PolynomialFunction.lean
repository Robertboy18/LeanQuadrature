import Quadrature.Compiler.Correspondence.FloatExpressions
import Quadrature.Compiler.Correspondence.GlobalFunctions

/-!
# Clight and Cminor execution of the internal cosine polynomial

Relates the Clight and Cminor versions of the internal cosine polynomial for the ten
programs, by `FloatExprLowering` on the Horner body and `BlocksAgree` on memory. Read
`polynomial_call_correspondence` first: from related memories, both calls return the same
binary64 value for every input, and the target's zero-size frame is allocated and freed.
`polynomial_return_preserved`: if the Clight call from `Kstop` terminates with trace `t` and
value `v`, the Cminor call terminates with the same `t` and `v` and related memory. This
holds under `ExternalCallsDeterministic`, where external calls have unique outcomes. Lookup
is checked in the application globals.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Compiler

open CC
open Binary64.Clight

/-- The imported internal polynomial, compiler global 68 at memory block 69. -/
def polynomialTarget : Cminor.Function :=
  match h : Cminor.Imported.global68.2 with
  | .Gfun (.Internal f) => f
  | .Gfun (.External _) => False.elim (by cases h)
  | .Gvar _ => False.elim (by cases h)

/-- Cminor syntax for the same separately rounded Horner recurrence. -/
def hornerTarget (rename : Ident → Ident) : List Binary64.Value → Cminor.Expr
  | [] => .Econst (.Ofloatconst Binary64.zero)
  | c :: cs =>
    .Ebinop .Oaddf (.Econst (.Ofloatconst c))
      (.Ebinop .Omulf (.Evar (rename polynomialSquare)) (hornerTarget rename cs))

/-- The Clight Horner expression lowers to `hornerTarget` under any renaming. -/
theorem horner_lowering (rename : Ident → Ident) (coefficients : List Binary64.Value) :
    FloatExprLowering rename (hornerExpression coefficients)
      (hornerTarget rename coefficients) := by
  induction coefficients with
  | nil => exact .constant _
  | cons c cs ih => exact .binary .add (.constant c) (.binary .mul (.temp _) ih)

/-- Global 68 of the imported program is `polynomialTarget`. -/
theorem polynomial_target_definition :
    Cminor.Imported.global68.2 = .Gfun (.Internal polynomialTarget) := rfl

/-- The imported body squares the argument and returns the Horner expression. -/
theorem polynomial_target_body :
    polynomialTarget.fn_body =
      .Sseq (.Sassign polynomialSquare
        (.Ebinop .Omulf (.Evar polynomialArgument) (.Evar polynomialArgument)))
        (.Sreturn (some (hornerTarget id Binary64.Polynomial.coefficients))) := rfl

/-- The imported polynomial takes and returns one float. -/
theorem polynomial_target_signature :
    polynomialTarget.fn_sig = mksignature [.Xfloat] .Xfloat cc_default := rfl

/-- The imported polynomial has a zero-size stack frame. -/
theorem polynomial_target_stackspace : polynomialTarget.fn_stackspace = 0 := rfl

/-- Entry bindings for the argument and the uninitialized square temporary. -/
def polynomialLocals (x : Binary64.Value) : TempEnv :=
  ((PTree.empty : TempEnv).set polynomialSquare .Vundef).set polynomialArgument (.Vfloat x)

/-- Entering the imported polynomial with argument `x` binds exactly `polynomialLocals x`. -/
theorem polynomial_entry_locals (x : Binary64.Value) :
    Cminor.setLocals polynomialTarget.fn_vars
      (Cminor.setParams [.Vfloat x] polynomialTarget.fn_params) = polynomialLocals x := rfl

/-- The entry locals agree with themselves under the identity renaming. -/
theorem polynomial_locals_agree (mapping : BlockMap) (x : Binary64.Value) :
    LocalsAgree mapping id (polynomialLocals x) (polynomialLocals x) :=
  ((LocalsAgree.empty mapping id).set (fun _ _ h => h) polynomialSquare .undef).set
    (fun _ _ h => h) polynomialArgument (.float x)

/-- Source Horner evaluation is the exact FloatLib recurrence. -/
theorem horner_source_eval (ge : CGenv) (e : Env) (le : TempEnv) (m : Mem)
    (z : Binary64.Value) (hz : le.get polynomialSquare = some (.Vfloat z))
    (coefficients : List Binary64.Value) :
    doEvalExpr ge e le m (hornerExpression coefficients) =
      some (.Vfloat (Binary64.Polynomial.horner z coefficients)) := by
  induction coefficients with
  | nil => rfl
  | cons c cs ih =>
    simp only [hornerExpression, doEvalExpr, hz, ih]
    rw [(horner_lowering id cs).source_type]
    rfl

/-- Expression preservation transfers Horner evaluation to related locals. -/
theorem horner_target_eval (sourceGe : CGenv) (targetGe : Cminor.Genv)
    (e : Env) (stack : Val) (sourceMemory targetMemory : Mem)
    (sourceLocals : TempEnv) (targetLocals : Cminor.Env) (mapping : BlockMap)
    (rename : Ident → Ident)
    (hlocals : LocalsAgree mapping rename sourceLocals targetLocals)
    (z : Binary64.Value) (hz : sourceLocals.get polynomialSquare = some (.Vfloat z))
    (coefficients : List Binary64.Value) :
    Cminor.evalExpr targetGe stack targetLocals targetMemory (hornerTarget rename coefficients) =
      some (.Vfloat (Binary64.Polynomial.horner z coefficients)) := by
  obtain ⟨value, heval, hrel⟩ := (horner_lowering rename coefficients).eval_preserved
    sourceGe targetGe e stack sourceMemory targetMemory sourceLocals targetLocals hlocals
    (horner_source_eval sourceGe e sourceLocals sourceMemory z hz coefficients)
  cases hrel
  exact heval

/-- The source returns the polynomial value with unchanged memory. -/
theorem polynomial_source_execution [ExternalCalls]
    (ge : CGenv) (m : Mem) (x : Binary64.Value) (k : Cont) :
    StarE0 (Step2 ge) (.Callstate (.Internal polynomialFunction) [.Vfloat x] k m)
      (.Returnstate (.Vfloat (Binary64.Polynomial.cosine x)) (callCont k) m) := by
  repeat'
    first
    | (guard_target =~ StarE0 _ (.Returnstate _ (callCont k) _) _
       exact StarE0.refl _)
    | refine StarE0.step _ _ _ (doStep_sound _ _ _ _ (by rfl)) ?_

/-- The target frees its frame and preserves the memory relation. -/
theorem polynomial_target_execution [ExternalCalls]
    (sourceGe : CGenv) (targetGe : Cminor.Genv)
    {mapping : BlockMap} {sourceMemory targetMemory : Mem}
    (hm : BlocksAgree mapping sourceMemory targetMemory)
    (x : Binary64.Value) (k : Cminor.Cont) :
    ∃ targetMemory',
      Cminor.Steps targetGe
        (.Callstate (.Internal polynomialTarget) [.Vfloat x] k targetMemory)
        E0 (.Returnstate (.Vfloat (Binary64.Polynomial.cosine x))
          (Cminor.callCont k) targetMemory') ∧
      BlocksAgree mapping sourceMemory targetMemory' ∧
      targetMemory'.nextblock = targetMemory.nextblock.succ := by
  obtain ⟨m', hfree, hrelated, hnext⟩ := hm.alloc_free_target_exists 0 0
  refine ⟨m', ?_, hrelated, hnext⟩
  have hlocals := polynomial_locals_agree mapping x
  have hupdated := hlocals.set (fun _ _ h => h) polynomialSquare
    (.float (Floats.Float.mul x x))
  have heval := horner_target_eval sourceGe targetGe emptyEnv
    (.Vptr targetMemory.nextblock Integers.Ptrofs.zero)
    sourceMemory (Mem.alloc targetMemory 0 0).1 _ _ mapping id hupdated
    (Floats.Float.mul x x) (PTree.gss _ _ _) Binary64.Polynomial.coefficients
  have hentry : Cminor.Step targetGe
      (.Callstate (.Internal polynomialTarget) [.Vfloat x] k targetMemory) E0
      (.Running polynomialTarget polynomialTarget.fn_body k
        (.Vptr targetMemory.nextblock Integers.Ptrofs.zero)
        (polynomialLocals x) (Mem.alloc targetMemory 0 0).1) :=
    .internal_function _ _ _ _ _ _ _ (.cons trivial .nil) rfl (polynomial_entry_locals x)
  rw [polynomial_target_body] at hentry
  refine Cminor.Steps.cons hentry (Cminor.Steps.cons (.seq ..) ?_)
  refine Cminor.Steps.cons (.assign _ _ _ _ _ _ _ (.Vfloat (Floats.Float.mul x x)) ?_) ?_
  · exact Cminor.eval_expr_sound (by rfl)
  refine Cminor.Steps.cons (.skip_seq ..) ?_
  exact Cminor.steps_single (.return_some _ _ _ _ _ _ _ _
    (Cminor.eval_expr_sound heval) hfree)

-- Kernel unfolding of the Clight global environment at block 8.
set_option maxRecDepth 10000 in
/-- Source block 8 holds the Clight polynomial function in every application program. -/
theorem polynomial_source_lookup (n : Nat) :
    Genv.findFunctPtr (Binary64.Clight.Application.program n).globalenv.genv_genv
      (Positive.ofNat 8) = some (.Internal polynomialFunction) := rfl

/-- A pointer with zero offset resolves through its block's function definition. -/
theorem find_function_at_zero_offset {F V : Type} (ge : Genv F V) (b : Block) :
    Genv.findFunct ge (.Vptr b Integers.Ptrofs.zero) = Genv.findFunctPtr ge b := rfl

/-- Appending a global preserves function lookup at an earlier block. -/
theorem find_function_before_last_global {F V : Type} (ge : Genv F V)
    (globals : List (Ident × GlobDef F V)) (last : Ident × GlobDef F V)
    (b : Block) (hb : (Genv.addGlobals ge globals).genv_next ≠ b) :
    Genv.findFunctPtr (Genv.addGlobals ge (globals ++ [last])) b =
      Genv.findFunctPtr (Genv.addGlobals ge globals) b := by
  change (globals.foldl Genv.addGlobal ge).genv_next ≠ b at hb
  simp only [Genv.addGlobals, List.foldl_append, List.foldl_cons, List.foldl_nil,
    Genv.findFunctPtr, Genv.findDef, Genv.addGlobal, PTree.gso _ _ _ _ hb]

-- Kernel evaluation of the imported global environment at block 69.
set_option maxRecDepth 100000 in
/-- Target block 69 holds the imported polynomial in every imported program. -/
theorem polynomial_target_lookup (n : Nat) :
    Genv.findFunctPtr (Cminor.Imported.program n).globalenv
      (Positive.ofNat 69) = some (.Internal polynomialTarget) := by
  let globalsPrefix := (Cminor.Imported.program 0).prog_defs.take 72
  change Genv.findFunctPtr
    (Genv.addGlobals (Genv.emptyGenv (Cminor.Imported.program 0).prog_public)
      (globalsPrefix ++ [Cminor.Imported.mainDefinition n])) (Positive.ofNat 69) = _
  rw [find_function_before_last_global _ _ _ _ (by decide +kernel)]
  decide +kernel

/-- From related memories `hm`, both polynomial calls return the same binary64 value, and the
memories stay related. -/
theorem polynomial_call_correspondence [ExternalCalls]
    (n : Nat) {mapping : BlockMap} {sourceMemory targetMemory : Mem}
    (hm : BlocksAgree mapping sourceMemory targetMemory) (x : Binary64.Value)
    (sourceCont : Cont) (targetCont : Cminor.Cont) :
    ∃ targetMemory',
      StarE0 (Step2 (Binary64.Clight.Application.program n).globalenv)
        (.Callstate (.Internal polynomialFunction) [.Vfloat x] sourceCont sourceMemory)
        (.Returnstate (.Vfloat (Binary64.Polynomial.cosine x))
          (callCont sourceCont) sourceMemory) ∧
      Cminor.Steps (Cminor.Imported.program n).globalenv
        (.Callstate (.Internal polynomialTarget) [.Vfloat x] targetCont targetMemory)
        E0 (.Returnstate (.Vfloat (Binary64.Polynomial.cosine x))
          (Cminor.callCont targetCont) targetMemory') ∧
      BlocksAgree mapping sourceMemory targetMemory' := by
  obtain ⟨targetMemory', htarget, hrelated, _⟩ := polynomial_target_execution
    (Binary64.Clight.Application.program n).globalenv
    (Cminor.Imported.program n).globalenv hm x targetCont
  exact ⟨targetMemory', polynomial_source_execution _ _ _ _, htarget, hrelated⟩

/-- Any completed source call is matched by a target call with the same return value. -/
theorem polynomial_return_preserved [calls : ExternalCalls]
    [ExternalCallsDeterministic calls] (n : Nat)
    {mapping : BlockMap} {sourceMemory targetMemory returnedMemory : Mem}
    (hm : BlocksAgree mapping sourceMemory targetMemory) (x : Binary64.Value)
    {value : Val} {trace : Trace}
    (hsource : Star (Step2 (Binary64.Clight.Application.program n).globalenv)
      (.Callstate (.Internal polynomialFunction) [.Vfloat x] .Kstop sourceMemory)
      trace (.Returnstate value .Kstop returnedMemory)) :
    ∃ targetMemory',
      Cminor.Steps (Cminor.Imported.program n).globalenv
        (.Callstate (.Internal polynomialTarget) [.Vfloat x] .Kstop targetMemory)
        trace (.Returnstate value .Kstop targetMemory') ∧
      BlocksAgree mapping returnedMemory targetMemory' := by
  obtain ⟨htrace, hremaining⟩ := silent_execution_prefix
    (Binary64.Clight.Application.program n)
    (polynomial_source_execution _ sourceMemory x .Kstop)
    (return_stop_no_step _ _ _) hsource
  have heq := starE0_of_stuck hremaining (return_stop_no_step _ _ _)
  rcases State.Returnstate.inj heq with ⟨rfl, _, rfl⟩
  subst trace
  obtain ⟨targetMemory', htarget, hrelated, _⟩ := polynomial_target_execution
    (Binary64.Clight.Application.program n).globalenv
    (Cminor.Imported.program n).globalenv hm x .Kstop
  exact ⟨targetMemory', htarget, hrelated⟩

end Quadrature.Compiler
