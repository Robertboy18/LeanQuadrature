import Quadrature.Compiler.Cminor.Annotations
import Quadrature.Compiler.Execution.Run
import Quadrature.Compiler.Linear.Semantics

/-!
# A checked Linear executor

An executable checker for the rules of `Quadrature.Compiler.Linear.Semantics`. Read `executeStep`
first, which computes the successor of a state or fails when a lookup, memory access,
or signature check fails. `execute_step_sound` shows that every successful step is a
`Step` derivation whenever the external executor is sound.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Linear

open CC
open Cminor (freeStack free_stack_iff)

/-- Executable external calls, the contract shared by every stage. -/
abbrev ExternalExecutor := Cminor.ExternalExecutor
/-- The external executor that emits numeric annotations and delegates other calls to CLean. -/
abbrev annotatedExternalCall := Cminor.annotatedExternalCall

/-- Computes one Linear transition, using `external` for builtins and external functions.
Returns `none` when a lookup, memory access, or signature check fails. -/
def executeStep (external : ExternalExecutor) (ge : Genv) : State → Option (Trace × State)
  | .Running s f sp (instruction :: bb) rs m =>
      match instruction with
      | .Lop op args result => do
          let value ← evalOperation ge sp op (rs.values args)
          pure (E0, .Running s f sp bb
            ((rs.undefRegs (destroyedByOp op)).set (.R result) value) m)
      | .Lload chunk address args result => do
          let pointer ← evalAddressing ge sp address (rs.values args)
          let value ← Mem.loadv chunk m pointer
          pure (E0, .Running s f sp bb (rs.set (.R result) value) m)
      | .Lgetstack slot offset type result =>
          some (E0, .Running s f sp bb ((rs.undefRegs (destroyedByGetstack slot)).set
            (.R result) (rs (.S slot offset type))) m)
      | .Lsetstack source slot offset type =>
          some (E0, .Running s f sp bb ((rs.undefRegs (destroyedBySetstack type)).set
            (.S slot offset type) (rs.reg source)) m)
      | .Lstore chunk address args source => do
          let pointer ← evalAddressing ge sp address (rs.values args)
          let m' ← Mem.storev chunk m pointer (rs.reg source)
          pure (E0, .Running s f sp bb rs m')
      | .Lcall signature target => do
          let fd ← findFunction ge target rs
          if fd.signature = signature then
            pure (E0, .Callstate (⟨f, sp, rs, bb⟩ :: s) fd rs m)
          else none
      | .Ltailcall signature target => do
          let restored := returnRegs (parentLocset s) rs
          let fd ← findFunction ge target restored
          if fd.signature = signature then
            let m' ← freeStack m sp f.fn_stacksize
            pure (E0, .Callstate s fd restored m')
          else none
      | .Lbuiltin ef args result => do
          let values ← evalBuiltinArgs ge sp rs m args
          let (trace, value, m') ← external ef values m
          pure (trace, .Running s f sp bb
            ((rs.undefRegs (destroyedByBuiltin ef)).setResult result value) m')
      | .Llabel _ => some (E0, .Running s f sp bb rs m)
      | .Lgoto label => do
          let target ← findLabel label f.fn_code
          pure (E0, .Running s f sp target rs m)
      | .Lcond condition args label => do
          let result ← evalCondition condition (rs.values args)
          let target ← if result then findLabel label f.fn_code else some bb
          pure (E0, .Running s f sp target rs m)
      | .Ljumptable arg table =>
          match rs.reg arg with
          | .Vint index => do
              let label ← table[(Integers.Int.unsigned index).toNat]?
              let target ← findLabel label f.fn_code
              pure (E0, .Running s f sp target (rs.undefRegs [.AX, .DX]) m)
          | _ => none
      | .Lreturn => do
          let m' ← freeStack m sp f.fn_stacksize
          pure (E0, .Returnstate s (returnRegs (parentLocset s) rs) m')
  | .Running _ _ _ [] _ _ => none
  | .Callstate s (.Internal f) rs m =>
      let (m', block) := Mem.alloc m 0 f.fn_stacksize
      some (E0, .Running s f (.Vptr block Integers.Ptrofs.zero) f.fn_code
        ((callRegs rs).undefRegs [.AX, .FP0]) m')
  | .Callstate s (.External ef) rs m => do
      let (trace, value, m') ← external ef ((locArguments ef.sig).map rs) m
      pure (trace, .Returnstate s
        ((undefCallerSaveRegs rs).set (.R (locResult ef.sig)) value) m')
  | .Returnstate (frame :: s) rs m =>
      some (E0, .Running s frame.caller frame.stack frame.continuation rs m)
  | .Returnstate [] _ _ => none

/-- Runs exactly `fuel` transitions from a state, concatenating their traces. -/
def executeSteps (external : ExternalExecutor) (ge : Genv) :
    Nat → State → Option (Trace × State) :=
  Execution.run (executeStep external ge)

/-- The stage-specific executor implements the shared finite runner. -/
theorem execute_steps_eq_run (external : ExternalExecutor) (ge : Genv)
    (fuel : Nat) (state : State) :
    executeSteps external ge fuel state = Execution.run (executeStep external ge) fuel state :=
  rfl

variable [ExternalCalls] {external : ExternalExecutor} {ge : Genv}

/-- Every result accepted by `external` is permitted by the external-call relation over `ge`. -/
def ExternalExecutorSound (external : ExternalExecutor) (ge : Genv) : Prop :=
  Execution.ExternalExecutorSound external ge.toSenv

/-- A successful `executeStep` under a sound external executor `hexternal` is a `Step`. -/
theorem execute_step_sound (hexternal : ExternalExecutorSound external ge)
    {start finish : State} {trace : Trace}
    (h : executeStep external ge start = some (trace, finish)) :
    Step ge start trace finish := by
  cases start with
  | Running s f sp instructions rs m =>
      cases instructions with
      | nil => cases h
      | cons instruction bb =>
          cases instruction with
          | Lop op args result =>
              simp only [executeStep, bind, Option.bind_eq_some_iff] at h
              obtain ⟨value, hvalue, h⟩ := h
              cases h
              exact .operation _ _ _ _ _ _ _ _ _ _ hvalue
          | Lload chunk address args result =>
              simp only [executeStep, bind, Option.bind_eq_some_iff] at h
              obtain ⟨pointer, hp, value, hv, h⟩ := h
              cases h
              exact .load _ _ _ _ _ _ _ _ _ _ _ _ hp hv
          | Lgetstack slot offset type result =>
              cases h
              exact .getstack _ _ _ _ _ _ _ _ _ _
          | Lsetstack source slot offset type =>
              cases h
              exact .setstack _ _ _ _ _ _ _ _ _ _
          | Lstore chunk address args source =>
              simp only [executeStep, bind, Option.bind_eq_some_iff] at h
              obtain ⟨pointer, hp, m', hm, h⟩ := h
              cases h
              exact .store _ _ _ _ _ _ _ _ _ _ _ _ hp hm
          | Lcall signature target =>
              simp only [executeStep, bind, Option.bind_eq_some_iff] at h
              obtain ⟨fd, hfd, h⟩ := h
              split at h
              · next hsig =>
                  cases h
                  exact .call _ _ _ _ _ _ _ _ _ hfd hsig
              · cases h
          | Ltailcall signature target =>
              simp only [executeStep, bind, Option.bind_eq_some_iff] at h
              obtain ⟨fd, hfd, h⟩ := h
              split at h
              · next hsig =>
                  simp only [Option.bind_eq_some_iff] at h
                  obtain ⟨m', hm, h⟩ := h
                  cases h
                  obtain ⟨block, rfl, hm⟩ := free_stack_iff.mp hm
                  exact .tailcall _ _ _ _ _ _ _ _ _ _ hfd hsig hm
              · cases h
          | Lbuiltin ef args result =>
              simp only [executeStep, bind, Option.bind_eq_some_iff] at h
              obtain ⟨values, hv, ⟨emitted, value, m'⟩, hext, h⟩ := h
              cases h
              exact .builtin _ _ _ _ _ _ _ _ _ _ _ _ _ (LTL.eval_builtin_args_sound hv)
                (hexternal _ _ _ _ _ _ hext)
          | Llabel label =>
              cases h
              exact .label _ _ _ _ _ _ _
          | Lgoto label =>
              simp only [executeStep, bind, Option.bind_eq_some_iff] at h
              obtain ⟨target, htarget, h⟩ := h
              cases h
              exact .goto _ _ _ _ _ _ _ _ htarget
          | Lcond condition args label =>
              simp only [executeStep, bind, Option.bind_eq_some_iff] at h
              obtain ⟨result, hb, h⟩ := h
              cases result with
              | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_some] at h
                  cases h
                  exact .condition_false _ _ _ _ _ _ _ _ _ hb
              | true =>
                  simp only [↓reduceIte, Option.bind_eq_some_iff] at h
                  obtain ⟨target, htarget, h⟩ := h
                  cases h
                  exact .condition_true _ _ _ _ _ _ _ _ _ _ hb htarget
          | Ljumptable arg table =>
              simp only [executeStep] at h
              cases harg : rs.reg arg <;> simp only [harg] at h <;> try cases h
              simp only [bind, Option.bind_eq_some_iff] at h
              obtain ⟨label, hn, target, htarget, h⟩ := h
              cases h
              exact .jumpTable _ _ _ _ _ _ _ _ _ _ _ harg hn htarget
          | Lreturn =>
              simp only [executeStep, bind, Option.bind_eq_some_iff] at h
              obtain ⟨m', hm, h⟩ := h
              cases h
              obtain ⟨block, rfl, hm⟩ := free_stack_iff.mp hm
              exact .returnValue _ _ _ _ _ _ _ hm
  | Callstate s fd rs m =>
      cases fd with
      | Internal f =>
          cases h
          exact .internal_function _ _ _ _ _ _ rfl
      | External ef =>
          simp only [executeStep, bind, Option.bind_eq_some_iff] at h
          obtain ⟨⟨emitted, value, m'⟩, hext, h⟩ := h
          cases h
          exact .external_function _ _ _ _ _ _ _ (hexternal _ _ _ _ _ _ hext)
  | Returnstate s rs m =>
      cases s <;> cases h
      exact .return_to_caller _ _ _ _

/-- A successful `executeSteps` run under a sound external executor `hexternal` is a `Steps`
derivation with the same trace. -/
theorem execute_steps_sound (hexternal : ExternalExecutorSound external ge)
    {fuel : Nat} {start finish : State} {trace : Trace}
    (h : executeSteps external ge fuel start = some (trace, finish)) :
    Steps ge start trace finish := by
  rw [execute_steps_eq_run] at h
  exact Execution.run_sound (execute_step_sound hexternal) Steps.refl Steps.cons h

/-- The numeric-annotation executor is sound in every global environment. -/
theorem annotated_external_executor_sound : ExternalExecutorSound annotatedExternalCall ge :=
  Cminor.annotated_external_call_sound

end Quadrature.Linear
