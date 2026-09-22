import Quadrature.Compiler.Cminor.Annotations
import Quadrature.Compiler.Execution.Run
import Quadrature.Compiler.LTL.Semantics

/-!
# A checked LTL executor

`executeStep external ge s` runs one transition. If it returns `some (t, s')` then
`Step ge s t s'` (`execute_step_sound`), provided every `some` result of `external` is
permitted by CompCert's `externalCall`. That contract constrains only the calls
`external` accepts. `executeStep` returns `none` for external functions it cannot run,
so `none` means unchecked, not stuck.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.LTL

open CC
open Cminor (freeStack free_stack_iff)

/-- The shared executor type for external calls, `Execution.ExternalExecutor`. -/
abbrev ExternalExecutor := Cminor.ExternalExecutor
/-- The annotation executor of `Cminor/Annotations.lean`, reused. -/
abbrev annotatedExternalCall := Cminor.annotatedExternalCall

/-- `executeStep external ge s` runs one transition from `s`, returning its trace and successor,
or `none` when it cannot decide one. Builtins and external functions are run by `external`. -/
def executeStep (external : ExternalExecutor) (ge : Genv) : State → Option (Trace × State)
  | .Running s f sp pc rs m => do
      let bb ← f.fn_code.get pc
      pure (E0, .Block s f sp bb rs m)
  | .Block s f sp (instruction :: bb) rs m =>
      match instruction with
      | .Lop op args result => do
          let value ← evalOperation ge sp op (rs.values args)
          pure (E0, .Block s f sp bb
            ((rs.undefRegs (destroyedByOp op)).set (.R result) value) m)
      | .Lload chunk address args result => do
          let pointer ← evalAddressing ge sp address (rs.values args)
          let value ← Mem.loadv chunk m pointer
          pure (E0, .Block s f sp bb (rs.set (.R result) value) m)
      | .Lgetstack slot offset type result =>
          some (E0, .Block s f sp bb ((rs.undefRegs (destroyedByGetstack slot)).set
            (.R result) (rs (.S slot offset type))) m)
      | .Lsetstack source slot offset type =>
          some (E0, .Block s f sp bb ((rs.undefRegs (destroyedBySetstack type)).set
            (.S slot offset type) (rs.reg source)) m)
      | .Lstore chunk address args source => do
          let pointer ← evalAddressing ge sp address (rs.values args)
          let m' ← Mem.storev chunk m pointer (rs.reg source)
          pure (E0, .Block s f sp bb rs m')
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
          pure (trace, .Block s f sp bb
            ((rs.undefRegs (destroyedByBuiltin ef)).setResult result value) m')
      | .Lbranch next => some (E0, .Running s f sp next rs m)
      | .Lcond condition args yes no => do
          let result ← evalCondition condition (rs.values args)
          pure (E0, .Running s f sp (if result then yes else no) rs m)
      | .Ljumptable arg table =>
          match rs.reg arg with
          | .Vint index => do
              let next ← table[(Integers.Int.unsigned index).toNat]?
              pure (E0, .Running s f sp next (rs.undefRegs [.AX, .DX]) m)
          | _ => none
      | .Lreturn => do
          let m' ← freeStack m sp f.fn_stacksize
          pure (E0, .Returnstate s (returnRegs (parentLocset s) rs) m')
  | .Block _ _ _ [] _ _ => none
  | .Callstate s (.Internal f) rs m =>
      let (m', block) := Mem.alloc m 0 f.fn_stacksize
      some (E0, .Running s f (.Vptr block Integers.Ptrofs.zero) f.fn_entrypoint
        ((callRegs rs).undefRegs [.AX, .FP0]) m')
  | .Callstate s (.External ef) rs m => do
      let (trace, value, m') ← external ef ((locArguments ef.sig).map rs) m
      pure (trace, .Returnstate s
        ((undefCallerSaveRegs rs).set (.R (locResult ef.sig)) value) m')
  | .Returnstate (frame :: s) rs m =>
      some (E0, .Block s frame.caller frame.stack frame.continuation rs m)
  | .Returnstate [] _ _ => none

/-- `executeSteps external ge fuel s` runs exactly `fuel` transitions from `s` and concatenates
their traces, failing if any step fails. -/
def executeSteps (external : ExternalExecutor) (ge : Genv) :
    Nat → State → Option (Trace × State) :=
  Execution.run (executeStep external ge)

/-- `executeSteps` equals the shared runner `Execution.run` applied to `executeStep`. -/
theorem execute_steps_eq_run (external : ExternalExecutor) (ge : Genv)
    (fuel : Nat) (state : State) :
    executeSteps external ge fuel state = Execution.run (executeStep external ge) fuel state :=
  rfl

variable [ExternalCalls] {external : ExternalExecutor} {ge : Genv}

/-- Specialization of `Execution.ExternalExecutorSound` to this stage's `Genv`. -/
def ExternalExecutorSound (external : ExternalExecutor) (ge : Genv) : Prop :=
  Execution.ExternalExecutorSound external ge.toSenv

/-- If `executeStep external ge s` returns `some (t, s')` and `external` is sound, then
`Step ge s t s'`. -/
theorem execute_step_sound (hexternal : ExternalExecutorSound external ge)
    {start finish : State} {trace : Trace}
    (h : executeStep external ge start = some (trace, finish)) :
    Step ge start trace finish := by
  cases start with
  | Running s f sp pc rs m =>
      simp only [executeStep, bind, Option.bind_eq_some_iff] at h
      obtain ⟨bb, hcode, h⟩ := h
      cases h
      exact .startBlock _ _ _ _ _ _ _ hcode
  | Block s f sp instructions rs m =>
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
              exact .builtin _ _ _ _ _ _ _ _ _ _ _ _ _ (eval_builtin_args_sound hv)
                (hexternal _ _ _ _ _ _ hext)
          | Lbranch next =>
              cases h
              exact .branch _ _ _ _ _ _ _
          | Lcond condition args yes no =>
              simp only [executeStep, bind, Option.bind_eq_some_iff] at h
              obtain ⟨result, hb, h⟩ := h
              cases h
              exact .condition _ _ _ _ _ _ _ _ _ _ _ hb
          | Ljumptable arg table =>
              simp only [executeStep] at h
              cases harg : rs.reg arg <;> simp only [harg] at h <;> try cases h
              simp only [bind, Option.bind_eq_some_iff] at h
              obtain ⟨next, hn, h⟩ := h
              cases h
              exact .jumpTable _ _ _ _ _ _ _ _ _ _ harg hn
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

/-- If `executeSteps external ge fuel s` returns `some (t, s')` and `external` is sound, then
`Steps ge s t s'`. -/
theorem execute_steps_sound (hexternal : ExternalExecutorSound external ge)
    {fuel : Nat} {start finish : State} {trace : Trace}
    (h : executeSteps external ge fuel start = some (trace, finish)) :
    Steps ge start trace finish := by
  rw [execute_steps_eq_run] at h
  exact Execution.run_sound (execute_step_sound hexternal) Steps.refl Steps.cons h

/-- The annotation executor `annotatedExternalCall` is sound for this stage's `Genv`. -/
theorem annotated_external_executor_sound : ExternalExecutorSound annotatedExternalCall ge :=
  Cminor.annotated_external_call_sound

end Quadrature.LTL
