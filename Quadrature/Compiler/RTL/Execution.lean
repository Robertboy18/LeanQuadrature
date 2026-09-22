import Quadrature.Compiler.Cminor.Annotations
import Quadrature.Compiler.Execution.Run
import Quadrature.Compiler.RTL.Semantics

/-!
# A checked RTL executor

`executeStep external ge s` runs one transition. If it returns `some (t, s')` then
`Step ge s t s'` (`execute_step_sound`), provided every `some` result of `external` is
permitted by CompCert's `externalCall`. `executeStep` returns `none` for external
functions it cannot run, so `none` means unchecked, not stuck. The annotation executor
`annotatedExternalCall` runs the one builtin the ten programs use.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.RTL

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
      let instruction ← f.fn_code.get pc
      match instruction with
      | .Inop next => pure (E0, .Running s f sp next rs m)
      | .Iop op args result next => do
          let value ← evalOperation ge sp op (rs.values args)
          pure (E0, .Running s f sp next (rs.set result value) m)
      | .Iload chunk address args result next => do
          let pointer ← evalAddressing ge sp address (rs.values args)
          let value ← Mem.loadv chunk m pointer
          pure (E0, .Running s f sp next (rs.set result value) m)
      | .Istore chunk address args source next => do
          let pointer ← evalAddressing ge sp address (rs.values args)
          let m' ← Mem.storev chunk m pointer (rs.get source)
          pure (E0, .Running s f sp next rs m')
      | .Icall signature target args result next => do
          let fd ← findFunction ge target rs
          if fd.signature = signature then
            pure (E0, .Callstate (⟨result, f, sp, next, rs⟩ :: s) fd (rs.values args) m)
          else none
      | .Itailcall signature target args => do
          let fd ← findFunction ge target rs
          if fd.signature = signature then
            let m' ← freeStack m sp f.fn_stacksize
            pure (E0, .Callstate s fd (rs.values args) m')
          else none
      | .Ibuiltin ef args result next => do
          let values ← evalBuiltinArgs ge sp rs m args
          let (trace, value, m') ← external ef values m
          pure (trace, .Running s f sp next (rs.setResult result value) m')
      | .Icond condition args yes no => do
          let result ← evalCondition condition (rs.values args)
          pure (E0, .Running s f sp (if result then yes else no) rs m)
      | .Ijumptable arg table =>
          match rs.get arg with
          | .Vint index => do
              let next ← table[(Integers.Int.unsigned index).toNat]?
              pure (E0, .Running s f sp next rs m)
          | _ => none
      | .Ireturn result => do
          let m' ← freeStack m sp f.fn_stacksize
          pure (E0, .Returnstate s (rs.optget result) m')
  | .Callstate s (.Internal f) values m =>
      if HasArgTypes values f.fn_sig.sig_args then
        let (m', block) := Mem.alloc m 0 f.fn_stacksize
        some (E0, .Running s f (.Vptr block Integers.Ptrofs.zero) f.fn_entrypoint
          (initRegs values f.fn_params) m')
      else none
  | .Callstate s (.External ef) values m => do
      let (trace, value, m') ← external ef values m
      pure (trace, .Returnstate s value m')
  | .Returnstate (frame :: s) value m =>
      some (E0, .Running s frame.caller frame.stack frame.next
        (frame.registers.set frame.result value) m)
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
      obtain ⟨instruction, hcode, h⟩ := h
      cases instruction with
      | Inop next =>
          cases h
          exact .nop _ _ _ _ _ _ _ hcode
      | Iop op args result next =>
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨value, hvalue, h⟩ := h
          cases h
          exact .operation _ _ _ _ _ _ _ _ _ _ _ hcode hvalue
      | Iload chunk address args result next =>
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨pointer, hp, value, hv, h⟩ := h
          cases h
          exact .load _ _ _ _ _ _ _ _ _ _ _ _ _ hcode hp hv
      | Istore chunk address args source next =>
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨pointer, hp, m', hm, h⟩ := h
          cases h
          exact .store _ _ _ _ _ _ _ _ _ _ _ _ _ hcode hp hm
      | Icall signature target args result next =>
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨fd, hfd, h⟩ := h
          split at h
          · next hsig =>
              cases h
              exact .call _ _ _ _ _ _ _ _ _ _ _ _ hcode hfd hsig
          · cases h
      | Itailcall signature target args =>
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨fd, hfd, h⟩ := h
          split at h
          · next hsig =>
              simp only [Option.bind_eq_some_iff] at h
              obtain ⟨m', hm, h⟩ := h
              cases h
              obtain ⟨block, rfl, hm⟩ := free_stack_iff.mp hm
              exact .tailcall _ _ _ _ _ _ _ _ _ _ _ hcode hfd hsig hm
          · cases h
      | Ibuiltin ef args result next =>
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨values, hv, ⟨emitted, value, m'⟩, hext, h⟩ := h
          cases h
          exact .builtin _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcode
            (eval_builtin_args_sound hv) (hexternal _ _ _ _ _ _ hext)
      | Icond condition args yes no =>
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨result, hb, h⟩ := h
          cases h
          exact .branch _ _ _ _ _ _ _ _ _ _ _ hcode hb
      | Ijumptable arg table =>
          cases harg : rs.get arg <;> simp only [harg] at h <;> try cases h
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨next, hn, h⟩ := h
          cases h
          exact .jumpTable _ _ _ _ _ _ _ _ _ _ hcode harg hn
      | Ireturn result =>
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨m', hm, h⟩ := h
          cases h
          obtain ⟨block, rfl, hm⟩ := free_stack_iff.mp hm
          exact .returnValue _ _ _ _ _ _ _ _ hcode hm
  | Callstate s fd values m =>
      cases fd with
      | Internal f =>
          simp only [executeStep] at h
          split at h
          · next hargs =>
              cases h
              exact .internal_function _ _ _ _ _ _ hargs rfl
          · cases h
      | External ef =>
          simp only [executeStep, bind, Option.bind_eq_some_iff] at h
          obtain ⟨⟨emitted, value, m'⟩, hext, h⟩ := h
          cases h
          exact .external_function _ _ _ _ _ _ _ (hexternal _ _ _ _ _ _ hext)
  | Returnstate s value m =>
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

/-- CLean's `CC.doExternalCall` is a sound external executor for this stage's `Genv`. -/
theorem default_external_executor_sound : ExternalExecutorSound CC.doExternalCall ge :=
  Execution.default_external_executor_sound

/-- `execute_steps_sound` instantiated with CLean's `CC.doExternalCall`. -/
theorem default_execute_steps_sound {fuel : Nat} {start finish : State} {trace : Trace}
    (h : executeSteps CC.doExternalCall ge fuel start = some (trace, finish)) :
    Steps ge start trace finish :=
  execute_steps_sound default_external_executor_sound h

/-- The annotation executor `annotatedExternalCall` is sound for this stage's `Genv`. -/
theorem annotated_external_executor_sound : ExternalExecutorSound annotatedExternalCall ge :=
  Cminor.annotated_external_call_sound

end Quadrature.RTL
