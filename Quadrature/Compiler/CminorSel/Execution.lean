import Quadrature.Compiler.Cminor.Annotations
import Quadrature.Compiler.CminorSel.Semantics
import Quadrature.Compiler.Execution.Run

/-!
# An executable checker for instruction-selected programs

`executeStep external ge s` runs one transition. If it returns `some (t, s')` then
`Step ge s t s'` (`execute_step_sound`), provided every `some` result of `external` is
permitted by CompCert's `externalCall`. `executeStep` returns `none` for external
functions it cannot run, so `none` means unchecked, not stuck. `executeSteps` runs an
exact number of transitions and concatenates their traces.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.CminorSel

open CC
open Cminor (freeStack free_stack_iff)

/-- The shared executor type for external calls, `Execution.ExternalExecutor`. -/
abbrev ExternalExecutor := Cminor.ExternalExecutor
/-- The annotation executor of `Cminor/Annotations.lean`, reused. -/
abbrev annotatedExternalCall := Cminor.annotatedExternalCall

/-- `executeStep external ge s` runs one transition from `s`, returning its trace and successor,
or `none` when it cannot decide one. Builtins and external functions are run by `external`. -/
def executeStep (external : ExternalExecutor) (ge : Genv) : State → Option (Trace × State)
  | .Running f statement k stack env memory =>
      match statement with
      | .Sskip =>
          match k with
          | .Kseq s rest => some (E0, .Running f s rest stack env memory)
          | .Kblock rest => some (E0, .Running f .Sskip rest stack env memory)
          | _ => do
              let memory' ← freeStack memory stack f.fn_stackspace
              pure (E0, .Returnstate .Vundef k memory')
      | .Sassign name a => do
          let value ← evalExpr ge stack env memory [] a
          pure (E0, .Running f .Sskip k stack (env.set name value) memory)
      | .Sstore chunk address args a => do
          let values ← evalExprList ge stack env memory [] args
          let value ← evalExpr ge stack env memory [] a
          let pointer ← evalAddressing ge stack address values
          let memory' ← Mem.storev chunk memory pointer value
          pure (E0, .Running f .Sskip k stack env memory')
      | .Scall result signature a args => do
          let function ← evalExprOrSymbol ge stack env memory [] a
          let values ← evalExprList ge stack env memory [] args
          let fd ← CC.Genv.findFunct ge function
          if fd.signature = signature then
            pure (E0, .Callstate fd values (.Kcall result f stack env k) memory)
          else none
      | .Stailcall signature a args => do
          let function ← evalExprOrSymbol ge stack env memory [] a
          let values ← evalExprList ge stack env memory [] args
          let fd ← CC.Genv.findFunct ge function
          if fd.signature = signature then
            let memory' ← freeStack memory stack f.fn_stackspace
            pure (E0, .Callstate fd values (callCont k) memory')
          else none
      | .Sbuiltin result ef args => do
          let values ← evalBuiltinArgs ge stack env memory args
          let (trace, value, memory') ← external ef values memory
          pure (trace, .Running f .Sskip k stack (setBuiltinRes result value env) memory')
      | .Sseq first second =>
          some (E0, .Running f first (.Kseq second k) stack env memory)
      | .Sifthenelse condition yes no => do
          let result ← evalCondExpr ge stack env memory [] condition
          pure (E0, .Running f (if result then yes else no) k stack env memory)
      | .Sloop body =>
          some (E0, .Running f body (.Kseq (.Sloop body) k) stack env memory)
      | .Sblock body => some (E0, .Running f body (.Kblock k) stack env memory)
      | .Sexit depth =>
          match k with
          | .Kseq _ rest => some (E0, .Running f (.Sexit depth) rest stack env memory)
          | .Kblock rest =>
              match depth with
              | 0 => some (E0, .Running f .Sskip rest stack env memory)
              | depth + 1 => some (E0, .Running f (.Sexit depth) rest stack env memory)
          | _ => none
      | .Sswitch a => do
          let depth ← evalExitExpr ge stack env memory [] a
          pure (E0, .Running f (.Sexit depth) k stack env memory)
      | .Sreturn a => do
          let value ← match a with
            | none => some .Vundef
            | some a => evalExpr ge stack env memory [] a
          let memory' ← freeStack memory stack f.fn_stackspace
          pure (E0, .Returnstate value (callCont k) memory')
      | .Slabel _ body => some (E0, .Running f body k stack env memory)
      | .Sgoto name => do
          let (body, rest) ← findLabel name f.fn_body (callCont k)
          pure (E0, .Running f body rest stack env memory)
  | .Callstate (.Internal f) values k memory =>
      if HasArgTypes values f.fn_sig.sig_args then
        let (memory', stack) := Mem.alloc memory 0 f.fn_stackspace
        let env := setLocals f.fn_vars (setParams values f.fn_params)
        some (E0, .Running f f.fn_body k (.Vptr stack Integers.Ptrofs.zero) env memory')
      else none
  | .Callstate (.External ef) values k memory => do
      let (trace, value, memory') ← external ef values memory
      pure (trace, .Returnstate value k memory')
  | .Returnstate value (.Kcall result f stack env k) memory =>
      some (E0, .Running f .Sskip k stack (setOptvar result value env) memory)
  | .Returnstate .. => none

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
  | Running f statement k stack env memory =>
      cases statement with
      | Sskip =>
          cases k with
          | Kseq s k =>
              simp only [executeStep, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .skip_seq _ _ _ _ _ _
          | Kblock k =>
              simp only [executeStep, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact .skip_block _ _ _ _ _
          | Kstop =>
              simp only [executeStep, bind, Option.bind_eq_some_iff,
                pure, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨memory', hfree, rfl, rfl⟩ := h
              obtain ⟨block, rfl, hfree⟩ := free_stack_iff.mp hfree
              exact .skip_call _ _ _ _ _ _ trivial hfree
          | Kcall result caller callerStack callerEnv rest =>
              simp only [executeStep, bind, Option.bind_eq_some_iff,
                pure, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨memory', hfree, rfl, rfl⟩ := h
              obtain ⟨block, rfl, hfree⟩ := free_stack_iff.mp hfree
              exact .skip_call _ _ _ _ _ _ trivial hfree
      | Sassign name a =>
          simp only [executeStep, bind, Option.bind_eq_some_iff,
            pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨value, hvalue, rfl, rfl⟩ := h
          exact .assign _ _ _ _ _ _ _ _ (eval_expr_sound hvalue)
      | Sstore chunk address args a =>
          simp only [executeStep, bind, Option.bind_eq_some_iff,
            pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨values, hargs, value, hv, pointer, hp, memory', hm, rfl, rfl⟩ := h
          exact .store _ _ _ _ _ _ _ _ _ _ _ _ _
            (eval_expr_list_sound hargs) (eval_expr_sound hv) hp hm
      | Scall result signature a args =>
          simp only [executeStep, bind, Option.bind_eq_some_iff] at h
          obtain ⟨function, hf, values, hv, fd, hfd, h⟩ := h
          split at h
          · next hsig =>
              cases h
              exact .call _ _ _ _ _ _ _ _ _ _ _ _
                (eval_expr_or_symbol_sound hf) (eval_expr_list_sound hv) hfd hsig
          · cases h
      | Stailcall signature a args =>
          simp only [executeStep, bind, Option.bind_eq_some_iff] at h
          obtain ⟨function, hf, values, hv, fd, hfd, h⟩ := h
          split at h
          · next hsig =>
              simp only [Option.bind_eq_some_iff] at h
              obtain ⟨memory', hfree, h⟩ := h
              cases h
              obtain ⟨block, rfl, hfree⟩ := free_stack_iff.mp hfree
              exact .tailcall _ _ _ _ _ _ _ _ _ _ _ _
                (eval_expr_or_symbol_sound hf) (eval_expr_list_sound hv) hfd hsig hfree
          · cases h
      | Sbuiltin result ef args =>
          simp only [executeStep, bind, Option.bind_eq_some_iff] at h
          obtain ⟨values, hv, ⟨emitted, value, memory'⟩, hext, h⟩ := h
          cases h
          exact .builtin _ _ _ _ _ _ _ _ _ _ _ _
            (eval_builtin_args_sound hv) (hexternal _ _ _ _ _ _ hext)
      | Sseq first second =>
          cases h
          exact .seq _ _ _ _ _ _ _
      | Sifthenelse condition yes no =>
          simp only [executeStep, bind, Option.bind_eq_some_iff,
            pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨result, hb, rfl, rfl⟩ := h
          exact .branch _ _ _ _ _ _ _ _ _ (eval_cond_expr_sound hb)
      | Sloop body =>
          cases h
          exact .loop _ _ _ _ _ _
      | Sblock body =>
          cases h
          exact .block _ _ _ _ _ _
      | Sexit depth =>
          cases k with
          | Kstop => cases h
          | Kcall => cases h
          | Kseq s rest =>
              cases h
              exact .exit_seq _ _ _ _ _ _ _
          | Kblock rest =>
              cases depth with
              | zero =>
                  cases h
                  exact .exit_block_zero _ _ _ _ _
              | succ depth =>
                  cases h
                  exact .exit_block_succ _ _ _ _ _ _
      | Sswitch a =>
          simp only [executeStep, bind, Option.bind_eq_some_iff,
            pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨depth, hdepth, rfl, rfl⟩ := h
          exact .switch _ _ _ _ _ _ _ (eval_exit_expr_sound hdepth)
      | Sreturn a =>
          cases a with
          | none =>
              simp only [executeStep, bind, Option.bind_some, Option.bind_eq_some_iff,
                pure, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨memory', hfree, rfl, rfl⟩ := h
              obtain ⟨block, rfl, hfree⟩ := free_stack_iff.mp hfree
              exact .return_none _ _ _ _ _ _ hfree
          | some a =>
              simp only [executeStep, bind, Option.bind_eq_some_iff,
                pure, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨value, hv, memory', hfree, rfl, rfl⟩ := h
              obtain ⟨block, rfl, hfree⟩ := free_stack_iff.mp hfree
              exact .return_some _ _ _ _ _ _ _ _ (eval_expr_sound hv) hfree
      | Slabel name body =>
          cases h
          exact .label _ _ _ _ _ _ _
      | Sgoto name =>
          simp only [executeStep, bind, Option.bind_eq_some_iff] at h
          obtain ⟨⟨body, rest⟩, hlabel, h⟩ := h
          cases h
          exact .goto _ _ _ _ _ _ _ _ hlabel
  | Callstate fd values k memory =>
      cases fd with
      | Internal f =>
          simp only [executeStep] at h
          split at h
          · next hargs =>
              cases h
              exact .internal_function _ _ _ _ _ _ _ hargs rfl rfl
          · cases h
      | External ef =>
          simp only [executeStep, bind, Option.bind_eq_some_iff] at h
          obtain ⟨⟨emitted, value, memory'⟩, hext, h⟩ := h
          cases h
          exact .external_function _ _ _ _ _ _ _ (hexternal _ _ _ _ _ _ hext)
  | Returnstate value k memory =>
      cases k <;> cases h
      exact .return_to_caller _ _ _ _ _ _ _

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

end Quadrature.CminorSel
