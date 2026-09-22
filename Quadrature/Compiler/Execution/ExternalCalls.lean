import CCLib.ClightExecSound

/-!
# External-call contracts for checked execution

Every stage's checker takes an `ExternalExecutor`, a function that runs one external
call on CLean's shared values, memory, events, and symbol environments.
`ExternalExecutorSound` says each result it accepts is permitted by CompCert's
`externalCall` relation. `ExternalExecutorAgrees` says each result it accepts is the
only permitted one, trace included. Both contracts constrain only the calls the
executor accepts and assume nothing about the external environment as a whole.

`CC.doExternalCall` is CLean's executor for the `malloc`, `free`, `memcpy`, and debug
builtins. It satisfies both contracts. The annotation executor used by the ten
programs is in `Cminor/Annotations.lean`.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Execution

open CC

/-- `ExternalExecutor` runs one external call and returns `none` when it cannot decide it.
Shared by all compiler stages. -/
abbrev ExternalExecutor := ExtFun → List Val → Mem → Option (Trace × Val × Mem)

/-- `ExternalExecutorSound external ge` holds when every `some` result of `external` is
permitted by `externalCall` in the symbol environment `ge`. -/
def ExternalExecutorSound [ExternalCalls] (external : ExternalExecutor) (ge : Senv) : Prop :=
  ∀ ef args memory trace value memory',
    external ef args memory = some (trace, value, memory') →
      externalCall ef ge args memory trace value memory'

/-- `ExternalExecutorAgrees external ge` holds when a `some` result of `external` is the only
result `externalCall` permits for that call, trace included. -/
def ExternalExecutorAgrees [ExternalCalls] (external : ExternalExecutor) (ge : Senv) : Prop :=
  ∀ ef args memory trace value memory' otherTrace otherValue otherMemory,
    external ef args memory = some (trace, value, memory') →
    externalCall ef ge args memory otherTrace otherValue otherMemory →
    trace = otherTrace ∧ value = otherValue ∧ memory' = otherMemory

private theorem empty_trace_unique {sem : ExtcallSem} {ge : Senv}
    {args : List Val} {memory memory' otherMemory : Mem} {trace otherTrace : Trace}
    {value otherValue : Val} (hdeterm : ExtcallDeterm sem ge)
    (h : sem ge args memory trace value memory') (hempty : trace = [])
    (hother : sem ge args memory otherTrace otherValue otherMemory) :
    trace = otherTrace ∧ value = otherValue ∧ memory' = otherMemory := by
  obtain ⟨hmatch, hrest⟩ := hdeterm.determ _ _ _ _ _ _ _ _ h hother
  have htrace : trace = otherTrace := by
    subst trace
    cases hmatch
    rfl
  exact ⟨htrace, hrest htrace⟩

/-- CLean's `CC.doExternalCall` is sound: every result it accepts is permitted by `externalCall`. -/
theorem default_external_executor_sound [ExternalCalls] {ge : Senv} :
    ExternalExecutorSound CC.doExternalCall ge :=
  CC.doExternalCall_sound ge

/-- CLean's `CC.doExternalCall` agrees with `externalCall`: its builtins emit no events and
determine their results uniquely. -/
theorem default_external_executor_agrees [ExternalCalls] {ge : Senv} :
    ExternalExecutorAgrees CC.doExternalCall ge := by
  intro ef args memory trace value memory' otherTrace otherValue otherMemory h hother
  have hsem := CC.doExternalCall_sound ge ef args memory trace value memory' h
  cases ef with
  | EF_malloc =>
      exact empty_trace_unique extcallMallocSem_determ hsem (by cases hsem; rfl) hother
  | EF_free =>
      exact empty_trace_unique extcallFreeSem_determ hsem (by cases hsem <;> rfl) hother
  | EF_memcpy size alignment =>
      exact empty_trace_unique (extcallMemcpySem_determ size alignment)
        hsem (by cases hsem; rfl) hother
  | EF_debug kind text types =>
      exact empty_trace_unique extcallDebugSem_determ hsem (by cases hsem; rfl) hother
  | _ => simp [CC.doExternalCall] at h

end Quadrature.Execution
