import Quadrature.Compiler.Cminor.Execution

/-!
# Checked execution of numeric annotations

`EF_annot text types` is CompCert's annotation builtin: an external call that emits the
event `Event_annot text events` describing its arguments and changes nothing else.
`annotatedExternalCall` executes it in Lean, without delegating to CLean, when every
argument is a numeric value of the matching type. Pointer annotations return `none`.
Every other external function is passed to CLean's `CC.doExternalCall`.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Cminor

open CC

/-- `numericEvent v ty` encodes the numeric value `v` as an event value of annotation type `ty`,
failing on pointers, `Vundef`, and type mismatches. -/
def numericEvent : Val → ATyp → Option EventVal
  | .Vint n, .Tint => some (.EVint n)
  | .Vlong n, .Tlong => some (.EVlong n)
  | .Vfloat n, .Tfloat => some (.EVfloat n)
  | .Vsingle n, .Tsingle => some (.EVsingle n)
  | _, _ => none

/-- If `numericEvent v ty` returns `some ev`, then `ev` matches `v` at type `ty`
(`EventValMatch`). -/
theorem numeric_event_sound {ge : Senv} {value : Val} {type : ATyp} {event : EventVal}
    (h : numericEvent value type = some event) : EventValMatch ge event type value := by
  cases value <;> cases type <;> cases h <;> constructor

/-- If `numericEvent v ty` returns `some ev`, every event value matching `v` at `ty` equals `ev`. -/
theorem numeric_event_unique {ge : Senv} {value : Val} {type : ATyp}
    {event other : EventVal} (h : numericEvent value type = some event)
    (hother : EventValMatch ge other type value) : event = other := by
  cases hother <;> cases h <;> rfl

/-- `numericEvents vs tys` encodes each argument with its annotation type, requiring the lists to
have the same length. -/
def numericEvents : List Val → List ATyp → Option (List EventVal)
  | [], [] => some []
  | value :: values, type :: types => do
      let event ← numericEvent value type
      let events ← numericEvents values types
      pure (event :: events)
  | _, _ => none

/-- If `numericEvents vs tys` returns `some evs`, the event values match the arguments pointwise
(`EventValListMatch`). -/
theorem numeric_events_sound {ge : Senv} {values : List Val} {types : List ATyp}
    {events : List EventVal} (h : numericEvents values types = some events) :
    EventValListMatch ge events types values := by
  induction values generalizing types events with
  | nil =>
      cases types <;> cases h
      constructor
  | cons value values ih =>
      cases types with
      | nil => cases h
      | cons type types =>
          simp only [numericEvents, bind, Option.bind_eq_some_iff] at h
          obtain ⟨event, hevent, rest, hrest, h⟩ := h
          cases h
          exact .evl_match_cons _ _ _ _ _ _ (numeric_event_sound hevent) (ih hrest)

/-- If `numericEvents vs tys` returns `some evs`, every matching event list equals `evs`. -/
theorem numeric_events_unique {ge : Senv} {values : List Val} {types : List ATyp}
    {events other : List EventVal} (h : numericEvents values types = some events)
    (hother : EventValListMatch ge other types values) : events = other := by
  induction hother generalizing events with
  | evl_match_nil => cases h; rfl
  | evl_match_cons event type value rest types values hevent _ ih =>
      simp only [numericEvents, bind, Option.bind_eq_some_iff] at h
      obtain ⟨first, hfirst, tail, htail, h⟩ := h
      cases h
      rw [numeric_event_unique hfirst hevent, ih htail]

/-- `annotatedExternalCall` executes `EF_annot` with numeric arguments in Lean and delegates every
other external call to CLean's `CC.doExternalCall`. -/
def annotatedExternalCall : ExternalExecutor
  | .EF_annot _ text types, values, memory => do
      let events ← numericEvents values types
      pure ([.Event_annot text events], .Vundef, memory)
  | ef, values, memory => CC.doExternalCall ef values memory

/-- `annotatedExternalCall` is sound in every symbol environment: each result it accepts is
permitted by `externalCall`. -/
theorem annotated_external_call_sound [ExternalCalls] {ge : Senv} :
    Execution.ExternalExecutorSound annotatedExternalCall ge := by
  intro ef values memory trace value memory' h
  cases ef with
  | EF_annot kind text types =>
      simp only [annotatedExternalCall, bind, Option.bind_eq_some_iff] at h
      obtain ⟨events, hevents, h⟩ := h
      cases h
      exact ExtcallAnnotSem.intro _ _ _ _ (numeric_events_sound hevents)
  | _ => exact CC.doExternalCall_sound ge _ _ _ _ _ _ h

/-- The annotation executor `annotatedExternalCall` is sound for this stage's `Genv`. -/
theorem annotated_external_executor_sound [ExternalCalls] {ge : Genv} :
    ExternalExecutorSound annotatedExternalCall ge :=
  annotated_external_call_sound

/-- `annotatedExternalCall` agrees with `externalCall` in every symbol environment: each result it
accepts is the only permitted one, trace included. -/
theorem annotated_external_call_agrees [ExternalCalls] {ge : Senv} :
    Execution.ExternalExecutorAgrees annotatedExternalCall ge := by
  intro ef args memory trace value memory' otherTrace otherValue otherMemory h hother
  cases ef with
  | EF_annot kind text types =>
      simp only [annotatedExternalCall, bind, Option.bind_eq_some_iff] at h
      obtain ⟨events, hevents, h⟩ := h
      cases h
      cases hother with
      | intro _ _ _ other hmatch =>
          rw [numeric_events_unique hevents hmatch]
          exact ⟨rfl, rfl, rfl⟩
  | EF_malloc =>
      exact Execution.default_external_executor_agrees .EF_malloc _ _ _ _ _ _ _ _ h hother
  | EF_free =>
      exact Execution.default_external_executor_agrees .EF_free _ _ _ _ _ _ _ _ h hother
  | EF_memcpy size alignment =>
      exact Execution.default_external_executor_agrees (.EF_memcpy size alignment)
        _ _ _ _ _ _ _ _ h hother
  | EF_debug kind text types =>
      exact Execution.default_external_executor_agrees (.EF_debug kind text types)
        _ _ _ _ _ _ _ _ h hother
  | _ => simp [annotatedExternalCall, CC.doExternalCall] at h

end Quadrature.Cminor
