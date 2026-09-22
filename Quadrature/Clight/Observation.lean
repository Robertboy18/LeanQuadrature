import Quadrature.Clight.Execution

/-!
# Determined executions with observable annotations

Vocabulary: see `Quadrature.Clight.Execution`. An `Event_annot` event is emitted
by CompCert's annotation builtin, and the program itself fixes its payload, so
the next state cannot depend on the environment. This is unlike a system call
or a volatile load, whose result the environment chooses. A finite run whose
trace consists of annotations therefore determines every reachable prefix and
rules out infinite execution, which extends the silent-execution argument to
callers that expose their numerical result in the trace.
-/

namespace Quadrature.Binary64.Clight

/-- Every event of `trace` is an `Event_annot text args`. The definition says nothing about
payloads. That the program fixes them is a property of `Step`, expressed by the `annot` case of
`CC.MatchTraces` and used in `annotation_match_eq`. -/
def AnnotationTrace (trace : CC.Trace) : Prop :=
  ∀ event ∈ trace, ∃ text args, event = CC.Event.Event_annot text args

/-- The empty trace is an annotation trace. -/
theorem annotation_trace_nil : AnnotationTrace CC.E0 := by
  simp [AnnotationTrace, CC.E0]

/-- A single annotation event is an annotation trace. -/
theorem annotation_trace_singleton (text : String) (args : List CC.EventVal) :
    AnnotationTrace [.Event_annot text args] := by
  simp [AnnotationTrace]

/-- A concatenation is an annotation trace exactly when both parts are. -/
theorem annotation_trace_append {left right : CC.Trace} :
    AnnotationTrace (CC.Eapp left right) ↔ AnnotationTrace left ∧ AnnotationTrace right := by
  simp [AnnotationTrace, CC.Eapp, or_imp, forall_and]

/-- Two traces related by `CC.MatchTraces` are equal when the left one contains only
annotations. The syscall and volatile cases, where the environment may choose the result, are
excluded by the hypothesis. -/
theorem annotation_match_eq {ge : CC.Senv} {left right : CC.Trace}
    (h : AnnotationTrace left) (hmatch : CC.MatchTraces ge left right) : left = right := by
  cases hmatch with
  | nil => rfl
  | syscall => simp [AnnotationTrace] at h
  | vload => simp [AnnotationTrace] at h
  | vstore => simp [AnnotationTrace] at h
  | annot => rfl

/-- Two runs compose end to end, and their traces concatenate with `CC.Eapp`. -/
theorem star_trans {R : CC.State → CC.Trace → CC.State → Prop}
    {start middle finish : CC.State} {left right : CC.Trace}
    (hleft : CC.Star R start left middle) (hright : CC.Star R middle right finish) :
    CC.Star R start (CC.Eapp left right) finish := by
  induction hleft with
  | refl => simpa [CC.Eapp, CC.E0] using hright
  | step start first next rest middle total hstep _ htrace ih =>
    exact .step _ _ _ _ _ _ hstep (ih hright) (by simp [htrace, CC.Eapp, List.append_assoc])

/-- Assume a run from `start` to a stuck state `finish` whose trace `total` contains only
annotations, and deterministic external calls. Then every run from `start` with trace `trace`
extends to `finish` with some `remaining` trace such that `trace ++ remaining = total`. -/
theorem annotation_execution_prefix [calls : CC.ExternalCalls]
    [CC.ExternalCallsDeterministic calls] (program : CC.Program)
    {start finish : CC.State} {total : CC.Trace}
    (hrun : CC.Star (CC.Step2 program.globalenv) start total finish)
    (hannotations : AnnotationTrace total)
    (hstop : ∀ trace state, ¬ CC.Step2 program.globalenv finish trace state) :
    ∀ {trace state}, CC.Star (CC.Step2 program.globalenv) start trace state →
      ∃ remaining, CC.Eapp trace remaining = total ∧
        CC.Star (CC.Step2 program.globalenv) state remaining finish := by
  induction hrun with
  | refl state =>
    intro trace reached hprefix
    cases hprefix with
    | refl => exact ⟨CC.E0, rfl, .refl _⟩
    | step _ first next _ _ _ hstep _ _ => exact (hstop first next hstep).elim
  | step start first next rest finish total hstep htail htrace ih =>
    have hparts := annotation_trace_append.mp (htrace ▸ hannotations)
    intro trace reached hprefix
    cases hprefix with
    | refl => exact ⟨total, rfl, .step _ _ _ _ _ _ hstep htail htrace⟩
    | step _ otherFirst otherNext otherRest _ _ hfirst hrest hprefixTrace =>
      have hdet := CC.step_determ (CC.entryDeterm_functionEntry2 program.globalenv)
        (CC.program_symbolsInjective program) hstep hfirst
      have heq := annotation_match_eq hparts.1 hdet.1
      have hnext := hdet.2 heq
      subst otherNext
      obtain ⟨remaining, hremaining, hfinish⟩ := ih hparts.2 hstop hrest
      refine ⟨remaining, ?_, hfinish⟩
      simpa only [hprefixTrace, ← heq, CC.Eapp, List.append_assoc, htrace] using
        congrArg (CC.Eapp first) hremaining

/-- Under the hypotheses of `annotation_execution_prefix`, any run from `start` that reaches a
stuck state has trace `total` and ends in `finish`. -/
theorem annotation_execution_unique [calls : CC.ExternalCalls]
    [CC.ExternalCallsDeterministic calls] (program : CC.Program)
    {start finish reached : CC.State} {total trace : CC.Trace}
    (hrun : CC.Star (CC.Step2 program.globalenv) start total finish)
    (hannotations : AnnotationTrace total)
    (hstop : ∀ t s, ¬ CC.Step2 program.globalenv finish t s)
    (hother : CC.Star (CC.Step2 program.globalenv) start trace reached)
    (hotherStop : ∀ t s, ¬ CC.Step2 program.globalenv reached t s) :
    trace = total ∧ reached = finish := by
  obtain ⟨remaining, htrace, hrest⟩ :=
    annotation_execution_prefix program hrun hannotations hstop hother
  cases hrest with
  | refl => exact ⟨by simpa [CC.Eapp, CC.E0] using htrace, rfl⟩
  | step _ first next _ _ _ hstep _ _ => exact (hotherStop first next hstep).elim

/-- Under the hypotheses of `annotation_execution_prefix`, no infinite sequence of steps starts
at `start`. -/
theorem annotation_execution_not_infinite [calls : CC.ExternalCalls]
    [CC.ExternalCallsDeterministic calls] (program : CC.Program)
    {start finish : CC.State} {total : CC.Trace}
    (hrun : CC.Star (CC.Step2 program.globalenv) start total finish)
    (hannotations : AnnotationTrace total)
    (hstop : ∀ trace state, ¬ CC.Step2 program.globalenv finish trace state) :
    ∀ (states : Nat → CC.State) (traces : Nat → CC.Trace), states 0 = start →
      (∀ n, CC.Step2 program.globalenv (states n) (traces n) (states (n + 1))) →
      False := by
  induction hrun with
  | refl state =>
    intro states traces hstart hsteps
    have hfirst := hsteps 0
    rw [hstart] at hfirst
    exact hstop _ _ hfirst
  | step start first next rest finish total hstep _ htrace ih =>
    have hparts := annotation_trace_append.mp (htrace ▸ hannotations)
    intro states traces hstart hsteps
    have hfirst := hsteps 0
    rw [hstart] at hfirst
    have hdet := CC.step_determ (CC.entryDeterm_functionEntry2 program.globalenv)
      (CC.program_symbolsInjective program) hstep hfirst
    have hnext := hdet.2 (annotation_match_eq hparts.1 hdet.1)
    exact ih hparts.2 hstop (fun n => states (n + 1)) (fun n => traces (n + 1))
      hnext.symm (fun n => hsteps (n + 1))

end Quadrature.Binary64.Clight
