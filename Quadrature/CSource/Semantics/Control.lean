import Quadrature.CSource.Semantics.StoreTotal

/-!
# Deterministic control steps of the C machine

Expression evaluation may choose among exposed operands. Statement control,
function entry with nonvolatile parameters, and return from a function have
unique successors. These lemmas compose the expression proofs into complete
function executions.
-/

namespace Quadrature.CSource.C

open CC hiding State Cont Step
open SmallStep

/-- A nonvolatile C assignment also satisfies the shared Clight memory relation. -/
theorem AssignLoc.toClight {ge : ExpressionEnv} {type : Ty} {memory final : Mem}
    {block : Block} {offset : Integers.Ptrofs} {value result : Val}
    (hv : typeIsVolatile type = false)
    (h : AssignLoc ge type memory block offset .Full value E0 final result) :
    CC.AssignLoc ge.composites type memory block offset .Full value final := by
  cases h with
  | value _ _ _ hmode _ hstore => exact .value _ _ _ hmode hstore
  | volatile _ _ _ _ _ hvolatile _ => simp [hv] at hvolatile
  | copy _ _ _ _ hmode hsource hdest hdisjoint hload hstore =>
      exact .copy _ _ _ _ hmode (fun _ => Int.emod_eq_zero_of_dvd hsource)
        (fun _ => Int.emod_eq_zero_of_dvd hdest) hdisjoint hload hstore

/-- Binding nonvolatile parameters uses the same stores as Clight parameter binding. -/
theorem BindParameters.toClight {ge : ExpressionEnv} {locals : Env} {memory final : Mem}
    {params : List (Ident × Ty)} {args : List Val}
    (h : BindParameters ge locals memory params args final)
    (hv : ∀ param ∈ params, typeIsVolatile param.2 = false) :
    CC.BindParameters ge.composites locals memory params args final := by
  induction h with
  | nil => exact .nil _
  | cons memory name type params value values result block middle final hlocal hstore hrest ih =>
      exact .cons _ _ _ _ _ _ _ _ _ hlocal
        (hstore.toClight (hv _ (List.mem_cons_self ..)))
        (ih (fun param hparam => hv param (List.mem_cons_of_mem _ hparam)))

/-- Function entry is unique when parameter binding has no volatile accesses. -/
theorem FunctionEntry.determ {ge : ExpressionEnv} {function : Function} {args : List Val}
    {memory entered₁ entered₂ : Mem} {locals₁ locals₂ : Env}
    (hv : ∀ param ∈ function.fn_params, typeIsVolatile param.2 = false)
    (h₁ : FunctionEntry ge function args memory locals₁ entered₁)
    (h₂ : FunctionEntry ge function args memory locals₂ entered₂) :
    locals₁ = locals₂ ∧ entered₁ = entered₂ := by
  obtain ⟨allocated₁, ha₁, hb₁⟩ := h₁.allocated_and_bound
  obtain ⟨allocated₂, ha₂, hb₂⟩ := h₂.allocated_and_bound
  obtain ⟨rfl, rfl⟩ := CC.allocVariables_determ ha₁ _ _ ha₂
  exact ⟨rfl, CC.bindParameters_determ (hb₁.toClight hv) _ (hb₂.toClight hv)⟩

namespace SmallStep

variable [ExternalCalls]

/-- Two control transitions from the same statement have the same trace and successor. -/
theorem StmtStep.statement_determ {ge : GlobalEnv} {function : Function} {statement : Stmt}
    {cont : Cont} {locals : Env} {memory : Mem} {trace₁ trace₂ : Trace} {next₁ next₂ : State}
    (h₁ : StmtStep ge (.statement function statement cont locals memory) trace₁ next₁)
    (h₂ : StmtStep ge (.statement function statement cont locals memory) trace₂ next₂) :
    trace₁ = trace₂ ∧ next₁ = next₂ := by
  cases h₁ <;> cases h₂
  all_goals simp_all [Cont.IsCall]

/-- Consuming a computed expression value has a unique control transition. -/
theorem StmtStep.value_determ {ge : GlobalEnv} {function : Function} {value : Val} {type : Ty}
    {cont : Cont} {locals : Env} {memory : Mem} {trace₁ trace₂ : Trace} {next₁ next₂ : State}
    (h₁ : StmtStep ge (.expression function (.Eval value type) cont locals memory) trace₁ next₁)
    (h₂ : StmtStep ge (.expression function (.Eval value type) cont locals memory) trace₂ next₂) :
    trace₁ = trace₂ ∧ next₁ = next₂ := by
  cases h₁ <;> cases h₂
  all_goals simp_all

/-- Prepend a statement control step. -/
theorem Total.statement {ge : GlobalEnv} {post : State → Prop} {function : Function}
    {statement : Stmt} {cont : Cont} {locals : Env} {memory : Mem} {next : State}
    (hstep : StmtStep ge (.statement function statement cont locals memory) E0 next)
    (hnext : Total ge post next) :
    Total ge post (.statement function statement cont locals memory) := by
  apply Total.single (.inr hstep) ?_ hnext
  intro trace result h
  rcases h with h | h
  · cases h
  · exact ⟨(hstep.statement_determ h).1.symm, (hstep.statement_determ h).2.symm⟩

/-- Prepend the control step that consumes a computed expression value. -/
theorem Total.value {ge : GlobalEnv} {post : State → Prop} {function : Function}
    {value : Val} {type : Ty} {cont : Cont} {locals : Env} {memory : Mem} {next : State}
    (hstep : StmtStep ge (.expression function (.Eval value type) cont locals memory) E0 next)
    (hnext : Total ge post next) :
    Total ge post (.expression function (.Eval value type) cont locals memory) := by
  apply Total.single (.inr hstep) ?_ hnext
  intro trace result h
  rcases h with h | h
  · exact False.elim (h.not_value)
  · exact ⟨(hstep.value_determ h).1.symm, (hstep.value_determ h).2.symm⟩

/-- Enter a function whose allocation and nonvolatile parameter binding have been proved. -/
theorem Total.internal {ge : GlobalEnv} {post : State → Prop} {function : Function}
    {args : List Val} {cont : Cont} {locals : Env} {memory entered : Mem}
    (hv : ∀ param ∈ function.fn_params, typeIsVolatile param.2 = false)
    (hentry : FunctionEntry ge.expressionEnv function args memory locals entered)
    (hbody : Total ge post (.statement function function.fn_body cont locals entered)) :
    Total ge post (.call (.Internal function) args cont memory) := by
  obtain ⟨allocated, halloc, hbound⟩ := hentry.allocated_and_bound
  apply Total.single
    (.inr (.internal _ _ _ _ _ _ _ hentry.names_unique halloc hbound)) ?_ hbody
  intro trace result hstep
  rcases hstep with hstep | hstep
  · cases hstep
  · cases hstep with
    | internal _ _ _ _ _ _ _ hnames halloc' hbound' =>
        obtain ⟨rfl, rfl⟩ := hentry.determ hv ⟨hnames, ⟨_, halloc', hbound'⟩⟩
        exact ⟨rfl, rfl⟩

omit [ExternalCalls] in
/-- Returning through a function boundary retains that boundary's continuation. -/
theorem Cont.callCont_eq {cont : Cont} (h : cont.IsCall) : cont.callCont = cont := by
  cases cont <;> simp_all [Cont.IsCall, Cont.callCont]

end SmallStep
end Quadrature.CSource.C
