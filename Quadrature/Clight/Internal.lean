import Quadrature.Clight.Execution

/-!
# Clight executions that need no external-call assumption

`InternalProgram` checks that every function uses structured statements and
makes no builtin or external call. `InternalState.step` preserves this
property during execution. Consequently, `internal_execution_prefix` and
`internal_execution_accessible` need no determinism hypothesis about the
external environment.

The check permits indirect calls: every function in the global environment
must satisfy the same condition. It rejects `goto`, labels and switches,
which the selected quadrature functions do not use.
-/

namespace Quadrature.Binary64.Clight

open CC

/-- Structured statements without builtins. Clight expressions have no calls or side effects. -/
def InternalStmt : CC.Stmt → Bool
  | .Sskip | .Sassign .. | .Sset .. | .Scall .. | .Sbreak | .Scontinue | .Sreturn _ => true
  | .Ssequence first last | .Sloop first last => InternalStmt first && InternalStmt last
  | .Sifthenelse _ yes no => InternalStmt yes && InternalStmt no
  | _ => false

/-- A global is either data or an internal function using the structured fragment. -/
def InternalGlobal : GlobDef FunDef Ty → Bool
  | .Gvar _ => true
  | .Gfun (.Internal function) => InternalStmt function.fn_body
  | .Gfun (.External ..) => false

/-- Every callable definition in the program belongs to the internal fragment. -/
def InternalProgram (program : Program) : Prop :=
  ∀ definition ∈ program.prog_defs, InternalGlobal definition.2 = true

/-- Suspended statements also belong to the internal fragment. -/
def InternalCont : CC.Cont → Prop
  | .Kstop => True
  | .Kseq statement next => InternalStmt statement = true ∧ InternalCont next
  | .Kloop1 body increment next | .Kloop2 body increment next =>
      InternalStmt body = true ∧ InternalStmt increment = true ∧ InternalCont next
  | .Kswitch next | .Kcall _ _ _ _ next => InternalCont next

/-- The next statement or function, and all suspended statements, are internal. -/
def InternalState : CC.State → Prop
  | .State _ statement next _ _ _ => InternalStmt statement = true ∧ InternalCont next
  | .Callstate (.Internal function) _ next _ =>
      InternalStmt function.fn_body = true ∧ InternalCont next
  | .Callstate (.External ..) _ _ _ => False
  | .Returnstate _ next _ => InternalCont next

/-- Removing statement continuations preserves the internal-fragment invariant. -/
theorem InternalCont.callCont {cont : CC.Cont} (h : InternalCont cont) :
    InternalCont (CC.callCont cont) := by
  induction cont with
  | Kstop => trivial
  | Kseq _ _ ih => exact ih h.2
  | Kloop1 _ _ _ ih | Kloop2 _ _ _ ih => exact ih h.2.2
  | Kswitch _ ih => exact ih h
  | Kcall => exact h

private theorem internal_addGlobals (ge : Genv FunDef Ty)
    (definitions : List (Ident × GlobDef FunDef Ty))
    (hge : ∀ block definition, ge.genv_defs.get block = some definition →
      InternalGlobal definition = true)
    (hdefinitions : ∀ definition ∈ definitions, InternalGlobal definition.2 = true) :
    ∀ block definition, (Genv.addGlobals ge definitions).genv_defs.get block = some definition →
      InternalGlobal definition = true := by
  induction definitions generalizing ge with
  | nil => exact hge
  | cons first rest ih =>
      apply ih (Genv.addGlobal ge first)
      · intro block definition hlookup
        change (ge.genv_defs.set ge.genv_next first.2).get block = some definition at hlookup
        by_cases hblock : block = ge.genv_next
        · subst block
          rw [PTree.gss] at hlookup
          cases Option.some.inj hlookup
          exact hdefinitions first List.mem_cons_self
        · rw [PTree.gso _ _ _ _ (Ne.symm hblock)] at hlookup
          exact hge block definition hlookup
      · intro definition hmem
        exact hdefinitions definition (List.mem_cons_of_mem _ hmem)

/-- A successful indirect function lookup in an internal program selects an internal body. -/
theorem InternalProgram.findFunct {program : Program} (h : InternalProgram program)
    {pointer : Val} {definition : FunDef}
    (hlookup : Genv.findFunct program.globalenv.genv_genv pointer = some definition) :
    ∃ function, definition = .Internal function ∧ InternalStmt function.fn_body = true := by
  have hdefs : ∀ block value,
      program.globalenv.genv_genv.genv_defs.get block = some value →
        InternalGlobal value = true :=
    internal_addGlobals _ _ (by simp [Genv.emptyGenv, PTree.gempty]) h
  cases pointer <;> simp only [Genv.findFunct] at hlookup
  all_goals try contradiction
  rename_i block offset
  split at hlookup
  · unfold Genv.findFunctPtr Genv.findDef at hlookup
    split at hlookup
    · rename_i function hfunction
      cases Option.some.inj hlookup
      have hinternal := hdefs block (.Gfun definition) hfunction
      cases definition with
      | Internal body => exact ⟨body, rfl, hinternal⟩
      | External => exact (Bool.false_ne_true hinternal).elim
    · contradiction
  · contradiction

/-- Each transition of an internal program keeps its state in the internal fragment. -/
theorem InternalState.step [ExternalCalls] {program : Program}
    (hprogram : InternalProgram program) {state next : CC.State} {trace : Trace}
    (hstate : InternalState state) (hstep : Step2 program.globalenv state trace next) :
    InternalState next := by
  cases hstep <;>
    simp only [InternalState, InternalStmt, InternalCont, Bool.and_eq_true,
      Bool.false_eq_true, false_and] at *
  all_goals try exact ⟨trivial, hstate.2⟩
  all_goals try exact hstate.2
  all_goals try exact hstate
  case call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hlookup _ =>
    obtain ⟨function, rfl, hinternal⟩ := hprogram.findFunct hlookup
    exact ⟨hinternal, hstate.2⟩
  case seq => exact ⟨hstate.1.1, hstate.1.2, hstate.2⟩
  case continue_seq => exact ⟨trivial, hstate.2.2⟩
  case break_seq => exact ⟨trivial, hstate.2.2⟩
  case ifthenelse =>
    refine ⟨?_, hstate.2⟩
    split <;> first | exact hstate.1.1 | exact hstate.1.2
  case loop => exact ⟨hstate.1.1, hstate.1.1, hstate.1.2, hstate.2⟩
  case skip_or_continue_loop1 =>
    exact ⟨hstate.2.2.1, hstate.2.1, hstate.2.2⟩
  case break_loop1 => exact ⟨trivial, hstate.2.2.2⟩
  case skip_loop2 => exact ⟨⟨hstate.2.1, hstate.2.2.1⟩, hstate.2.2.2⟩
  case break_loop2 => exact ⟨trivial, hstate.2.2.2⟩
  case return_0 => exact hstate.2.callCont
  case return_1 => exact hstate.2.callCont
  case returnstate => exact ⟨trivial, hstate⟩

private abbrev emptyCalls : ExternalCalls :=
  ⟨fun _ _ _ _ _ _ _ _ => False, fun _ _ _ _ _ _ _ _ => False⟩

private instance : ExternalCallsDeterministic emptyCalls :=
  ⟨fun _ _ _ => ⟨fun _ _ _ _ _ _ _ _ h => h.elim, fun _ _ _ _ _ h => h.elim⟩,
   fun _ _ _ => ⟨fun _ _ _ _ _ _ _ _ h => h.elim, fun _ _ _ _ _ h => h.elim⟩⟩

/-- An internal transition does not depend on the interpretation of external calls. -/
theorem InternalState.change_external {calls other : ExternalCalls}
    {ge : CGenv} {state next : CC.State} {trace : Trace}
    (hstate : InternalState state) (hstep : @Step2 calls ge state trace next) :
    @Step2 other ge state trace next := by
  cases hstep <;>
    simp only [InternalState, InternalStmt, Bool.false_eq_true, false_and] at hstate
  all_goals constructor <;> assumption

/-- Internal transitions have one successor and no observable events, under any environment. -/
theorem InternalState.determ [ExternalCalls] (program : Program)
    {state first last : CC.State} {left right : Trace} (hstate : InternalState state)
    (hfirst : Step2 program.globalenv state left first)
    (hlast : Step2 program.globalenv state right last) :
    left = E0 ∧ right = E0 ∧ first = last := by
  have hleft : left = E0 := by
    cases hfirst <;> simp_all [InternalState, InternalStmt]
  have hdeterm := @CC.step_determ emptyCalls inferInstance program.globalenv _
    (CC.entryDeterm_functionEntry2 program.globalenv) (CC.program_symbolsInjective program)
    state left first right last (hstate.change_external hfirst) (hstate.change_external hlast)
  have hright : right = E0 := matchTraces_empty (hleft ▸ hdeterm.1)
  exact ⟨hleft, hright, hdeterm.2 (hleft.trans hright.symm)⟩

/-- Every run of a closed internal call is a silent prefix of its proved terminating run. -/
theorem internal_execution_prefix [ExternalCalls] (program : Program)
    (hprogram : InternalProgram program) {start finish : CC.State}
    (hstart : InternalState start)
    (hrun : StarE0 (Step2 program.globalenv) start finish)
    (hstop : ∀ trace state, ¬ Step2 program.globalenv finish trace state)
    {trace : Trace} {state : CC.State}
    (hprefix : Star (Step2 program.globalenv) start trace state) :
    trace = E0 ∧ StarE0 (Step2 program.globalenv) state finish := by
  induction hrun generalizing trace state with
  | refl state =>
      cases hprefix with
      | refl => exact ⟨rfl, .refl _⟩
      | step _ trace next _ _ _ hstep _ _ => exact (hstop trace next hstep).elim
  | step start next finish hstep hrest ih =>
      cases hprefix with
      | refl => exact ⟨rfl, .step _ _ _ hstep hrest⟩
      | step _ first otherNext rest _ _ hfirst htail htrace =>
          obtain ⟨_, hfirstTrace, hnext⟩ := hstart.determ program hstep hfirst
          subst otherNext
          obtain ⟨htailTrace, hremaining⟩ := ih (hstart.step hprogram hstep) hstop htail
          exact ⟨by simpa [hfirstTrace, htailTrace, Eapp, E0] using htrace, hremaining⟩

/-- No infinite transition sequence starts from a proved terminating internal call. -/
theorem internal_execution_accessible [ExternalCalls] (program : Program)
    (hprogram : InternalProgram program) {start finish : CC.State}
    (hstart : InternalState start)
    (hrun : StarE0 (Step2 program.globalenv) start finish)
    (hstop : ∀ trace state, ¬ Step2 program.globalenv finish trace state) :
    Acc (fun next state => ∃ trace, Step2 program.globalenv state trace next) start := by
  induction hrun with
  | refl state => exact .intro _ (fun next ⟨trace, hstep⟩ => (hstop trace next hstep).elim)
  | step start next finish hstep _ ih =>
      refine .intro _ (fun other ⟨trace, hother⟩ => ?_)
      obtain ⟨_, _, rfl⟩ := hstart.determ program hstep hother
      exact ih (hstart.step hprogram hstep) hstop

end Quadrature.Binary64.Clight
