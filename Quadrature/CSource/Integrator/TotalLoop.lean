import Quadrature.CSource.Integrator.TotalSteps

/-!
# Termination and result of every C loop execution

The induction in `integrator_loop_total` consumes one table cell per
iteration. It covers every reduction order of each iteration and rules
out both stuck executions and infinite executions.
-/

namespace Quadrature.CSource.C

open CC hiding State Cont Step
open FloatLib.Floats.Formats.BinaryInterchange SmallStep

variable [ExternalCalls]

/-- Every execution of the remaining loop terminates with the binary64 left fold and preserves
all memory outside the two updated locals. -/
theorem integrator_loop_total (ge : GlobalEnv) (frame : IntegratorFrame) (memory : Mem)
    (ctx : SourceTableFunctions ge) (callback : Val) (callee : FunDef)
    (f : Floats.Float → Floats.Float) (n : Nat) (hn : n ≤ 10)
    (terms : List (Floats.Float × Floats.Float)) (i : Nat) (accumulator : Floats.Float)
    (hlen : i + terms.length = n)
    (state : IntegratorState frame memory callback n i accumulator)
    (separate : TableSeparation frame ctx.nodes ctx.weights)
    (contract : CallbackCorrect ge callback callee f)
    (cells : Binary64.Clight.TableCells memory ctx.nodes ctx.weights n i terms)
    (function : Function) (cont : Cont) :
    Total ge (fun result => ∃ final,
      result = .statement function .Sskip cont frame.locals final ∧
      IntegratorState frame final callback n n
        ((terms.map fun term => Model.mul term.1 (f term.2)).foldl Model.add accumulator) ∧
      LoopMemory frame memory final)
      (.statement function integratorLoop cont frame.locals memory) := by
  induction terms generalizing memory i accumulator with
  | nil =>
      have hi : i = n := by simpa using hlen
      subst i
      apply Total.statement (.for_test _ _ _ _ _ _ _)
      apply ((integrator_guard_value ge frame memory callback n n accumulator hn hn state).total
        function _).bind
      rintro _ rfl
      refine Total.value (.for_false _ _ _ _ _ _ _ _ _ ?_) ?_
      · simp only [Nat.lt_irrefl, decide_false]
        rfl
      · exact .done ⟨memory, rfl, state, .refl _ _⟩
  | cons term terms ih =>
      obtain ⟨weight, node⟩ := term
      obtain ⟨hweight, hnode, hrest⟩ := cells
      have hi : i < n := by simp only [List.length_cons] at hlen; omega
      have hi10 : i ≤ 10 := by omega
      apply Total.statement (.for_test _ _ _ _ _ _ _)
      apply ((integrator_guard_value ge frame memory callback n i accumulator hn hi10
        state).total function _).bind
      rintro _ rfl
      refine Total.value (.for_true _ _ _ _ _ _ _ _ _ ?_) ?_
      · simp only [hi, decide_true]
        rfl
      · apply (integrator_update_total ge frame memory ctx callback callee f n i
          accumulator weight node hn hi10 state contract hweight hnode function _).bind
        rintro _ ⟨updated, rfl, updatedState, updatedMemory⟩
        apply Total.statement (.for_increment _ _ _ _ _ _ _ _ (.inl rfl))
        apply (integrator_increment_total ge frame updated callback n i
          (Model.add accumulator (Model.mul weight (f node))) updatedState function _).bind
        rintro _ ⟨incremented, rfl, incrementedState, incrementedMemory⟩
        have iterationMemory := updatedMemory.trans incrementedMemory
        apply Total.statement (.for_repeat _ _ _ _ _ _ _)
        apply (ih incremented (i + 1) (Model.add accumulator (Model.mul weight (f node)))
          (by simp only [List.length_cons] at hlen; omega) incrementedState
          (iterationMemory.table_cells separate hrest)).mono
        rintro result ⟨final, rfl, finalState, finalMemory⟩
        exact ⟨final, rfl, finalState, iterationMemory.trans finalMemory⟩

end Quadrature.CSource.C
