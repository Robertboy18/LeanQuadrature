import Quadrature.CSource.Integrator.Steps

/-!
# Execution of the original source-C loop

`integrator_loop` proves, by induction on the remaining table cells, that the
source `for` loop executes every remaining sample and terminates with the exact
FloatLib fold, for at most ten samples. Each iteration composes the guard, the
nested calls, the compound assignment and the post-increment from
`Quadrature.CSource.Integrator.Steps`. The initial local state, table
separation, symbol lookups and callback contract are explicit hypotheses.
Entry and exit are handled in `Quadrature.CSource.Integrator.Function`.
-/

namespace Quadrature.CSource.C

open CC FloatLib.Floats.Formats.BinaryInterchange

variable [ExternalCalls]

/-- Given `IntegratorState` at index `i` with accumulator `acc`, the table cells of the remaining
`terms` from index `i` (with `i + terms.length = n ≤ 10`), `TableSeparation` and the callback
contract, `integratorLoop` executes normally. It ends in `IntegratorState` at index `n` with
accumulator `foldl Model.add acc (terms.map (w, x) ↦ Model.mul w (f x))` and `LoopMemory`. -/
theorem integrator_loop (ge : GlobalEnv) (frame : IntegratorFrame) (memory : Mem)
    (ctx : SourceTableFunctions ge) (callback : Val) (function : FunDef)
    (f : Floats.Float → Floats.Float) (n : Nat) (hn : n ≤ 10)
    (terms : List (Floats.Float × Floats.Float)) (i : Nat) (accumulator : Floats.Float)
    (hlen : i + terms.length = n)
    (state : IntegratorState frame memory callback n i accumulator)
    (separate : TableSeparation frame ctx.nodes ctx.weights)
    (contract : SourceCallbackContract ge callback function f)
    (cells : Binary64.Clight.TableCells memory ctx.nodes ctx.weights n i terms) :
    ∃ final,
      ExecStmt ge frame.locals memory integratorLoop E0 final .normal ∧
      IntegratorState frame final callback n n
        ((terms.map fun term => Model.mul term.1 (f term.2)).foldl Model.add accumulator) ∧
      LoopMemory frame memory final := by
  induction terms generalizing memory i accumulator with
  | nil =>
    have hi : i = n := by simpa using hlen
    subst i
    refine ⟨memory, ?_, state, .refl frame memory⟩
    apply ExecStmt.for_false
    · exact integrator_guard ge frame memory callback n n accumulator hn hn state
    · simp only [Nat.lt_irrefl, decide_false]
      rfl
  | cons term terms ih =>
    obtain ⟨weight, node⟩ := term
    obtain ⟨hweight, hnode, hrest⟩ := cells
    have hi : i < n := by simp only [List.length_cons] at hlen; omega
    have hi10 : i ≤ 10 := by omega
    obtain ⟨updated, hupdate, updatedState, updatedMemory⟩ :=
      integrator_update ge frame memory ctx callback function f n i accumulator weight node
        hn hi10 state contract hweight hnode
    obtain ⟨incremented, hincrement, incrementedState, incrementedMemory⟩ :=
      integrator_increment ge frame updated callback n i
        (Model.add accumulator (Model.mul weight (f node))) updatedState
    have iterationMemory := updatedMemory.trans incrementedMemory
    obtain ⟨final, hloop, finalState, finalMemory⟩ :=
      ih incremented (i + 1) (Model.add accumulator (Model.mul weight (f node)))
        (by simp only [List.length_cons] at hlen; omega)
        incrementedState (iterationMemory.table_cells separate hrest)
    refine ⟨final, ?_, finalState, iterationMemory.trans finalMemory⟩
    apply ExecStmt.for_loop (t₁ := E0) (t₂ := E0) (t₃ := E0) (t₄ := E0)
      (m₁ := memory) (m₂ := updated) (m₃ := incremented) (out₁ := .normal)
    · exact integrator_guard ge frame memory callback n i accumulator hn hi10 state
    · simp only [hi, decide_true]
      rfl
    · exact hupdate
    · exact .normal
    · exact hincrement
    · exact hloop

end Quadrature.CSource.C
