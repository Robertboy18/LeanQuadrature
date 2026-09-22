import Quadrature.CSource.Integrator.ReadOnly
import Quadrature.CSource.Integrator.Steps
import Quadrature.CSource.Semantics.ScalarReduction

/-!
# Total correctness of the loop's two updates

`integrator_increment_total` follows the complete C reduction of `i++`.
`integrator_update_total` permits every operand order in the compound
assignment, including orders that call the callback before looking up the
weight. Both preserve the loop's local and table invariants.
-/

namespace Quadrature.CSource.C

open CC hiding State Cont Step
open Binary64.ClightSource FloatLib.Floats.Formats.BinaryInterchange SmallStep

variable [ExternalCalls]

/-- Every execution of `i++;` terminates with the successor index and preserves other blocks. -/
theorem integrator_increment_total (ge : GlobalEnv) (frame : IntegratorFrame) (memory : Mem)
    (callback : Val) (n i : Nat) (accumulator : Floats.Float)
    (state : IntegratorState frame memory callback n i accumulator)
    (function : Function) (cont : Cont) :
    Total ge (fun result => ∃ final,
      result = .statement function .Sskip cont frame.locals final ∧
      IntegratorState frame final callback n (i + 1) accumulator ∧
      LoopMemory frame memory final)
      (.statement function integratorIncrement cont frame.locals memory) := by
  obtain ⟨final, hstore⟩ : ∃ final, Mem.store .Mint32 memory frame.index 0
      (.Vint (Integers.Int.repr (i + 1))) = some final := by
    simp only [Mem.store, state.index_writable, ite_true]
    exact ⟨_, rfl⟩
  have hadd : Cop.semBinaryOperation ge.composites .Oadd
      (.Vint (Integers.Int.repr i)) tint (.Vint Integers.Int.one) tint memory =
      some (.Vint (Integers.Int.repr (i + 1))) := by
    change some (Val.Vint (Integers.Int.add (Integers.Int.repr i) (Integers.Int.repr 1))) = _
    rw [int_repr_add_one]
  apply Total.statement (.do_start _ _ _ _ _)
  apply (ExpressionReduction.postincr_local (ge := ge) (block := frame.index)
    (by rfl) .incr).total
  apply (ExpressionReduction.postincr_location (block := frame.index)
    (offset := Integers.Ptrofs.zero) (type := tint) .incr rfl
    (.value .Mint32 _ rfl rfl state.index_load)).total
  apply ((ExpressionReduction.binop (type := tint) hadd).assign_right
    frame.index Integers.Ptrofs.zero .Full tint |>.comma
      (.Eval (.Vint (Integers.Int.repr i)) tint) tint).total
  apply ((ExpressionReduction.assign (ge := ge) (block := frame.index)
    (offset := Integers.Ptrofs.zero) (type := tint) (rhsType := tint)
    (rhs := .Vint (Integers.Int.repr (i + 1))) rfl rfl rfl hstore).comma
      (.Eval (.Vint (Integers.Int.repr i)) tint) tint).total
  apply (ExpressionReduction.comma_value _ _ _ _ rfl).total
  apply Total.value (.do_finish _ _ _ _ _ _)
  exact .done ⟨final, rfl, state.store_index hstore, .of_store hstore (.inl rfl)⟩

/-- Every execution of the accumulator update returns the same rounded sum, while permitting
different allocation histories for the nested calls. -/
theorem integrator_update_total (ge : GlobalEnv) (frame : IntegratorFrame) (memory : Mem)
    (ctx : SourceTableFunctions ge) (callback : Val) (callee : FunDef)
    (f : Floats.Float → Floats.Float) (n i : Nat) (accumulator weight node : Floats.Float)
    (hn : n ≤ 10) (hi : i ≤ 10)
    (state : IntegratorState frame memory callback n i accumulator)
    (contract : CallbackCorrect ge callback callee f)
    (hweight : Mem.load .Mfloat64 memory ctx.weights
      (8 * Binary64.Clight.tableOffset n i : Nat) = some (.Vfloat weight))
    (hnode : Mem.load .Mfloat64 memory ctx.nodes
      (8 * Binary64.Clight.tableOffset n i : Nat) = some (.Vfloat node))
    (function : Function) (cont : Cont) :
    Total ge (fun result => ∃ final,
      result = .statement function .Sskip cont frame.locals final ∧
      IntegratorState frame final callback n i
        (Model.add accumulator (Model.mul weight (f node))) ∧
      LoopMemory frame memory final)
      (.statement function integratorUpdate cont frame.locals memory) := by
  have heval : StoreExpr ge frame.locals memory frame.accumulator Integers.Ptrofs.zero tdouble
      (.Vfloat (Model.add accumulator (Model.mul weight (f node))))
      (.Eassignop .Oadd (.Evar _s tdouble) weightedSample tdouble tdouble) := by
    apply StoreExpr.compound (old := .Vfloat accumulator)
      (rhs := .Vfloat (Model.mul weight (f node)))
      (combined := .Vfloat (Model.add accumulator (Model.mul weight (f node))))
    · exact .var_local _ _ _ rfl
    · exact weighted_sample_read_eval ge frame memory ctx callback callee f n i
        accumulator weight node hn hi state contract hweight hnode
    · rfl
    · intro current hmemory
      exact .value .Mfloat64 _ rfl rfl (hmemory.load state.accumulator_load)
    · intro current _
      rfl
    · intro current _
      rfl
  have writable : ∀ current, CallMemory memory current →
      ∃ final, Mem.storev .Mfloat64 current (.Vptr frame.accumulator Integers.Ptrofs.zero)
        (.Vfloat (Model.add accumulator (Model.mul weight (f node)))) = some final := by
    intro current hmemory
    change ∃ final, Mem.store .Mfloat64 current frame.accumulator 0 _ = some final
    simp only [Mem.store, (state.after_call hmemory).accumulator_writable, ite_true]
    exact ⟨_, rfl⟩
  apply Total.statement (.do_start _ _ _ _ _)
  apply (heval.total (.refl _) rfl rfl writable function _).bind
  rintro result ⟨before, final, hmemory, hstore, rfl⟩
  apply Total.value (.do_finish _ _ _ _ _ _)
  exact .done ⟨final, rfl, (state.after_call hmemory).store_accumulator hstore,
    (LoopMemory.of_call frame hmemory).trans (.of_store hstore (.inr rfl))⟩

end Quadrature.CSource.C
