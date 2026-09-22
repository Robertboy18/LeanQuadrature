import Quadrature.CSource.Integrator.Calls
import Quadrature.CSource.Integrator.Memory

/-!
# Guard, accumulator update, and increment in the original C loop

`integrator_guard` evaluates the test `i < n`, `integrator_update` executes
`s += gauss_weight(i, n) * f(gauss_point(i, n));` with its three nested calls,
the separately rounded multiply and add, and a successful store to the
accumulator, and `integrator_increment` executes `i++` and stores the next
signed index. Each memory effect satisfies `LoopMemory`, so the table cells
and the other locals survive.
-/

namespace Quadrature.CSource.C

open CC Binary64.ClightSource FloatLib.Floats.Formats.BinaryInterchange

private theorem small_signed (n : Nat) (hn : n ≤ 10) :
    Integers.Int.signed (Integers.Int.repr n) = (n : Int) := by
  apply BitVec.toInt_ofInt_eq_self (by decide) <;> norm_num; omega

private theorem small_compare (ge : GlobalEnv) (memory : Mem) (i n : Nat)
    (hi : i ≤ 10) (hn : n ≤ 10) :
    Cop.semBinaryOperation ge.composites .Olt
      (.Vint (Integers.Int.repr i)) tint (.Vint (Integers.Int.repr n)) tint memory =
      some (Val.ofBool (decide (i < n))) := by
  change some (Val.ofBool (decide (Integers.Int.signed (Integers.Int.repr i) <
    Integers.Int.signed (Integers.Int.repr n)))) = _
  rw [small_signed i hi, small_signed n hn]
  simp

/-- Adding one to the represented loop index gives the representation of its successor. -/
theorem int_repr_add_one (i : Nat) :
    Integers.Int.add (Integers.Int.repr i) (Integers.Int.repr 1) =
      Integers.Int.repr (i + 1) := by
  change BitVec.ofInt 32 (i : Int) + BitVec.ofInt 32 1 =
    BitVec.ofInt 32 ((i + 1 : Nat) : Int)
  rw [← BitVec.ofInt_add]
  simp

/-- The loop guard is a pure read and signed comparison of its two small indices. -/
theorem integrator_guard_value (ge : GlobalEnv) (frame : IntegratorFrame) (memory : Mem)
    (callback : Val) (n i : Nat) (accumulator : Floats.Float) (hn : n ≤ 10) (hi : i ≤ 10)
    (state : IntegratorState frame memory callback n i accumulator) :
    EvalRvalue ge.expressionEnv frame.locals memory integratorGuard
      (Val.ofBool (decide (i < n))) :=
  .binop _ _ _ _ _ _ _
    (read_local ge.expressionEnv frame.locals memory _i tint frame.index .Mint32
      (.Vint (Integers.Int.repr i)) rfl rfl rfl state.index_load)
    (read_local ge.expressionEnv frame.locals memory _n tint frame.count .Mint32
      (.Vint (Integers.Int.repr n)) rfl rfl rfl state.count_load)
    (small_compare ge memory i n hi hn)

variable [ExternalCalls]

/-- Under `IntegratorState` with `n, i ≤ 10`, the loop test `i < n` evaluates to the boolean
`decide (i < n)` without changing memory. -/
theorem integrator_guard (ge : GlobalEnv) (frame : IntegratorFrame) (memory : Mem)
    (callback : Val) (n i : Nat) (accumulator : Floats.Float) (hn : n ≤ 10) (hi : i ≤ 10)
    (state : IntegratorState frame memory callback n i accumulator) :
    EvalExpression ge frame.locals memory integratorGuard E0 memory
      (Val.ofBool (decide (i < n))) := by
  apply EvalExpression.intro
  · exact .binop _ _ _ E0 _ _ _ E0 _ _ _ _
      (read_var_effects ge frame.locals memory _i tint rfl)
      (read_var_effects ge frame.locals memory _n tint rfl)
  · exact integrator_guard_value ge frame memory callback n i accumulator hn hi state

/-- Under `IntegratorState` at index `i`, the statement `i++;` executes normally, storing `i + 1`
into the index block and yielding `IntegratorState` at index `i + 1` and `LoopMemory`. -/
theorem integrator_increment (ge : GlobalEnv) (frame : IntegratorFrame) (memory : Mem)
    (callback : Val) (n i : Nat) (accumulator : Floats.Float)
    (state : IntegratorState frame memory callback n i accumulator) :
    ∃ final,
      ExecStmt ge frame.locals memory integratorIncrement E0 final .normal ∧
      IntegratorState frame final callback n (i + 1) accumulator ∧
      LoopMemory frame memory final := by
  obtain ⟨final, hstore⟩ : ∃ final, Mem.store .Mint32 memory frame.index 0
      (.Vint (Integers.Int.repr (i + 1))) = some final := by
    simp only [Mem.store, state.index_writable, ite_true]
    exact ⟨_, rfl⟩
  refine ⟨final, ?_, state.store_index hstore, .of_store hstore (Or.inl rfl)⟩
  apply ExecStmt.do
  apply EvalExpression.intro
  · apply EvalExpr.postincr (t₁ := E0) (t₂ := E0) (t₃ := E0) (m₁ := memory)
      (block := frame.index) (ofs := Integers.Ptrofs.zero) (bf := .Full)
      (v₁ := .Vint (Integers.Int.repr i)) (v₂ := .Vint (Integers.Int.repr (i + 1)))
      (v₃ := .Vint (Integers.Int.repr (i + 1)))
    · exact .var _ _ _ _
    · exact .var_local _ _ _ rfl
    · exact .value .Mint32 _ rfl rfl state.index_load
    · change some (Val.Vint (Integers.Int.add (Integers.Int.repr i) (Integers.Int.repr 1))) = _
      rw [int_repr_add_one]
    · rfl
    · exact .value _ .Mint32 _ rfl rfl hstore
    · rfl
  · exact .value _ _

/-- Under `IntegratorState`, `SourceTableFunctions`, `SourceCallbackContract` and the table cells
for `n` and `i`, the statement `s += ...;` executes normally and yields `IntegratorState` with
accumulator `Model.add acc (Model.mul weight (f node))` and `LoopMemory`. -/
theorem integrator_update (ge : GlobalEnv) (frame : IntegratorFrame) (memory : Mem)
    (ctx : SourceTableFunctions ge) (callback : Val) (function : FunDef)
    (f : Floats.Float → Floats.Float) (n i : Nat) (accumulator weight node : Floats.Float)
    (hn : n ≤ 10) (hi : i ≤ 10)
    (state : IntegratorState frame memory callback n i accumulator)
    (contract : SourceCallbackContract ge callback function f)
    (hweight : Mem.load .Mfloat64 memory ctx.weights
      (8 * Binary64.Clight.tableOffset n i : Nat) = some (.Vfloat weight))
    (hnode : Mem.load .Mfloat64 memory ctx.nodes
      (8 * Binary64.Clight.tableOffset n i : Nat) = some (.Vfloat node)) :
    ∃ final,
      ExecStmt ge frame.locals memory integratorUpdate E0 final .normal ∧
      IntegratorState frame final callback n i
        (Model.add accumulator (Model.mul weight (f node))) ∧
      LoopMemory frame memory final := by
  obtain ⟨sampled, heffects, hmemory⟩ := weighted_sample_effects ge frame memory ctx callback
    function f n i accumulator weight node hn hi state contract hweight hnode
  have sampledState := state.after_call hmemory
  obtain ⟨final, hstore⟩ : ∃ final, Mem.store .Mfloat64 sampled frame.accumulator 0
      (.Vfloat (Model.add accumulator (Model.mul weight (f node)))) =
        some final := by
    simp only [Mem.store, sampledState.accumulator_writable, ite_true]
    exact ⟨_, rfl⟩
  refine ⟨final, ?_, sampledState.store_accumulator hstore,
    (LoopMemory.of_call frame hmemory).trans (.of_store hstore (Or.inr rfl))⟩
  apply ExecStmt.do
  apply EvalExpression.intro
  · apply EvalExpr.assignop (t₁ := E0) (t₂ := E0) (t₃ := E0) (t₄ := E0)
      (m₁ := memory) (m₂ := sampled) (block := frame.accumulator)
      (ofs := Integers.Ptrofs.zero) (bf := .Full) (v₁ := .Vfloat accumulator)
      (v₂ := .Vfloat (Model.mul weight (f node)))
      (v₃ := .Vfloat (Model.add accumulator (Model.mul weight (f node))))
      (v₄ := .Vfloat (Model.add accumulator (Model.mul weight (f node))))
    · exact .var _ _ _ _
    · exact heffects
    · exact .var_local _ _ _ rfl
    · exact .value .Mfloat64 _ rfl rfl sampledState.accumulator_load
    · exact .binop _ _ _ _ _ _ _ (.value _ _) (.value _ _) rfl
    · rfl
    · rfl
    · exact .value _ .Mfloat64 _ rfl rfl hstore
    · rfl
  · exact .value _ _

end Quadrature.CSource.C
