import Quadrature.CSource.Integrator.Loop

/-!
# Initialization and return of the original integrator body

`integrator_body` starts after parameter binding, with writable storage for
the two locals (`IntegratorParameters`), and executes `s = 0.0`, the `for`
initializer `i = 0`, every loop iteration and the final `return s`. The
initial contents of the two locals are not assumed. `source_integrator_body`
identifies the executed body with the one elaborated from the original C
program. Allocation, parameter binding and freeing are handled by the enclosing
call in `Quadrature.CSource.Integrator.Function`.
-/

namespace Quadrature.CSource.C

open CC Binary64.ClightSource FloatLib.Floats.Formats.BinaryInterchange

/-- The statement `s = 0.0;`. -/
def integratorInitialize : Stmt :=
  .Sdo (.Eassign (.Evar _s tdouble) (.Eval (.Vfloat Binary64.zero) tdouble) tdouble)

/-- The `for` initializer `i = 0;`. -/
def integratorIndexInitialize : Stmt :=
  .Sdo (.Eassign (.Evar _i tint) (.Eval (.Vint (Integers.Int.repr 0)) tint) tint)

/-- The statement `return s;`. -/
def integratorReturn : Stmt := .Sreturn (some (readVar _s tdouble))

/-- The elaborated body of `Typed.integrate` is `s = 0.0;`, then the `for` loop with initializer
`i = 0;`, then `return s;`, by `rfl`. -/
theorem integrator_body_syntax :
    Typed.integrate.fn_body =
      .Ssequence integratorInitialize
        (.Ssequence
          (.Sfor integratorIndexInitialize integratorGuard integratorIncrement integratorUpdate)
          integratorReturn) := by
  rfl

/-- `IntegratorParameters frame memory callback n`: the callback and count blocks hold `callback`
and `n`, and the index and accumulator blocks are writable. This is the state at body entry,
before the locals are initialized. `integrator_entry` establishes it. -/
structure IntegratorParameters (frame : IntegratorFrame) (memory : Mem)
    (callback : Val) (n : Nat) : Prop where
  callback_load : Mem.load Mptr memory frame.callback 0 = some callback
  count_load : Mem.load .Mint32 memory frame.count 0 = some (.Vint (Integers.Int.repr n))
  index_writable : Mem.validAccess memory .Mint32 frame.index 0 .Writable = true
  accumulator_writable : Mem.validAccess memory .Mfloat64 frame.accumulator 0 .Writable = true

variable [ExternalCalls]

private theorem assign_constant (ge : GlobalEnv) (locals : Env) (memory final : Mem)
    (name : Ident) (block : Block) (type : Ty) (chunk : Chunk) (value : Val)
    (hname : locals.get name = some (block, type))
    (hmode : accessMode type = .By_value chunk) (hvolatile : typeIsVolatile type = false)
    (hcast : Cop.semCast value type type memory = some value)
    (hstore : Mem.store chunk memory block 0 value = some final) :
    ExecStmt ge locals memory (.Sdo (.Eassign (.Evar name type) (.Eval value type) type))
      E0 final .normal := by
  apply ExecStmt.do
  apply EvalExpression.intro
  · apply EvalExpr.assign (t₁ := E0) (t₂ := E0) (t₃ := E0) (m₁ := memory) (m₂ := memory)
      (block := block) (ofs := Integers.Ptrofs.zero) (bf := .Full) (v := value) (v₁ := value)
    · exact .var _ _ _ _
    · exact .value _ _ _ _
    · exact .var_local _ _ _ hname
    · exact .value _ _
    · exact hcast
    · exact .value _ chunk _ hmode hvolatile hstore
    · rfl
  · exact .value _ _

omit [ExternalCalls] in
/-- The two initializer stores establish the loop invariant without reading either local's
previous contents. Both the strategy and full C proofs use these same memory facts. -/
theorem integrator_initialization_memory (frame : IntegratorFrame) (memory : Mem)
    (callback : Val) (n : Nat) (parameters : IntegratorParameters frame memory callback n) :
    ∃ summed ready,
      Mem.store .Mfloat64 memory frame.accumulator 0 (.Vfloat Binary64.zero) = some summed ∧
      Mem.store .Mint32 summed frame.index 0 (.Vint (Integers.Int.repr 0)) = some ready ∧
      IntegratorState frame ready callback n 0 Binary64.zero ∧ LoopMemory frame memory ready := by
  obtain ⟨summed, hsum⟩ : ∃ summed,
      Mem.store .Mfloat64 memory frame.accumulator 0 (.Vfloat Binary64.zero) =
        some summed := by
    simp only [Mem.store, parameters.accumulator_writable, ite_true]
    exact ⟨_, rfl⟩
  have hindex : Mem.validAccess summed .Mint32 frame.index 0 .Writable = true := by
    rw [Mem.validAccess_store_eq hsum]
    exact parameters.index_writable
  obtain ⟨ready, hi⟩ : ∃ ready,
      Mem.store .Mint32 summed frame.index 0 (.Vint (Integers.Int.repr 0)) = some ready := by
    simp only [Mem.store, hindex, ite_true]
    exact ⟨_, rfl⟩
  refine ⟨summed, ready, hsum, hi, ?_,
    (LoopMemory.of_store hsum (Or.inr rfl)).trans (.of_store hi (Or.inl rfl))⟩
  refine ⟨?_, ?_, Mem.load_store_same hi, ?_, ?_, ?_⟩
  · rw [Mem.load_store_other hi Mptr frame.callback 0 (Or.inl frame.callback_ne_index),
      Mem.load_store_other hsum Mptr frame.callback 0 (Or.inl frame.callback_ne_accumulator)]
    exact parameters.callback_load
  · rw [Mem.load_store_other hi .Mint32 frame.count 0 (Or.inl frame.count_ne_index),
      Mem.load_store_other hsum .Mint32 frame.count 0 (Or.inl frame.count_ne_accumulator)]
    exact parameters.count_load
  · rw [Mem.load_store_other hi .Mfloat64 frame.accumulator 0
      (Or.inl frame.index_ne_accumulator.symm)]
    exact Mem.load_store_same hsum
  · rw [Mem.validAccess_store_eq hi]
    exact hindex
  · rw [Mem.validAccess_store_eq hi, Mem.validAccess_store_eq hsum]
    exact parameters.accumulator_writable

/-- Given `IntegratorParameters`, the statements `s = 0.0;` and `i = 0;` execute normally in
turn, and the result satisfies `IntegratorState` at index 0 with accumulator `+0.0` and
`LoopMemory`. -/
theorem integrator_initialization (ge : GlobalEnv) (frame : IntegratorFrame) (memory : Mem)
    (callback : Val) (n : Nat) (parameters : IntegratorParameters frame memory callback n) :
    ∃ summed ready,
      ExecStmt ge frame.locals memory integratorInitialize E0 summed .normal ∧
      ExecStmt ge frame.locals summed integratorIndexInitialize E0 ready .normal ∧
      IntegratorState frame ready callback n 0 Binary64.zero ∧ LoopMemory frame memory ready := by
  obtain ⟨summed, ready, hsum, hi, hstate, hmemory⟩ :=
    integrator_initialization_memory frame memory callback n parameters
  exact ⟨summed, ready,
    assign_constant ge frame.locals memory summed _s frame.accumulator tdouble
      .Mfloat64 (.Vfloat Binary64.zero) rfl rfl rfl rfl hsum,
    assign_constant ge frame.locals summed ready _i frame.index tint
      .Mint32 (.Vint (Integers.Int.repr 0)) rfl rfl rfl rfl hi,
    hstate, hmemory⟩

/-- Given `IntegratorParameters` for `terms.length ≤ 10` nodes, `SourceTableFunctions`,
`TableSeparation`, `SourceCallbackContract` and the `TableCells` of `terms`, the body of
`Typed.integrate` executes silently to outcome `return (Vfloat (integrate f terms))`. The final
memory satisfies `IntegratorState` at the final index and `LoopMemory` from the entry memory. -/
theorem integrator_body (ge : GlobalEnv) (frame : IntegratorFrame) (memory : Mem)
    (ctx : SourceTableFunctions ge) (callback : Val) (function : FunDef)
    (f : Floats.Float → Floats.Float) (terms : List (Floats.Float × Floats.Float))
    (hn : terms.length ≤ 10)
    (parameters : IntegratorParameters frame memory callback terms.length)
    (separate : TableSeparation frame ctx.nodes ctx.weights)
    (contract : SourceCallbackContract ge callback function f)
    (cells : Binary64.Clight.TableCells memory ctx.nodes ctx.weights terms.length 0 terms) :
    ∃ final,
      ExecStmt ge frame.locals memory Typed.integrate.fn_body E0 final
        (.return (some (.Vfloat (Binary64.integrate f terms), tdouble))) ∧
      IntegratorState frame final callback terms.length terms.length
        (Binary64.integrate f terms) ∧ LoopMemory frame memory final := by
  obtain ⟨summed, ready, hsum, hindex, readyState, initializedMemory⟩ :=
    integrator_initialization ge frame memory callback terms.length parameters
  obtain ⟨final, hloop, finalState, loopMemory⟩ := integrator_loop ge frame ready ctx callback
    function f terms.length hn terms 0 Binary64.zero (Nat.zero_add _)
    readyState separate contract (initializedMemory.table_cells separate cells)
  refine ⟨final, ?_, finalState, initializedMemory.trans loopMemory⟩
  rw [integrator_body_syntax]
  apply ExecStmt.seq_normal (t₁ := E0) (t₂ := E0) (m₁ := summed)
  · exact hsum
  · apply ExecStmt.seq_normal (t₁ := E0) (t₂ := E0) (m₁ := final)
    · exact .for_start _ _ _ _ _ _ _ _ _ E0 E0 hindex hloop
    · apply ExecStmt.return_some
      apply EvalExpression.intro
      · exact read_var_effects ge frame.locals final _s tdouble rfl
      · exact read_local ge.expressionEnv frame.locals final _s tdouble frame.accumulator
          .Mfloat64 _ rfl rfl rfl finalState.accumulator_load

/-- `integrator_body` restated for the function that parsing and elaborating the original C text
of `integrate` produces. -/
theorem source_integrator_body (ge : GlobalEnv) (frame : IntegratorFrame) (memory : Mem)
    (ctx : SourceTableFunctions ge) (callback : Val) (function : FunDef)
    (f : Floats.Float → Floats.Float) (terms : List (Floats.Float × Floats.Float))
    (hn : terms.length ≤ 10)
    (parameters : IntegratorParameters frame memory callback terms.length)
    (separate : TableSeparation frame ctx.nodes ctx.weights)
    (contract : SourceCallbackContract ge callback function f)
    (cells : Binary64.Clight.TableCells memory ctx.nodes ctx.weights terms.length 0 terms) :
    ∃ sourceFunction final,
      typedSourceFunction CSourceData.source "integrate" = some sourceFunction ∧
      ExecStmt ge frame.locals memory sourceFunction.fn_body E0 final
        (.return (some (.Vfloat (Binary64.integrate f terms), tdouble))) ∧
      LoopMemory frame memory final := by
  obtain ⟨final, hbody, _, hmemory⟩ :=
    integrator_body ge frame memory ctx callback function f terms hn parameters
      separate contract cells
  exact ⟨Typed.integrate, final, Typed.integrate_elaboration, hbody, hmemory⟩

end Quadrature.CSource.C
