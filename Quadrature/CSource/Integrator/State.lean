import Quadrature.CSource.Semantics.CallMemory

/-!
# Local state of the original C integrator

The integrator's four variables `f`, `n`, `i`, `s` occupy distinct memory
blocks (`IntegratorFrame`). The loop invariant `IntegratorState` records their
loaded values and writable access to the two updated variables. Nested calls
preserve the invariant when they satisfy `CallMemory`, and the two stores
update it. Function entry establishes it in
`Quadrature.CSource.Integrator.Entry`. The typed C fragments of the loop body
are defined here so that later files can name them.
-/

namespace Quadrature.CSource.C

open CC Binary64.ClightSource

/-- The C type of the callback `f`: `double (double)`. -/
def callbackType : Ty := .Tfunction [tdouble] tdouble cc_default

/-- The C type of both table accessors: `double (int, int)`. -/
def accessorType : Ty := .Tfunction [tint, tint] tdouble cc_default

/-- The typed C read of variable `name`: `Evalof (Evar name type) type`. -/
def readVar (name : Ident) (type : Ty) : Expr := .Evalof (.Evar name type) type

/-- The call `name(i, n)` of an accessor with the integrator's index and count. -/
def accessorCall (name : Ident) : Expr :=
  .Ecall (readVar name accessorType)
    (.Econs (readVar _i tint) (.Econs (readVar _n tint) .Enil)) tdouble

/-- The source product `gauss_weight(i, n) * f(gauss_point(i, n))`, with its three nested
calls. -/
def weightedSample : Expr :=
  .Ebinop .Omul (accessorCall _gauss_weight)
    (.Ecall (readVar _f (tptr callbackType))
      (.Econs (accessorCall _gauss_point) .Enil) tdouble) tdouble

/-- The loop body statement `s += weightedSample;`. -/
def integratorUpdate : Stmt :=
  .Sdo (.Eassignop .Oadd (.Evar _s tdouble) weightedSample tdouble tdouble)

/-- The loop increment statement `i++;`. -/
def integratorIncrement : Stmt :=
  .Sdo (.Epostincr .incr (.Evar _i tint) tint)

/-- The loop test `i < n`. -/
def integratorGuard : Expr := .Ebinop .Olt (readVar _i tint) (readVar _n tint) tint

/-- The `for` loop after its initializer has run: test `integratorGuard`, increment
`integratorIncrement`, body `integratorUpdate`. -/
def integratorLoop : Stmt :=
  .Sfor .Sskip integratorGuard integratorIncrement integratorUpdate

/-- The blocks of the integrator's four variables `f` (`callback`), `n` (`count`), `i` (`index`)
and `s` (`accumulator`), required to be distinct, independently of their contents. -/
structure IntegratorFrame where
  callback : Block
  count : Block
  index : Block
  accumulator : Block
  distinct : [callback, count, index, accumulator].Nodup

/-- The C environment binding `f`, `n`, `i` and `s` to the frame's blocks with their types. -/
def IntegratorFrame.locals (frame : IntegratorFrame) : Env :=
  (((emptyEnv.set _f (frame.callback, tptr callbackType)).set _n (frame.count, tint)).set
    _i (frame.index, tint)).set _s (frame.accumulator, tdouble)

/-- Two frame blocks differ, from `distinct`. -/
theorem IntegratorFrame.callback_ne_index (frame : IntegratorFrame) :
    frame.callback ≠ frame.index := by
  have h := frame.distinct
  simp only [List.nodup_cons, List.mem_cons, not_or] at h
  exact h.1.2.1

/-- Two frame blocks differ, from `distinct`. -/
theorem IntegratorFrame.callback_ne_accumulator (frame : IntegratorFrame) :
    frame.callback ≠ frame.accumulator := by
  have h := frame.distinct
  simp only [List.nodup_cons, List.mem_cons, not_or] at h
  exact h.1.2.2.1

/-- Two frame blocks differ, from `distinct`. -/
theorem IntegratorFrame.count_ne_index (frame : IntegratorFrame) :
    frame.count ≠ frame.index := by
  have h := frame.distinct
  simp only [List.nodup_cons, List.mem_cons, not_or] at h
  exact h.2.1.1

/-- Two frame blocks differ, from `distinct`. -/
theorem IntegratorFrame.count_ne_accumulator (frame : IntegratorFrame) :
    frame.count ≠ frame.accumulator := by
  have h := frame.distinct
  simp only [List.nodup_cons, List.mem_cons, not_or] at h
  exact h.2.1.2.1

/-- Two frame blocks differ, from `distinct`. -/
theorem IntegratorFrame.index_ne_accumulator (frame : IntegratorFrame) :
    frame.index ≠ frame.accumulator := by
  have h := frame.distinct
  simp only [List.nodup_cons, List.mem_cons, not_or] at h
  exact h.2.2.1.1

/-- `IntegratorState frame memory callback n i acc`: the frame's blocks hold `callback`, `n`, `i`
and `acc` in `memory`, and the index and accumulator blocks are writable. Allocation is not part
of the assertion. `IntegratorEntry` establishes it. -/
structure IntegratorState (frame : IntegratorFrame) (memory : Mem)
    (callback : Val) (n i : Nat) (accumulator : Floats.Float) : Prop where
  callback_load : Mem.load Mptr memory frame.callback 0 = some callback
  count_load : Mem.load .Mint32 memory frame.count 0 = some (.Vint (Integers.Int.repr n))
  index_load : Mem.load .Mint32 memory frame.index 0 = some (.Vint (Integers.Int.repr i))
  accumulator_load : Mem.load .Mfloat64 memory frame.accumulator 0 = some (.Vfloat accumulator)
  index_writable : Mem.validAccess memory .Mint32 frame.index 0 .Writable = true
  accumulator_writable : Mem.validAccess memory .Mfloat64 frame.accumulator 0 .Writable = true

/-- A nested call satisfying `CallMemory` preserves the invariant. -/
theorem IntegratorState.after_call {frame : IntegratorFrame} {initial final : Mem}
    {callback : Val} {n i : Nat} {accumulator : Floats.Float}
    (state : IntegratorState frame initial callback n i accumulator)
    (hcall : CallMemory initial final) :
    IntegratorState frame final callback n i accumulator := by
  refine ⟨hcall.load state.callback_load, hcall.load state.count_load,
    hcall.load state.index_load, hcall.load state.accumulator_load, ?_, ?_⟩
  · rw [hcall.valid_access _ _ _ _ (block_valid_of_load state.index_load)]
    exact state.index_writable
  · rw [hcall.valid_access _ _ _ _ (block_valid_of_load state.accumulator_load)]
    exact state.accumulator_writable

/-- Storing `value` into the accumulator block updates the invariant's accumulator. -/
theorem IntegratorState.store_accumulator {frame : IntegratorFrame} {initial final : Mem}
    {callback : Val} {n i : Nat} {accumulator value : Floats.Float}
    (state : IntegratorState frame initial callback n i accumulator)
    (hstore : Mem.store .Mfloat64 initial frame.accumulator 0 (.Vfloat value) = some final) :
    IntegratorState frame final callback n i value := by
  refine ⟨?_, ?_, ?_, Mem.load_store_same hstore, ?_, ?_⟩
  · rw [Mem.load_store_other hstore Mptr frame.callback 0
      (Or.inl frame.callback_ne_accumulator)]
    exact state.callback_load
  · rw [Mem.load_store_other hstore .Mint32 frame.count 0
      (Or.inl frame.count_ne_accumulator)]
    exact state.count_load
  · rw [Mem.load_store_other hstore .Mint32 frame.index 0
      (Or.inl frame.index_ne_accumulator)]
    exact state.index_load
  · rw [Mem.validAccess_store_eq hstore]
    exact state.index_writable
  · rw [Mem.validAccess_store_eq hstore]
    exact state.accumulator_writable

/-- Storing `j` into the index block updates the invariant's index. -/
theorem IntegratorState.store_index {frame : IntegratorFrame} {initial final : Mem}
    {callback : Val} {n i j : Nat} {accumulator : Floats.Float}
    (state : IntegratorState frame initial callback n i accumulator)
    (hstore : Mem.store .Mint32 initial frame.index 0
      (.Vint (Integers.Int.repr j)) = some final) :
    IntegratorState frame final callback n j accumulator := by
  refine ⟨?_, ?_, Mem.load_store_same hstore, ?_, ?_, ?_⟩
  · rw [Mem.load_store_other hstore Mptr frame.callback 0 (Or.inl frame.callback_ne_index)]
    exact state.callback_load
  · rw [Mem.load_store_other hstore .Mint32 frame.count 0 (Or.inl frame.count_ne_index)]
    exact state.count_load
  · rw [Mem.load_store_other hstore .Mfloat64 frame.accumulator 0
      (Or.inl frame.index_ne_accumulator.symm)]
    exact state.accumulator_load
  · rw [Mem.validAccess_store_eq hstore]
    exact state.index_writable
  · rw [Mem.validAccess_store_eq hstore]
    exact state.accumulator_writable

end Quadrature.CSource.C
