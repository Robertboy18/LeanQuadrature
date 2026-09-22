import Quadrature.CSource.Callback.Entry
import Quadrature.CSource.Cosine.Source

/-!
# Execution of the C polynomial cosine

`function_call` proves that the complete C routine returns
`Binary64.Polynomial.cosine x` for every binary64 argument. Allocation,
parameter binding, the store of the rounded square, the return cast and freeing
are all derived. The routine calls no external function and preserves the
caller's memory.

`callback_contract` supplies the contract needed by the original quadrature
callback when its `cos` symbol resolves to this internal definition.
-/

namespace Quadrature.CSource.Cosine

open CC Binary64 FloatLib.Floats.Formats.BinaryInterchange
open Binary64.ClightSource

/-- Every signed coefficient expression has type `double`. -/
theorem coefficient_type (c : Bool × Nat) :
    C.typeof (coefficientExpression c) = tdouble := by
  cases h : c.1 <;> simp [coefficientExpression, h, C.typeof]

/-- Every Horner expression has type `double`, including the zero polynomial. -/
theorem horner_type (cs : List (Bool × Nat)) :
    C.typeof (hornerExpression cs) = tdouble := by
  cases cs <;> rfl

/-- A signed coefficient evaluates to its rounded literal value in every memory. -/
theorem coefficient_value (ge : C.ExpressionEnv) (locals : Env) (memory : Mem)
    (c : Bool × Nat) :
    C.EvalRvalue ge locals memory (coefficientExpression c) (.Vfloat (coefficientValue c)) := by
  cases h : c.1
  · simpa only [coefficientExpression, coefficientValue, h, Bool.false_eq_true, ↓reduceIte]
      using C.EvalRvalue.value (ge := ge) (e := locals) (m := memory)
        (.Vfloat (Model.ofNatBits c.2)) tdouble
  · simp only [coefficientExpression, coefficientValue, h, ↓reduceIte]
    exact .unop _ _ _ _ _ (.value _ _) rfl

/-- Reading the square from `block` and evaluating Horner's expression gives exactly the
FloatLib fold, with a separate rounding for each product and addition. -/
theorem horner_value (ge : C.ExpressionEnv) (memory : Mem) (block : Block)
    (square : Floats.Float) (cs : List (Bool × Nat))
    (hload : Mem.load .Mfloat64 memory block 0 = some (.Vfloat square)) :
    C.EvalRvalue ge (C.testfunLocals block) memory (hornerExpression cs)
      (.Vfloat (Polynomial.horner square (cs.map coefficientValue))) := by
  induction cs with
  | nil => exact .value _ _
  | cons c cs ih =>
      apply C.EvalRvalue.binop
        (v₁ := .Vfloat (coefficientValue c))
        (v₂ := .Vfloat (Model.mul square (Polynomial.horner square (cs.map coefficientValue))))
      · exact coefficient_value ge (C.testfunLocals block) memory c
      · apply C.EvalRvalue.binop (v₁ := .Vfloat square)
          (v₂ := .Vfloat (Polynomial.horner square (cs.map coefficientValue)))
        · exact C.read_local ge (C.testfunLocals block) memory _x tdouble block .Mfloat64
            (.Vfloat square) rfl rfl rfl hload
        · exact ih
        · rw [horner_type]
          rfl
      · rw [coefficient_type]
        rfl

variable [ExternalCalls]

/-- Evaluating a coefficient has no effects. -/
theorem coefficient_effects (ge : C.GlobalEnv) (locals : Env) (memory : Mem)
    (c : Bool × Nat) :
    C.EvalExpr ge locals memory .RV (coefficientExpression c) E0 memory
      (coefficientExpression c) := by
  cases h : c.1 <;> simp only [coefficientExpression, h, Bool.false_eq_true, ↓reduceIte]
  · exact .value _ _ _ _
  · exact .unop _ _ _ _ _ _ _ _ (.value _ _ _ _)

/-- Horner's expression only reads the parameter; it performs no stores or calls. -/
theorem horner_effects (ge : C.GlobalEnv) (locals : Env) (memory : Mem)
    (cs : List (Bool × Nat)) :
    C.EvalExpr ge locals memory .RV (hornerExpression cs) E0 memory
      (hornerExpression cs) := by
  induction cs with
  | nil => exact .value _ _ _ _
  | cons c cs ih =>
      apply C.EvalExpr.binop (t₁ := E0) (t₂ := E0) (m₁ := memory)
      · exact coefficient_effects ge locals memory c
      · exact .binop _ _ _ E0 _ _ _ E0 _ _ _ _
          (C.read_var_effects ge locals memory _x tdouble rfl) ih

/-- The first statement stores the rounded square in the parameter's own block. -/
theorem square_assignment (ge : C.GlobalEnv) (memory squaredMemory : Mem)
    (block : Block) (x : Floats.Float)
    (hload : Mem.load .Mfloat64 memory block 0 = some (.Vfloat x))
    (hstore : Mem.store .Mfloat64 memory block 0 (.Vfloat (Model.mul x x)) =
      some squaredMemory) :
    C.ExecStmt ge (C.testfunLocals block) memory (.Sdo squareAssignment)
      E0 squaredMemory .normal := by
  have hread := C.read_local ge.expressionEnv (C.testfunLocals block) memory
    _x tdouble block .Mfloat64 (.Vfloat x) rfl rfl rfl hload
  apply C.ExecStmt.do
  apply C.EvalExpression.intro
  · apply C.EvalExpr.assign (t₁ := E0) (t₂ := E0) (t₃ := E0)
      (m₁ := memory) (m₂ := memory) (block := block) (ofs := Integers.Ptrofs.zero)
      (bf := .Full) (v := .Vfloat (Model.mul x x)) (v₁ := .Vfloat (Model.mul x x))
    · exact .var _ _ _ _
    · exact .binop _ _ _ E0 _ _ _ E0 _ _ _ _
        (C.read_var_effects ge (C.testfunLocals block) memory _x tdouble rfl)
        (C.read_var_effects ge (C.testfunLocals block) memory _x tdouble rfl)
    · exact .var_local _ _ _ rfl
    · exact .binop _ _ _ _ _ _ _ hread hread rfl
    · rfl
    · exact .value _ .Mfloat64 _ rfl rfl hstore
    · rfl
  · exact .value _ _

/-- Calling the internal C polynomial on any binary64 value returns exactly
`Polynomial.cosine x`, silently, and preserves all memory allocated by its caller. -/
theorem function_call (ge : C.GlobalEnv) (memory : Mem) (x : Floats.Float) :
    ∃ final,
      C.EvalFuncall ge memory (.Internal function) [.Vfloat x] E0 final
        (.Vfloat (Polynomial.cosine x)) ∧ C.CallMemory memory final := by
  obtain ⟨entered, hentry, hload, hfreeable, hentryMemory⟩ :=
    C.testfun_entry ge.expressionEnv memory x
  have hwrite : Mem.validAccess entered .Mfloat64 memory.nextblock 0 .Writable = true := by
    have h := Mem.rangePerm_implies hfreeable
      (show permOrder .Freeable .Writable = true from rfl)
    simpa [Mem.validAccess, sizeChunk, alignChunk] using h
  obtain ⟨squaredMemory, hstore⟩ : ∃ squaredMemory,
      Mem.store .Mfloat64 entered memory.nextblock 0 (.Vfloat (Model.mul x x)) =
        some squaredMemory := by
    simp only [Mem.store, hwrite, ite_true]
    exact ⟨_, rfl⟩
  have hsquareLoad := Mem.load_store_same hstore
  have hsquareFree :
      Mem.rangePerm squaredMemory memory.nextblock 0 8 .Cur .Freeable = true := by
    rw [Mem.rangePerm_store_eq hstore]
    exact hfreeable
  have hsquareMemory := hentryMemory.store_fresh hstore (Nat.le_refl _)
  have hreturn := horner_value ge.expressionEnv squaredMemory memory.nextblock
    (Model.mul x x) coefficients hsquareLoad
  rw [coefficient_values] at hreturn
  have hbody :
      C.ExecStmt ge (C.testfunLocals memory.nextblock) entered function.fn_body
        E0 squaredMemory (.return (some (.Vfloat (Polynomial.cosine x), tdouble))) := by
    apply C.ExecStmt.seq_normal (t₁ := E0) (t₂ := E0) (m₁ := squaredMemory)
    · exact square_assignment ge entered squaredMemory memory.nextblock x hload hstore
    · apply C.ExecStmt.return_some
      exact .intro _ _ _ _ _ _
        _ (horner_effects ge (C.testfunLocals memory.nextblock) squaredMemory coefficients)
        hreturn
  obtain ⟨final, hfree, hmemory⟩ :=
    C.testfun_free ge.composites memory squaredMemory squaredMemory (Model.mul x x)
      hsquareLoad hsquareFree hsquareMemory (.refl _)
  have hfunctionEntry :
      C.FunctionEntry ge.expressionEnv function [.Vfloat x]
        memory (C.testfunLocals memory.nextblock) entered :=
    ⟨hentry.names_unique, hentry.allocated_and_bound⟩
  exact ⟨final, hfunctionEntry.eval_funcall hbody ⟨by decide, rfl⟩ hfree, hmemory⟩

/-- The shipped C source, after parsing and elaboration, has the complete call proved above. -/
theorem source_call (ge : C.GlobalEnv) (memory : Mem) (x : Floats.Float) :
    ∃ final,
      Typed.SourceFunctionCall source "cos" ge [.Vfloat x] memory E0 final
        (.Vfloat (Polynomial.cosine x)) ∧ C.CallMemory memory final := by
  obtain ⟨final, hcall, hmemory⟩ := function_call ge memory x
  exact ⟨final, ⟨function, elaboration, hcall⟩, hmemory⟩

/-- A symbol resolving to the internal polynomial satisfies the original callback's cosine
execution contract, with no external-call assumption. -/
theorem callback_contract (ge : C.GlobalEnv) (block : Block)
    (hfunction : Genv.findFunct ge.globals (.Vptr block Integers.Ptrofs.zero) =
      some (.Internal function)) :
    C.SourceCallbackContract ge (.Vptr block Integers.Ptrofs.zero)
      (.Internal function) Polynomial.cosine :=
  ⟨hfunction, rfl, function_call ge⟩

end Quadrature.CSource.Cosine
