import Quadrature.Compiler.Cminor.Execution

/-!
# Checks of the Cminor semantics

Small authored operations and programs that exercise the checker: rejected operations
and arguments, stack allocation and freeing, and complete executions of two functions.
`stack_store_load_returns` and `float_call_returns` are proved through the checker's
soundness theorem `default_execute_steps_sound`.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Cminor.Validation

open CC

/-- Signed 32-bit division by zero fails. -/
theorem integer_division_by_zero :
    evalBinary .Odiv (.Vint (Integers.Int.repr 7)) (.Vint Integers.Int.zero) Mem.empty =
      none := by decide

/-- Comparing undefined 64-bit values fails. -/
theorem invalid_long_comparison :
    evalBinary (.Ocmpl .Ceq) .Vundef .Vundef Mem.empty = none := rfl

/-- Comparing undefined 32-bit values yields `Vundef` rather than failing. -/
theorem invalid_int_comparison :
    evalBinary (.Ocmp .Ceq) .Vundef .Vundef Mem.empty = some .Vundef := rfl

/-- A 64-bit integer is rejected as a branch condition. -/
theorem long_is_not_a_condition :
    boolOfVal (.Vlong Integers.Int64.one) = none := rfl

/-- A 32-bit switch scrutinee is read as an unsigned integer, so `-1` selects key `4294967295`. -/
theorem switch_uses_unsigned_integer :
    switchArgument false (.Vint (Integers.Int.repr (-1))) = some 4294967295 := by decide

/-- `Vundef` is rejected as a binary64 argument. -/
theorem undefined_argument_rejected : ¬ HasArgType .Vundef .Xfloat := by decide

/-- `128` is rejected as a signed 8-bit argument. -/
theorem signed_byte_out_of_range :
    ¬ HasArgType (.Vint (Integers.Int.repr 128)) .Xint8signed := by decide

/-- `2` is rejected as a boolean argument. -/
theorem bool_argument_out_of_range :
    ¬ HasArgType (.Vint (Integers.Int.repr 2)) .Xbool := by decide

/-- Freeing a frame through a stack pointer with nonzero offset fails. -/
theorem nonzero_stack_offset_rejected (memory : Mem) :
    freeStack memory (.Vptr .xH (Integers.Ptrofs.repr 1)) 0 = none := rfl

/-- A global environment with no definitions. -/
def emptyGenv : Genv := CC.Genv.emptyGenv []

/-- A function with an 8-byte frame that stores 17 into it and returns the loaded value. -/
def stackFunction : Function where
  fn_sig := mksignature [] .Xlong cc_default
  fn_params := []
  fn_vars := []
  fn_stackspace := 8
  fn_body := .Sseq
    (.Sstore .Mint64 (.Econst (.Oaddrstack Integers.Ptrofs.zero))
      (.Econst (.Olongconst (Integers.Int64.repr 17))))
    (.Sreturn (some (.Eload .Mint64 (.Econst (.Oaddrstack Integers.Ptrofs.zero)))))

/-- A function with an empty frame that returns the binary64 sum of its two parameters. -/
def floatFunction : Function where
  fn_sig := mksignature [.Xfloat, .Xfloat] .Xfloat cc_default
  fn_params := [.xH, .xO .xH]
  fn_vars := []
  fn_stackspace := 0
  fn_body := .Sreturn (some (.Ebinop .Oaddf (.Evar .xH) (.Evar (.xO .xH))))

/-- `floatValue bits` is the binary64 value with the given bit pattern. -/
def floatValue (bits : Int) : Val := .Vfloat (Floats.Float.ofBits (Integers.Int64.repr bits))

/-- The call of `stackFunction` with no arguments in the empty memory. -/
def stackStart : State := .Callstate (.Internal stackFunction) [] .Kstop Mem.empty

/-- The call of `floatFunction` with arguments `2.0` and `3.0` in the empty memory. -/
def floatStart : State := .Callstate (.Internal floatFunction)
  [floatValue 0x4000000000000000, floatValue 0x4008000000000000] .Kstop Mem.empty

/-- Observe the result, fresh-block counter, and accessibility of the former stack. -/
private def observeReturn : State → Option (Val × Positive × Option Val)
  | .Returnstate value .Kstop memory =>
      some (value, memory.nextblock, Mem.load .Mint64 memory .xH 0)
  | _ => none

private def observeRun (fuel : Nat) (start : State) :
    Option (Trace × Val × Positive × Option Val) := do
  let (trace, finish) ← executeSteps CC.doExternalCall emptyGenv fuel start
  let (value, nextblock, formerStack) ← observeReturn finish
  pure (trace, value, nextblock, formerStack)

private theorem stack_run_checked :
    observeRun 5 stackStart = some ([], .Vlong (Integers.Int64.repr 17), .xO .xH, none) := by
  decide

private theorem float_run_checked :
    observeRun 2 floatStart = some ([], floatValue 0x4014000000000000, .xO .xH, none) := by
  decide

variable [ExternalCalls]

private theorem observed_run_sound {fuel : Nat} {start : State} {trace : Trace}
    {value : Val} {nextblock : Positive} {formerStack : Option Val}
    (h : observeRun fuel start = some (trace, value, nextblock, formerStack)) :
    ∃ memory, Steps emptyGenv start trace (.Returnstate value .Kstop memory) ∧
      memory.nextblock = nextblock ∧ Mem.load .Mint64 memory .xH 0 = formerStack := by
  simp only [observeRun, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨emitted, finish⟩, hrun, ⟨result, next, frame⟩, hresult, h⟩ := h
  cases h
  cases finish with
  | Running => cases hresult
  | Callstate => cases hresult
  | Returnstate result k memory =>
      cases k <;> cases hresult
      exact ⟨memory, default_execute_steps_sound hrun, rfl, rfl⟩

/-- `stackStart` returns 17 after allocating one fresh block, and the freed frame can no longer be
loaded. -/
theorem stack_store_load_returns :
    ∃ memory,
      Steps emptyGenv stackStart [] (.Returnstate (.Vlong (Integers.Int64.repr 17)) .Kstop memory) ∧
      memory.nextblock = .xO .xH ∧ Mem.load .Mint64 memory .xH 0 = none :=
  observed_run_sound stack_run_checked

/-- Binary64 `2 + 3` returns 5, and even this zero-size frame consumes a fresh block. -/
theorem float_call_returns :
    ∃ memory,
      Steps emptyGenv floatStart [] (.Returnstate (floatValue 0x4014000000000000) .Kstop memory) ∧
      memory.nextblock = .xO .xH ∧ Mem.load .Mint64 memory .xH 0 = none :=
  observed_run_sound float_run_checked

end Quadrature.Cminor.Validation
