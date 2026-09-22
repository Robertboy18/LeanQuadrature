import Quadrature.Clight.Callbacks

/-!
# Clight executions of the four polynomial applications

`polynomial_call_run` runs the interpreter `runCall` on `polynomialCall order`
by kernel evaluation, exercising the imported integrator, the accessors, the
initialized tables, the callback and the internal cosine polynomial together.
The returned binary64 values are `Polynomial.result order`, the values whose
integral error is bounded in `Quadrature.Examples.PolynomialRules`. With the empty
external environment `internalExternalCalls`, the `polynomial_*` theorems form
the total-correctness package for these calls (vocabulary: see
`Quadrature.Clight.Execution`), and `polynomial_return_accuracy` attaches the
integral bound to every return.
-/

namespace Quadrature.Binary64.Clight

open FloatLib.Floats.Formats.BinaryInterchange

-- Run the interpreter on the polynomial call for each order and compare value and memory.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
/-- Running the interpreter for 300 steps on `polynomialCall order` returns
`Vfloat (Polynomial.result order)` with `initialMemory` unchanged, by kernel evaluation. -/
theorem polynomial_call_run (order : Polynomial.Order) :
    runCall polynomialLibrary.globalenv 300 (polynomialCall order) =
      some (.Vfloat (Polynomial.result order), initialMemory) := by
  rw [Polynomial.result_value]
  cases order <;> rfl

/-- The value-only projection of `polynomial_call_run`. -/
theorem polynomial_call_value (order : Polynomial.Order) :
    runCallValue polynomialLibrary.globalenv 300 (polynomialCall order) =
      some (.Vfloat (Polynomial.result order)) := by
  simp only [runCallValue, polynomial_call_run, Option.map_some]

/-- The state entering the original two-point wrapper `integrate_testfun` from `initialMemory`,
with the internal polynomial at the `cos` symbol. -/
def polynomialWrapperCall : CC.State :=
  .Callstate (.Internal ClightSource.f_integrate_testfun) [] .Kstop initialMemory

-- Run the interpreter on the wrapper call, through `integrate` and both callbacks.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- Running the interpreter on the wrapper returns `Vfloat (Polynomial.result .two)` with
`initialMemory` unchanged, by kernel evaluation. -/
theorem polynomial_wrapper_run :
    runCall polynomialLibrary.globalenv 300 polynomialWrapperCall =
      some (.Vfloat (Polynomial.result .two), initialMemory) := by
  rw [Polynomial.result_value]
  rfl

/-- The value-only projection of `polynomial_wrapper_run`. -/
theorem polynomial_wrapper_value :
    runCallValue polynomialLibrary.globalenv 300 polynomialWrapperCall =
      some (.Vfloat (Polynomial.result .two)) := by
  simp only [runCallValue, polynomial_wrapper_run, Option.map_some]

/-- The external-call contract in which no external function or inline assembly call is
possible, as every call in `polynomialLibrary` is internal. Its determinism instance below is
immediate, since the semantics is empty. -/
@[instance_reducible]
def internalExternalCalls : CC.ExternalCalls where
  functionSem := fun _ _ _ _ _ _ _ _ => False
  assemblySem := fun _ _ _ _ _ _ _ _ => False

attribute [local instance] internalExternalCalls

local instance : CC.ExternalCallsDeterministic internalExternalCalls where
  functions := fun _ _ _ =>
    ⟨fun _ _ _ _ _ _ _ _ h => h.elim, fun _ _ _ _ _ h => h.elim⟩
  assembly := fun _ _ _ =>
    ⟨fun _ _ _ _ _ _ _ _ h => h.elim, fun _ _ _ _ _ h => h.elim⟩

/-- The Clight transition relation of `polynomialLibrary` under `internalExternalCalls`. -/
def polynomialStep : CC.State → CC.Trace → CC.State → Prop :=
  CC.Step2 polynomialLibrary.globalenv

/-- `polynomialCall order` runs silently to `Returnstate (Vfloat (Polynomial.result order))`
with `initialMemory` unchanged, from `callback_execution`. -/
theorem polynomial_call_execution (order : Polynomial.Order) :
    CC.StarE0 polynomialStep (polynomialCall order)
      (.Returnstate (.Vfloat (Polynomial.result order)) .Kstop initialMemory) :=
  callback_execution (.Internal ClightSource.f_testfun) (testfun Polynomial.cosine)
    polynomial_callback_contract order .Kstop

/-- The wrapper call runs silently to the two-point result, from the interpreter run through
`runCall_sound`. -/
theorem polynomial_wrapper_execution :
    CC.StarE0 polynomialStep polynomialWrapperCall
      (.Returnstate (.Vfloat (Polynomial.result .two)) .Kstop initialMemory) :=
  runCall_sound _ _ _ _ _ polynomial_wrapper_run

/-- A finished call has no successor under `polynomialStep`. -/
theorem return_no_step (value : CC.Val) (memory : CC.Mem)
    (trace : CC.Trace) (state : CC.State) :
    ¬ polynomialStep (.Returnstate value .Kstop memory) trace state := by
  intro h
  cases h

/-- Total-correctness package: every run from the call is silent and can finish with the stated
value and memory. -/
theorem polynomial_prefix (order : Polynomial.Order) (trace : CC.Trace) (state : CC.State)
    (h : CC.Star polynomialStep (polynomialCall order) trace state) :
    trace = CC.E0 ∧ CC.StarE0 polynomialStep state
      (.Returnstate (.Vfloat (Polynomial.result order)) .Kstop initialMemory) :=
  silent_execution_prefix polynomialLibrary (polynomial_call_execution order)
    (return_no_step _ _) h

/-- Total-correctness package: every finished run ends in the stated return state. -/
theorem polynomial_return_state (order : Polynomial.Order) (value : CC.Val) (memory : CC.Mem)
    (trace : CC.Trace)
    (h : CC.Star polynomialStep (polynomialCall order) trace
      (.Returnstate value .Kstop memory)) :
    CC.State.Returnstate value .Kstop memory =
      .Returnstate (.Vfloat (Polynomial.result order)) .Kstop initialMemory :=
  CC.starE0_of_stuck (polynomial_prefix order trace _ h).2 (return_no_step value memory)

/-- Total-correctness package: the returned value is `Vfloat (Polynomial.result order)` bit for
bit, including the sign of zero. -/
theorem polynomial_return_eq (order : Polynomial.Order) (value : CC.Val) (memory : CC.Mem)
    (trace : CC.Trace)
    (h : CC.Star polynomialStep (polynomialCall order) trace
      (.Returnstate value .Kstop memory)) :
    value = .Vfloat (Polynomial.result order) :=
  (CC.State.Returnstate.inj (polynomial_return_state order value memory trace h)).1

/-- Total-correctness package: the returned memory is `initialMemory`. -/
theorem polynomial_return_memory (order : Polynomial.Order) (value : CC.Val) (memory : CC.Mem)
    (trace : CC.Trace)
    (h : CC.Star polynomialStep (polynomialCall order) trace
      (.Returnstate value .Kstop memory)) :
    memory = initialMemory :=
  (CC.State.Returnstate.inj (polynomial_return_state order value memory trace h)).2.2

/-- Total-correctness package: every reachable state is the stated return state or has a silent
successor. -/
theorem polynomial_progress (order : Polynomial.Order) (trace : CC.Trace) (state : CC.State)
    (h : CC.Star polynomialStep (polynomialCall order) trace state) :
    state = .Returnstate (.Vfloat (Polynomial.result order)) .Kstop initialMemory ∨
      ∃ next, polynomialStep state CC.E0 next := by
  have hremaining := (polynomial_prefix order trace state h).2
  cases hremaining with
  | refl => exact Or.inl rfl
  | step _ next _ hstep _ => exact Or.inr ⟨next, hstep⟩

/-- Total-correctness package: no infinite sequence of steps starts at the call. -/
theorem polynomial_not_infinite (order : Polynomial.Order)
    (states : Nat → CC.State) (traces : Nat → CC.Trace)
    (hstart : states 0 = polynomialCall order)
    (hsteps : ∀ n, polynomialStep (states n) (traces n) (states (n + 1))) : False :=
  silent_execution_not_infinite polynomialLibrary (polynomial_call_execution order)
    (return_no_step _ _) states traces hstart hsteps

/-- Every value returned by `polynomialCall order` is finite and within
`Polynomial.errorBound order` of ∫₋₁¹ ½(1−x)cos x dx, by `Polynomial.integral_accuracy`. -/
theorem polynomial_return_accuracy (order : Polynomial.Order) (value : Value)
    (memory : CC.Mem) (trace : CC.Trace)
    (h : CC.Star polynomialStep (polynomialCall order) trace
      (.Returnstate (.Vfloat value) .Kstop memory)) :
    Model.isFinite value = true ∧
      |Model.toReal value - ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤
        Polynomial.errorBound order := by
  have heq := CC.Val.Vfloat.inj (polynomial_return_eq order (.Vfloat value) memory trace h)
  rw [heq]
  exact Polynomial.integral_accuracy order

end Quadrature.Binary64.Clight
