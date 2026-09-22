import Quadrature.Clight.Library

/-!
# Clight quadrature with a callback contract

`callbackLibrary fd` is `polynomialLibrary` with the `testfun` definition
replaced by an arbitrary `fd`. The two initialized tables, the wrapper and the
internal cosine polynomial are unchanged. `callback_execution` proves that the
imported integrator returns `Vfloat (integrate f (Polynomial.terms order))`
with unchanged memory, for orders one through four, whenever `fd` satisfies
`CallbackContract fd f`, and the `callback_*` theorems form the
total-correctness package (vocabulary: see `Quadrature.Clight.Execution`). The
theorem for an arbitrary surrounding program is `library_execution` in
`Quadrature.Clight.Library`, which this file instantiates.
-/

namespace Quadrature.Binary64.Clight

open FloatLib.Floats.Formats.BinaryInterchange
open ClightSource

/-- `polynomialLibrary` with the definition at the `testfun` symbol replaced by `fd`. Every other
global, and hence every block number, is the same. -/
def callbackLibrary (fd : CC.FunDef) : CC.Program :=
  CC.mkprogram []
    [(_gauss_pts, .Gvar (tableGlobal ClightTableData.nodeBits)),
     (_gauss_wts, .Gvar (tableGlobal ClightTableData.weightBits)),
     (_gauss_point, .Gfun (.Internal f_gauss_point)),
     (_gauss_weight, .Gfun (.Internal f_gauss_weight)),
     (_integrate, .Gfun (.Internal f_integrate)),
     (_testfun, .Gfun fd),
     (_integrate_testfun, .Gfun (.Internal f_integrate_testfun)),
     (_cos, .Gfun (.Internal polynomialFunction))]
    [] _integrate_testfun

/-- With the original callback, `callbackLibrary` is `polynomialLibrary`. -/
theorem callbackLibrary_polynomial :
    callbackLibrary (.Internal f_testfun) = polynomialLibrary := rfl

/-- The library declares no composite types, whatever the callback definition. -/
theorem callbackLibrary_composites (fd : CC.FunDef) :
    CC.compositesWellFormed (callbackLibrary fd) = true := rfl

-- Initialization never reads a function body, so this reduces to `polynomialLibrary_initialized`.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- Every `callbackLibrary fd` initializes to `initialMemory`, since global initialization does not
depend on function bodies. -/
theorem callbackLibrary_initialized (fd : CC.FunDef) :
    (callbackLibrary fd).initMem = some initialMemory := by
  have h : (callbackLibrary fd).initMem = polynomialLibrary.initMem := by rfl
  rw [h]
  exact polynomialLibrary_initialized

/-- The state entering the imported `integrate` with the `testfun` pointer and `orderCount order`
nodes, from `initialMemory` under continuation `k`. -/
def callbackCall (order : Polynomial.Order) (k : CC.Cont) : CC.State :=
  .Callstate (.Internal f_integrate)
    [.Vptr testfunBlock (CC.Integers.Ptrofs.repr 0),
     .Vint (CC.Integers.Int.repr (orderCount order))]
    k initialMemory

/-- `CallbackContract fd f`: `fd` has type `double (double)` and, in `callbackLibrary fd` from
`initialMemory`, calling it on `Vfloat x` under any call continuation returns `Vfloat (f x)`
silently with memory unchanged. Only the callback is constrained. Discharged for the original
callback by `polynomial_callback_contract`. -/
structure CallbackContract [CC.ExternalCalls] (fd : CC.FunDef) (f : Value → Value) : Prop where
  type_eq : CC.typeOfFundef fd = .Tfunction [CC.tdouble] CC.tdouble CC.cc_default
  execution : ∀ (x : Value) (k : CC.Cont), CC.isCallCont k = true →
    CC.StarE0 (CC.Step2 (callbackLibrary fd).globalenv)
      (.Callstate fd [.Vfloat x] k initialMemory)
      (.Returnstate (.Vfloat (f x)) k initialMemory)

-- Check the symbol table and the table loads of each order against the initialized memory.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- The initialized `callbackLibrary fd` satisfies `LibraryContext` for every supported order: the
tables are blocks 1 and 2, the accessors blocks 3 and 4, and each table load is checked by
`rfl`. -/
def callbackLibrary_context (fd : CC.FunDef) (order : Polynomial.Order) :
    LibraryContext (callbackLibrary fd).globalenv initialMemory order where
  nodes := CC.Positive.ofNat 1
  weights := CC.Positive.ofNat 2
  point := CC.Positive.ofNat 3
  weight := CC.Positive.ofNat 4
  nodes_symbol := by rfl
  weights_symbol := by rfl
  point_symbol := by rfl
  weight_symbol := by rfl
  point_function := by rfl
  weight_function := by rfl
  node_load := by
    intro i term hterm
    have hi := (List.getElem?_eq_some_iff.mp hterm).1
    have hlen : (Polynomial.terms order).length = orderCount order := by
      cases order <;> rfl
    rw [hlen] at hi
    cases order <;> dsimp [orderCount] at hi <;> interval_cases i <;>
      cases Option.some.inj hterm <;> rfl
  weight_load := by
    intro i term hterm
    have hi := (List.getElem?_eq_some_iff.mp hterm).1
    have hlen : (Polynomial.terms order).length = orderCount order := by
      cases order <;> rfl
    rw [hlen] at hi
    cases order <;> dsimp [orderCount] at hi <;> interval_cases i <;>
      cases Option.some.inj hterm <;> rfl

/-- A `CallbackContract` yields the `LibraryCallbackContract` of `Clight/Library` for the pointer
to `testfunBlock` in `callbackLibrary fd`. -/
theorem CallbackContract.library_contract [CC.ExternalCalls]
    {fd : CC.FunDef} {f : Value → Value} (contract : CallbackContract fd f) :
    LibraryCallbackContract (callbackLibrary fd).globalenv initialMemory
      (.Vptr testfunBlock (CC.Integers.Ptrofs.repr 0)) fd f :=
  ⟨by rfl, contract.type_eq, contract.execution⟩

/-- Given `CallbackContract fd f`, `callbackCall order k` runs silently to
`Returnstate (Vfloat (integrate f (Polynomial.terms order))) k initialMemory`. This is
`library_execution` in the initialized callback library. -/
theorem callback_execution [CC.ExternalCalls] (fd : CC.FunDef) (f : Value → Value)
    (contract : CallbackContract fd f) (order : Polynomial.Order) (k : CC.Cont) :
    CC.StarE0 (CC.Step2 (callbackLibrary fd).globalenv) (callbackCall order k)
      (.Returnstate (.Vfloat (integrate f (Polynomial.terms order)))
        (CC.callCont k) initialMemory) :=
  library_execution _ initialMemory order (callbackLibrary_context fd order) fd f
    (.Vptr testfunBlock (CC.Integers.Ptrofs.repr 0)) contract.library_contract k

/-- Total-correctness package: every run from the call is silent and can finish with the stated
value and memory. -/
theorem callback_prefix [calls : CC.ExternalCalls] [CC.ExternalCallsDeterministic calls]
    (fd : CC.FunDef) (f : Value → Value) (contract : CallbackContract fd f)
    (order : Polynomial.Order) (trace : CC.Trace) (state : CC.State)
    (h : CC.Star (CC.Step2 (callbackLibrary fd).globalenv) (callbackCall order .Kstop)
      trace state) :
    trace = CC.E0 ∧ CC.StarE0 (CC.Step2 (callbackLibrary fd).globalenv) state
      (.Returnstate (.Vfloat (integrate f (Polynomial.terms order))) .Kstop initialMemory) :=
  silent_execution_prefix (callbackLibrary fd) (callback_execution fd f contract order .Kstop)
    (return_stop_no_step _ _ _) h

/-- Total-correctness package: every finished run ends in the stated return state. -/
theorem callback_return_state [calls : CC.ExternalCalls] [CC.ExternalCallsDeterministic calls]
    (fd : CC.FunDef) (f : Value → Value) (contract : CallbackContract fd f)
    (order : Polynomial.Order) (value : CC.Val) (memory : CC.Mem) (trace : CC.Trace)
    (h : CC.Star (CC.Step2 (callbackLibrary fd).globalenv) (callbackCall order .Kstop)
      trace (.Returnstate value .Kstop memory)) :
    CC.State.Returnstate value .Kstop memory =
      .Returnstate (.Vfloat (integrate f (Polynomial.terms order))) .Kstop initialMemory :=
  CC.starE0_of_stuck (callback_prefix fd f contract order trace _ h).2
    (return_stop_no_step _ value memory)

/-- Total-correctness package: the returned value is `Vfloat (integrate f terms)` bit for bit,
including the sign of zero and any NaN payload. -/
theorem callback_return_eq [calls : CC.ExternalCalls] [CC.ExternalCallsDeterministic calls]
    (fd : CC.FunDef) (f : Value → Value) (contract : CallbackContract fd f)
    (order : Polynomial.Order) (value : CC.Val) (memory : CC.Mem) (trace : CC.Trace)
    (h : CC.Star (CC.Step2 (callbackLibrary fd).globalenv) (callbackCall order .Kstop)
      trace (.Returnstate value .Kstop memory)) :
    value = .Vfloat (integrate f (Polynomial.terms order)) :=
  (CC.State.Returnstate.inj
    (callback_return_state fd f contract order value memory trace h)).1

/-- Total-correctness package: the returned memory is `initialMemory`. -/
theorem callback_return_memory [calls : CC.ExternalCalls] [CC.ExternalCallsDeterministic calls]
    (fd : CC.FunDef) (f : Value → Value) (contract : CallbackContract fd f)
    (order : Polynomial.Order) (value : CC.Val) (memory : CC.Mem) (trace : CC.Trace)
    (h : CC.Star (CC.Step2 (callbackLibrary fd).globalenv) (callbackCall order .Kstop)
      trace (.Returnstate value .Kstop memory)) :
    memory = initialMemory :=
  (CC.State.Returnstate.inj
    (callback_return_state fd f contract order value memory trace h)).2.2

/-- Total-correctness package: every reachable state is the stated return state or has a silent
successor. -/
theorem callback_progress [calls : CC.ExternalCalls] [CC.ExternalCallsDeterministic calls]
    (fd : CC.FunDef) (f : Value → Value) (contract : CallbackContract fd f)
    (order : Polynomial.Order) (trace : CC.Trace) (state : CC.State)
    (h : CC.Star (CC.Step2 (callbackLibrary fd).globalenv) (callbackCall order .Kstop)
      trace state) :
    state = .Returnstate (.Vfloat (integrate f (Polynomial.terms order))) .Kstop initialMemory ∨
      ∃ next, CC.Step2 (callbackLibrary fd).globalenv state CC.E0 next := by
  have hremaining := (callback_prefix fd f contract order trace state h).2
  cases hremaining with
  | refl => exact Or.inl rfl
  | step _ next _ hstep _ => exact Or.inr ⟨next, hstep⟩

/-- Total-correctness package: no infinite sequence of steps starts at the call. -/
theorem callback_not_infinite [calls : CC.ExternalCalls]
    [CC.ExternalCallsDeterministic calls] (fd : CC.FunDef) (f : Value → Value)
    (contract : CallbackContract fd f) (order : Polynomial.Order)
    (states : Nat → CC.State) (traces : Nat → CC.Trace)
    (hstart : states 0 = callbackCall order .Kstop)
    (hsteps : ∀ n, CC.Step2 (callbackLibrary fd).globalenv
      (states n) (traces n) (states (n + 1))) : False :=
  silent_execution_not_infinite (callbackLibrary fd)
    (callback_execution fd f contract order .Kstop) (return_stop_no_step _ _ _)
    states traces hstart hsteps

/-- In `polynomialLibrary`, calling the original `f_testfun` on `Vfloat x` returns
`Vfloat (testfun Polynomial.cosine x)` silently with memory unchanged, for every binary64 `x`. -/
theorem polynomial_callback_execution [CC.ExternalCalls] (x : Value) (k : CC.Cont) :
    CC.StarE0 (CC.Step2 (callbackLibrary (.Internal f_testfun)).globalenv)
      (.Callstate (.Internal f_testfun) [.Vfloat x] k initialMemory)
      (.Returnstate (.Vfloat (testfun Polynomial.cosine x)) (CC.callCont k) initialMemory) :=
  polynomial_callback_execution_in_context _ initialMemory (CC.Positive.ofNat 8)
    (by rfl) (by rfl) x k

/-- The original callback `f_testfun` satisfies `CallbackContract` with
`f = testfun Polynomial.cosine`. -/
theorem polynomial_callback_contract [CC.ExternalCalls] :
    CallbackContract (.Internal f_testfun) (testfun Polynomial.cosine) := by
  refine ⟨rfl, ?_⟩
  intro x k hk
  simpa only [callCont_eq_self hk] using polynomial_callback_execution x k

end Quadrature.Binary64.Clight
