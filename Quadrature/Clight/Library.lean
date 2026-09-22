import Quadrature.Clight.Program

/-!
# Quadrature in a surrounding Clight program

`library_execution` proves that the imported integrator `f_integrate` returns
`Vfloat (integrate f (Polynomial.terms order))` with unchanged memory, for
orders one through four, in any global environment and memory satisfying
`LibraryContext` and for any callback satisfying `LibraryCallbackContract`.
The context names the accessor functions and the table cells the order reads.
It fixes neither block numbers nor unrelated memory. The `library_*` theorems
form the total-correctness package for this call (vocabulary: see
`Quadrature.Clight.Execution`), using the surrounding program's symbol
injectivity and deterministic external calls. The `polynomial_callback_*`
theorems discharge the callback contract for the original callback with the
internal polynomial at `cos`.
-/

namespace Quadrature.Binary64.Clight

open FloatLib.Floats.Formats.BinaryInterchange
open ClightSource

/-- `LibraryContext ge memory order`: the symbols `gauss_pts`, `gauss_wts`, `gauss_point` and
`gauss_weight` resolve to blocks, and the two accessor pointers are bound to the imported accessor
bodies. For the pair `(w, x)` at index `i` of `Polynomial.terms order`, the weights table holds
`w` and the nodes table holds `x` at byte offset `8 * (n(n-1)/2 + i)`, where
`n = orderCount order`. Discharged by `callbackLibrary_context` for the initialized library. -/
structure LibraryContext (ge : CC.CGenv) (memory : CC.Mem) (order : Polynomial.Order) where
  nodes : CC.Block
  weights : CC.Block
  point : CC.Block
  weight : CC.Block
  nodes_symbol : CC.Genv.findSymbol ge.genv_genv _gauss_pts = some nodes
  weights_symbol : CC.Genv.findSymbol ge.genv_genv _gauss_wts = some weights
  point_symbol : CC.Genv.findSymbol ge.genv_genv _gauss_point = some point
  weight_symbol : CC.Genv.findSymbol ge.genv_genv _gauss_weight = some weight
  point_function : CC.Genv.findFunct ge.genv_genv (.Vptr point CC.Integers.Ptrofs.zero) =
    some (.Internal f_gauss_point)
  weight_function : CC.Genv.findFunct ge.genv_genv (.Vptr weight CC.Integers.Ptrofs.zero) =
    some (.Internal f_gauss_weight)
  node_load : ∀ (i : Nat) (term : Value × Value), (Polynomial.terms order)[i]? = some term →
    CC.Mem.load .Mfloat64 memory nodes
      (8 * (orderCount order * (orderCount order - 1) / 2 + i) : Nat) =
      some (.Vfloat term.2)
  weight_load : ∀ (i : Nat) (term : Value × Value), (Polynomial.terms order)[i]? = some term →
    CC.Mem.load .Mfloat64 memory weights
      (8 * (orderCount order * (orderCount order - 1) / 2 + i) : Nat) =
      some (.Vfloat term.1)

/-- `LibraryCallbackContract ge memory ptr fd f`: `ptr` resolves to `fd`, `fd` has type
`double (double)`, and calling `fd` on `Vfloat x` from `memory` under any call continuation `k`
returns `Vfloat (f x)` silently with `memory` unchanged. Nothing is assumed about the enclosing
integrator. Discharged by `polynomial_callback_contract_in_context` for the original callback. -/
structure LibraryCallbackContract [CC.ExternalCalls] (ge : CC.CGenv) (memory : CC.Mem)
    (ptr : CC.Val) (fd : CC.FunDef) (f : Value → Value) : Prop where
  function_eq : CC.Genv.findFunct ge.genv_genv ptr = some fd
  type_eq : CC.typeOfFundef fd = .Tfunction [CC.tdouble] CC.tdouble CC.cc_default
  execution : ∀ (x : Value) (k : CC.Cont), CC.isCallCont k = true →
    CC.StarE0 (CC.Step2 ge) (.Callstate fd [.Vfloat x] k memory)
      (.Returnstate (.Vfloat (f x)) k memory)

/-- The state entering `f_integrate` with callback pointer `ptr`, node count `orderCount order`,
continuation `k` and memory `memory`. The caller has already resolved the function body. -/
def libraryCall (ptr : CC.Val) (order : Polynomial.Order) (k : CC.Cont)
    (memory : CC.Mem) : CC.State :=
  .Callstate (.Internal f_integrate)
    [ptr, .Vint (CC.Integers.Int.repr (orderCount order))] k memory

private theorem array_address (ge : CC.CGenv) (le : CC.TempEnv) (m : CC.Mem)
    (id : CC.Ident) (b : CC.Block) (index : CC.Expr) (n : CC.Integers.Int)
    (ofs : CC.Integers.Ptrofs)
    (hsym : CC.Genv.findSymbol ge.genv_genv id = some b)
    (hindex : CC.doEvalExpr ge CC.emptyEnv le m index = some (.Vint n))
    (hadd : CC.Cop.semBinaryOperation ge.genv_cenv .Oadd
      (.Vptr b CC.Integers.Ptrofs.zero) (CC.tarray CC.tdouble 55)
      (.Vint n) (CC.typeof index) m = some (.Vptr b ofs)) :
    CC.doEvalExpr ge CC.emptyEnv le m
      (.Ebinop .Oadd (.Evar id (CC.tarray CC.tdouble 55)) index (CC.tptr CC.tdouble)) =
        some (.Vptr b ofs) := by
  rw [CC.doEvalExpr, global_reference ge le m id _ b (by rfl) hsym, hindex]
  exact hadd

-- Unfold the imported loop for each of the four orders, taking loads and calls from the context.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- Given a `LibraryContext` and a callback meeting `LibraryCallbackContract`, the call
`libraryCall ptr order k m` runs silently to `Returnstate (Vfloat (integrate f terms)) k m`
with `terms = Polynomial.terms order` and memory `m` unchanged. -/
theorem library_execution [CC.ExternalCalls] (ge : CC.CGenv) (m : CC.Mem)
    (order : Polynomial.Order) (ctx : LibraryContext ge m order)
    (fd : CC.FunDef) (f : Value → Value) (ptr : CC.Val)
    (contract : LibraryCallbackContract ge m ptr fd f) (k : CC.Cont) :
    CC.StarE0 (CC.Step2 ge) (libraryCall ptr order k m)
      (.Returnstate (.Vfloat (integrate f (Polynomial.terms order))) (CC.callCont k) m) := by
  have hfind := contract.function_eq
  have htype := contract.type_eq
  have hcallback := contract.execution
  cases order <;>
  repeat'
    first
    | (guard_target =~ CC.StarE0 _ (.Returnstate _ (CC.callCont k) _) _
       exact CC.StarE0.refl _)
    | refine starE0_trans (hcallback _ _ (by rfl)) ?_
    | refine CC.StarE0.step _ _ _ (set_float_load
        (array_address _ _ _ _ _ _ _ _ ctx.weights_symbol (by rfl) (by rfl))
        (by
          conv_lhs => arg 4; cbv
          first
          | exact ctx.weight_load 0 _ (by rfl)
          | exact ctx.weight_load 1 _ (by rfl)
          | exact ctx.weight_load 2 _ (by rfl)
          | exact ctx.weight_load 3 _ (by rfl))) ?_
    | refine CC.StarE0.step _ _ _ (set_float_load
        (array_address _ _ _ _ _ _ _ _ ctx.nodes_symbol (by rfl) (by rfl))
        (by
          conv_lhs => arg 4; cbv
          first
          | exact ctx.node_load 0 _ (by rfl)
          | exact ctx.node_load 1 _ (by rfl)
          | exact ctx.node_load 2 _ (by rfl)
          | exact ctx.node_load 3 _ (by rfl))) ?_
    | refine CC.StarE0.step _ _ _ (CC.doStep_sound _ _ _ _ (by rfl)) ?_
    | refine CC.StarE0.step _ _ _ (call_step (by rfl)
        (global_reference _ _ _ _ _ _ (by rfl) ctx.weight_symbol)
        (by rfl) ctx.weight_function (by rfl)) ?_
    | refine CC.StarE0.step _ _ _ (call_step (by rfl)
        (global_reference _ _ _ _ _ _ (by rfl) ctx.point_symbol)
        (by rfl) ctx.point_function (by rfl)) ?_
    | refine CC.StarE0.step _ _ _ (call_step (by rfl)
        (by rfl) (by rfl) hfind htype) ?_


/-- Total-correctness package: every run from the call is silent and can finish with the stated
value and memory. -/
theorem library_prefix [calls : CC.ExternalCalls] [CC.ExternalCallsDeterministic calls]
    (program : CC.Program) (m : CC.Mem) (order : Polynomial.Order)
    (ctx : LibraryContext program.globalenv m order)
    (fd : CC.FunDef) (f : Value → Value) (ptr : CC.Val)
    (contract : LibraryCallbackContract program.globalenv m ptr fd f)
    (trace : CC.Trace) (state : CC.State)
    (h : CC.Star (CC.Step2 program.globalenv) (libraryCall ptr order .Kstop m) trace state) :
    trace = CC.E0 ∧ CC.StarE0 (CC.Step2 program.globalenv) state
      (.Returnstate (.Vfloat (integrate f (Polynomial.terms order))) .Kstop m) :=
  silent_execution_prefix program
    (library_execution program.globalenv m order ctx fd f ptr contract .Kstop)
    (return_stop_no_step _ _ _) h

/-- Total-correctness package: every finished run ends in the stated return state. -/
theorem library_return_state [calls : CC.ExternalCalls] [CC.ExternalCallsDeterministic calls]
    (program : CC.Program) (m : CC.Mem) (order : Polynomial.Order)
    (ctx : LibraryContext program.globalenv m order)
    (fd : CC.FunDef) (f : Value → Value) (ptr : CC.Val)
    (contract : LibraryCallbackContract program.globalenv m ptr fd f)
    (value : CC.Val) (memory : CC.Mem) (trace : CC.Trace)
    (h : CC.Star (CC.Step2 program.globalenv) (libraryCall ptr order .Kstop m) trace
      (.Returnstate value .Kstop memory)) :
    CC.State.Returnstate value .Kstop memory =
      .Returnstate (.Vfloat (integrate f (Polynomial.terms order))) .Kstop m :=
  CC.starE0_of_stuck (library_prefix program m order ctx fd f ptr contract trace _ h).2
    (return_stop_no_step _ value memory)

/-- Total-correctness package: the returned value is `Vfloat (integrate f terms)` bit for bit,
including the sign of zero and any NaN payload. -/
theorem library_return_eq [calls : CC.ExternalCalls] [CC.ExternalCallsDeterministic calls]
    (program : CC.Program) (m : CC.Mem) (order : Polynomial.Order)
    (ctx : LibraryContext program.globalenv m order)
    (fd : CC.FunDef) (f : Value → Value) (ptr : CC.Val)
    (contract : LibraryCallbackContract program.globalenv m ptr fd f)
    (value : CC.Val) (memory : CC.Mem) (trace : CC.Trace)
    (h : CC.Star (CC.Step2 program.globalenv) (libraryCall ptr order .Kstop m) trace
      (.Returnstate value .Kstop memory)) :
    value = .Vfloat (integrate f (Polynomial.terms order)) :=
  (CC.State.Returnstate.inj
    (library_return_state program m order ctx fd f ptr contract value memory trace h)).1

/-- Total-correctness package: the returned memory is the entry memory. -/
theorem library_return_memory [calls : CC.ExternalCalls] [CC.ExternalCallsDeterministic calls]
    (program : CC.Program) (m : CC.Mem) (order : Polynomial.Order)
    (ctx : LibraryContext program.globalenv m order)
    (fd : CC.FunDef) (f : Value → Value) (ptr : CC.Val)
    (contract : LibraryCallbackContract program.globalenv m ptr fd f)
    (value : CC.Val) (memory : CC.Mem) (trace : CC.Trace)
    (h : CC.Star (CC.Step2 program.globalenv) (libraryCall ptr order .Kstop m) trace
      (.Returnstate value .Kstop memory)) :
    memory = m :=
  (CC.State.Returnstate.inj
    (library_return_state program m order ctx fd f ptr contract value memory trace h)).2.2

/-- Total-correctness package: every reachable state is the stated return state or has a silent
successor. -/
theorem library_progress [calls : CC.ExternalCalls] [CC.ExternalCallsDeterministic calls]
    (program : CC.Program) (m : CC.Mem) (order : Polynomial.Order)
    (ctx : LibraryContext program.globalenv m order)
    (fd : CC.FunDef) (f : Value → Value) (ptr : CC.Val)
    (contract : LibraryCallbackContract program.globalenv m ptr fd f)
    (trace : CC.Trace) (state : CC.State)
    (h : CC.Star (CC.Step2 program.globalenv) (libraryCall ptr order .Kstop m) trace state) :
    state = .Returnstate (.Vfloat (integrate f (Polynomial.terms order))) .Kstop m ∨
      ∃ next, CC.Step2 program.globalenv state CC.E0 next := by
  have hremaining := (library_prefix program m order ctx fd f ptr contract trace state h).2
  cases hremaining with
  | refl => exact Or.inl rfl
  | step _ next _ hstep _ => exact Or.inr ⟨next, hstep⟩

/-- Total-correctness package: no infinite sequence of steps starts at the call. -/
theorem library_not_infinite [calls : CC.ExternalCalls] [CC.ExternalCallsDeterministic calls]
    (program : CC.Program) (m : CC.Mem) (order : Polynomial.Order)
    (ctx : LibraryContext program.globalenv m order)
    (fd : CC.FunDef) (f : Value → Value) (ptr : CC.Val)
    (contract : LibraryCallbackContract program.globalenv m ptr fd f)
    (states : Nat → CC.State) (traces : Nat → CC.Trace)
    (hstart : states 0 = libraryCall ptr order .Kstop m)
    (hsteps : ∀ n, CC.Step2 program.globalenv (states n) (traces n) (states (n + 1))) : False :=
  silent_execution_not_infinite program
    (library_execution program.globalenv m order ctx fd f ptr contract .Kstop)
    (return_stop_no_step _ _ _) states traces hstart hsteps

-- Step through `f_testfun`, resolving the `cos` call to `polynomialFunction` and unfolding it.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- In any global environment where `cos` resolves to `polynomialFunction`, calling `f_testfun`
on `Vfloat x` returns `Vfloat (testfun Polynomial.cosine x)` silently with memory unchanged. -/
theorem polynomial_callback_execution_in_context [CC.ExternalCalls]
    (ge : CC.CGenv) (m : CC.Mem) (cosBlock : CC.Block)
    (hsymbol : CC.Genv.findSymbol ge.genv_genv _cos = some cosBlock)
    (hfunction : CC.Genv.findFunct ge.genv_genv (.Vptr cosBlock CC.Integers.Ptrofs.zero) =
      some (.Internal polynomialFunction)) (x : Value) (k : CC.Cont) :
    CC.StarE0 (CC.Step2 ge) (.Callstate (.Internal f_testfun) [.Vfloat x] k m)
      (.Returnstate (.Vfloat (testfun Polynomial.cosine x)) (CC.callCont k) m) := by
  repeat'
    first
    | (guard_target =~ CC.StarE0 _ (.Returnstate _ (CC.callCont k) _) _
       exact CC.StarE0.refl _)
    | refine CC.StarE0.step _ _ _ (CC.doStep_sound _ _ _ _ (by rfl)) ?_
    | refine CC.StarE0.step _ _ _ (call_step (by rfl)
        (global_reference _ _ _ _ _ _ (by rfl) hsymbol) (by rfl) hfunction (by rfl)) ?_

/-- When `ptr` resolves to `f_testfun` and `cos` to `polynomialFunction`, the original callback
satisfies `LibraryCallbackContract` with `f = testfun Polynomial.cosine`. -/
theorem polynomial_callback_contract_in_context [CC.ExternalCalls]
    (ge : CC.CGenv) (m : CC.Mem) (ptr : CC.Val) (cosBlock : CC.Block)
    (hcallback : CC.Genv.findFunct ge.genv_genv ptr = some (.Internal f_testfun))
    (hsymbol : CC.Genv.findSymbol ge.genv_genv _cos = some cosBlock)
    (hfunction : CC.Genv.findFunct ge.genv_genv (.Vptr cosBlock CC.Integers.Ptrofs.zero) =
      some (.Internal polynomialFunction)) :
    LibraryCallbackContract ge m ptr (.Internal f_testfun) (testfun Polynomial.cosine) := by
  refine ⟨hcallback, rfl, ?_⟩
  intro x k hk
  simpa only [callCont_eq_self hk] using
    polynomial_callback_execution_in_context ge m cosBlock hsymbol hfunction x k

/-- Given a `LibraryContext` and the polynomial callback contract, every value returned by the
library call is finite and within `Polynomial.errorBound order` of ∫₋₁¹ ½(1−x)cos x dx. -/
theorem library_polynomial_return_accuracy [calls : CC.ExternalCalls]
    [CC.ExternalCallsDeterministic calls] (program : CC.Program) (m : CC.Mem)
    (order : Polynomial.Order) (ctx : LibraryContext program.globalenv m order) (ptr : CC.Val)
    (contract : LibraryCallbackContract program.globalenv m ptr
      (.Internal f_testfun) (testfun Polynomial.cosine))
    (value : Value) (memory : CC.Mem) (trace : CC.Trace)
    (h : CC.Star (CC.Step2 program.globalenv) (libraryCall ptr order .Kstop m) trace
      (.Returnstate (.Vfloat value) .Kstop memory)) :
    Model.isFinite value = true ∧
      |Model.toReal value - ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤
        Polynomial.errorBound order := by
  have heq := CC.Val.Vfloat.inj (library_return_eq program m order ctx
    (.Internal f_testfun) (testfun Polynomial.cosine) ptr contract (.Vfloat value) memory trace h)
  rw [heq]
  exact Polynomial.integral_accuracy order

end Quadrature.Binary64.Clight
