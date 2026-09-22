import Quadrature.CSource.Library.Normalized
import Quadrature.Clight.StoredAccuracy

/-!
# Execution of the frontend's complete Clight output

`integrate_execution` covers every stored order, including the empty rule.
`wrapper_execution` covers the original two-point entry point. Both use
the cosine function produced by the frontend, whose execution is proved
from its body in `Cosine.normalized_execution`.

The results hold for any interpretation of external calls: each call stays
inside the initialized library. The execution preserves the initial memory
because normalization places the C parameters and locals in temporaries.
-/

namespace Quadrature.CSource.Library.Normalized

open CC Binary64 Binary64.ClightSource FloatLib.Floats.Formats.BinaryInterchange
open Binary64.Clight

variable [ExternalCalls]

-- Follow the callback's control steps, using the proved execution at its internal cosine call.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- The normalized callback uses the normalized cosine and preserves memory. -/
theorem callback_execution (memory : Mem) (x : Value) (cont : CC.Cont) :
    StarE0 (Step2 program.globalenv) (.Callstate (.Internal f_testfun) [.Vfloat x] cont memory)
      (.Returnstate (.Vfloat (testfun Polynomial.cosine x)) (callCont cont) memory) := by
  repeat'
    first
    | (guard_target =~ StarE0 _ (.Returnstate _ (callCont cont) _) _
       exact StarE0.refl _)
    | refine starE0_trans (Cosine.normalized_execution _ _ _ _) ?_
    | refine StarE0.step _ _ _ (doStep_sound _ _ _ _ (by rfl)) ?_

/-- The initialized normalized callback satisfies the integrator's call contract. -/
theorem callback_contract (memory : Mem) :
    LibraryCallbackContract program.globalenv memory (.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero)
      (.Internal f_testfun) (testfun Polynomial.cosine) := by
  refine ⟨callback_function, rfl, ?_⟩
  intro x cont hcont
  simpa only [callCont_eq_self hcont] using callback_execution memory x cont

/-- The frontend's integrator returns the stored result for every order from zero through ten. -/
theorem integrate_execution (n : Nat) (hn : n ≤ 10) (cont : CC.Cont) :
    StarE0 (Step2 program.globalenv)
      (storedLibraryCall (.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero) n cont initialMemory)
      (.Returnstate (.Vfloat (StoredPolynomial.result n)) (callCont cont) initialMemory) := by
  simpa only [stored_terms_length n hn, StoredPolynomial.result] using
    stored_library_execution program.globalenv initialMemory (storedTerms n) (storedContext n hn)
      (.Internal f_testfun) (testfun Polynomial.cosine)
      (.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero) (callback_contract initialMemory) cont

-- Step through the wrapper, composing the integrator theorem at its only call.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- The original wrapper, as normalized from the C source, returns the two-point result. -/
theorem wrapper_execution (cont : CC.Cont) :
    StarE0 (Step2 program.globalenv)
      (.Callstate (.Internal f_integrate_testfun) [] cont initialMemory)
      (.Returnstate (.Vfloat (StoredPolynomial.result 2)) (callCont cont) initialMemory) := by
  repeat'
    first
    | (guard_target =~ StarE0 _ (.Returnstate _ (callCont cont) _) _
       exact StarE0.refl _)
    | refine starE0_trans (integrate_execution 2 (by decide) _) ?_
    | refine StarE0.step _ _ _ (doStep_sound _ _ _ _ (by rfl)) ?_

end Quadrature.CSource.Library.Normalized
