import Quadrature.CSource.Frontend.InitializedRefinement
import Quadrature.CSource.Library.Refinement

/-!
# Behavioral preservation from the two C source files

`parsed_refinement` is the source-to-Clight theorem for this library.
It identifies both frontend outputs, proves initialization succeeds, resolves
the selected function in each output and supplies total behavioral preservation.
`SupportedCall` spells out the covered inputs for all six exported functions.

`initialized_outcomes_iff` compares every returned value and trace by function
name. The `CallRefinement` certificates also exclude divergence and stuck
states and relate the final memories. This is preservation for the selected
library calls, not a theorem about arbitrary C source or a Lean–Rocq translation.
-/

namespace Quadrature.CSource.Library

open CC Binary64 Binary64.ClightSource FloatLib.Floats.Formats.BinaryInterchange
open Binary64.Clight

/-- The inputs and results covered by the library's preservation theorem.
The callback and cosine accept every binary64 value; integral bounds concern finite arguments
in the quadrature example. Integrator counts are zero through ten, and accessor indices select
an actual cell of the corresponding stored rule. -/
inductive SupportedCall : Ident → List Val → Val → Prop where
  /-- A node from one of the ten stored rules. -/
  | point (n i : Nat) (hn : n ≤ 10) (term : Value × Value)
      (hterm : (storedTerms n)[i]? = some term) :
      SupportedCall _gauss_point [.Vint (Integers.Int.repr i), .Vint (Integers.Int.repr n)]
        (.Vfloat term.2)
  /-- A weight from one of the ten stored rules. -/
  | weight (n i : Nat) (hn : n ≤ 10) (term : Value × Value)
      (hterm : (storedTerms n)[i]? = some term) :
      SupportedCall _gauss_weight [.Vint (Integers.Int.repr i), .Vint (Integers.Int.repr n)]
        (.Vfloat term.1)
  /-- The initialized polynomial callback integrated with zero through ten nodes. -/
  | integrate (n : Nat) (hn : n ≤ 10) :
      SupportedCall _integrate
        [.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero, .Vint (Integers.Int.repr n)]
        (.Vfloat (StoredPolynomial.result n))
  /-- The original callback with the internal polynomial at `cos`. -/
  | callback (x : Value) :
      SupportedCall _testfun [.Vfloat x] (.Vfloat (testfun Polynomial.cosine x))
  /-- The original entry point requesting two nodes. -/
  | wrapper : SupportedCall _integrate_testfun [] (.Vfloat (StoredPolynomial.result 2))
  /-- The shipped cosine polynomial, including the exact binary64 operation order. -/
  | cosine (x : Value) :
      SupportedCall _cos [.Vfloat x] (.Vfloat (Polynomial.cosine x))

variable [ExternalCalls]

/-- Initialization and actual symbol lookup establish preservation for all six functions. -/
theorem initialized_refinement {name : Ident} {args : List Val} {result : Val}
    (hcall : SupportedCall name args result) :
    InitializedRefinement polynomialLibrary Normalized.program name args result := by
  cases hcall with
  | point n i hn term hterm =>
      exact ⟨initialMemory, Positive.ofNat 3, _, _, initialized _, Normalized.initialized,
        rfl, rfl, rfl, rfl, point_refinement n i hn term hterm⟩
  | weight n i hn term hterm =>
      exact ⟨initialMemory, Positive.ofNat 4, _, _, initialized _, Normalized.initialized,
        rfl, rfl, rfl, rfl, weight_refinement n i hn term hterm⟩
  | integrate n hn =>
      exact ⟨initialMemory, Positive.ofNat 5, _, _, initialized _, Normalized.initialized,
        rfl, rfl, rfl, rfl, integrate_refinement n hn⟩
  | callback x =>
      exact ⟨initialMemory, Positive.ofNat 6, _, _, initialized _, Normalized.initialized,
        rfl, rfl, rfl, rfl, callback_refinement initialMemory x⟩
  | wrapper =>
      exact ⟨initialMemory, Positive.ofNat 7, _, _, initialized _, Normalized.initialized,
        rfl, rfl, rfl, rfl, wrapper_refinement⟩
  | cosine x =>
      exact ⟨initialMemory, Positive.ofNat 8, _, _, initialized _, Normalized.initialized,
        rfl, rfl, rfl, rfl, cosine_refinement initialMemory x⟩

/-- The outputs obtained from the retained quadrature source and shipped cosine have the
same total behavior for every supported call. This includes their actual global initialization. -/
theorem parsed_refinement :
    ∃ library program,
      fromSources CSourceData.source Cosine.source = some library ∧
      Normalized.fromSources CSourceData.source Cosine.source = some program ∧
      ∀ name args result, SupportedCall name args result →
        InitializedRefinement library program name args result :=
  ⟨polynomialLibrary, Normalized.program, from_sources, Normalized.from_sources,
    fun _ _ _ hcall => initialized_refinement hcall⟩

/-- Calls by exported name have exactly the same returned values and traces in C and Clight. -/
theorem initialized_outcomes_iff {name : Ident} {args : List Val} {result : Val}
    (hcall : SupportedCall name args result) (trace : Trace) (value : Val) :
    polynomialLibrary.InitializedOutcome name args trace value ↔
      ClightOutcome Normalized.program name args trace value :=
  (initialized_refinement hcall).outcomes_iff trace value

/-- The two frontends preserve the wrapper's exact result, with existence of a return on both
sides. Its integral-error theorem is `Library.parsed_wrapper_total_accuracy`. -/
theorem wrapper_outcomes (trace : Trace) (value : Val) :
    (polynomialLibrary.InitializedOutcome _integrate_testfun [] trace value ↔
      trace = E0 ∧ value = .Vfloat (Model.ofNatBits 0x3fead02c771c35ed)) ∧
    (ClightOutcome Normalized.program _integrate_testfun [] trace value ↔
      trace = E0 ∧ value = .Vfloat (Model.ofNatBits 0x3fead02c771c35ed)) := by
  have h := initialized_refinement SupportedCall.wrapper
  have hbits : StoredPolynomial.result 2 = Model.ofNatBits 0x3fead02c771c35ed :=
    StoredPolynomial.result_value 2 (by decide) (by decide)
  exact ⟨by simpa only [hbits] using h.source_outcome_iff trace value,
    by simpa only [hbits] using h.target_outcome_iff trace value⟩

end Quadrature.CSource.Library
