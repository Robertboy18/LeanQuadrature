import Quadrature.CSource.Frontend.Refinement
import Quadrature.CSource.Library.NormalizedExecution
import Quadrature.CSource.Library.Total

/-!
# Preservation of the six selected C functions

`integrate_refinement` and `wrapper_refinement` connect the typed C bodies
to the actual Clight frontend output. The two accessors, the callback and
the replacement cosine have the same connection below. All function and
table definitions come from the initialized library.

Each theorem supplies a `CallRefinement`: every execution on either side
terminates with the same binary64 value and preserves the caller's memory.
`CallRefinement.outcomes_iff` states the resulting equality of observable
behaviors. The integrator covers the initialized callback and orders zero
through ten; the callback and cosine cover every binary64 argument.
-/

namespace Quadrature.CSource.Library

open CC Binary64 Binary64.ClightSource FloatLib.Floats.Formats.BinaryInterchange
open Binary64.Clight

variable [ExternalCalls]

/-- Normalization preserves the cosine's rounded polynomial on every binary64 argument. -/
theorem cosine_refinement (memory : Mem) (x : Value) :
    CallRefinement globalEnv Normalized.program memory (.Internal Cosine.function)
      (.Internal Cosine.normalizedFunction) [.Vfloat x] (.Vfloat (Polynomial.cosine x)) :=
  ⟨Cosine.call_correct globalEnv memory x, Normalized.internal,
    ⟨Cosine.normalized_internal, trivial⟩,
    Cosine.normalized_execution Normalized.program.globalenv memory x .Kstop⟩

/-- Normalization preserves the callback, including its call to the internal cosine. -/
theorem callback_refinement (memory : Mem) (x : Value) :
    CallRefinement globalEnv Normalized.program memory (.Internal Typed.testfun)
      (.Internal f_testfun) [.Vfloat x] (.Vfloat (testfun Polynomial.cosine x)) :=
  ⟨callback_correct.execution memory x, Normalized.internal, ⟨rfl, trivial⟩,
    Normalized.callback_execution memory x .Kstop⟩

/-- Normalization preserves the initialized integrator for every order from zero through ten. -/
theorem integrate_refinement (n : Nat) (hn : n ≤ 10) :
    CallRefinement globalEnv Normalized.program initialMemory (.Internal Typed.integrate)
      (.Internal f_integrate)
      [.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero, .Vint (Integers.Int.repr n)]
      (.Vfloat (StoredPolynomial.result n)) :=
  ⟨integrate_call_correct n hn, Normalized.internal, ⟨rfl, trivial⟩,
    Normalized.integrate_execution n hn .Kstop⟩

/-- Normalization preserves the original two-point wrapper and its complete internal call tree. -/
theorem wrapper_refinement :
    CallRefinement globalEnv Normalized.program initialMemory (.Internal Typed.integrateTestfun)
      (.Internal f_integrate_testfun) [] (.Vfloat (StoredPolynomial.result 2)) :=
  ⟨wrapper_call_correct, Normalized.internal, ⟨rfl, trivial⟩,
    Normalized.wrapper_execution .Kstop⟩

omit [ExternalCalls] in
private theorem table_loads {memory : Mem} {nodes weights : Block} {n start i : Nat}
    {terms : List (Value × Value)} {term : Value × Value}
    (hcells : TableCells memory nodes weights n start terms)
    (hterm : terms[i]? = some term) :
    Mem.load .Mfloat64 memory weights (8 * tableOffset n (start + i) : Nat) =
        some (.Vfloat term.1) ∧
      Mem.load .Mfloat64 memory nodes (8 * tableOffset n (start + i) : Nat) =
        some (.Vfloat term.2) := by
  induction terms generalizing start i with
  | nil => simp at hterm
  | cons first rest ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hterm
          subst first
          exact ⟨hcells.1, hcells.2.1⟩
      | succ i =>
          simpa only [Nat.add_right_comm, Nat.add_assoc, Nat.succ_eq_add_one] using
            ih hcells.2.2 hterm

omit [ExternalCalls] in
private theorem stored_loads (n i : Nat) (hn : n ≤ 10) (term : Value × Value)
    (hterm : (storedTerms n)[i]? = some term) :
    Mem.load .Mfloat64 initialMemory (Positive.ofNat 2) (8 * tableOffset n i : Nat) =
        some (.Vfloat term.1) ∧
      Mem.load .Mfloat64 initialMemory (Positive.ofNat 1) (8 * tableOffset n i : Nat) =
        some (.Vfloat term.2) := by
  simpa only [Nat.zero_add, initialMemory] using table_loads (stored_table_cells n hn) hterm

/-- Normalization preserves every initialized node-table lookup in the stored rules. -/
theorem point_refinement (n i : Nat) (hn : n ≤ 10) (term : Value × Value)
    (hterm : (storedTerms n)[i]? = some term) :
    CallRefinement globalEnv Normalized.program initialMemory
      (.Internal (Typed.accessor _gauss_pts)) (.Internal f_gauss_point)
      [.Vint (Integers.Int.repr i), .Vint (Integers.Int.repr n)] (.Vfloat term.2) := by
  have hi : i ≤ 10 := by
    have hi := (List.getElem?_eq_some_iff.mp hterm).1
    rw [stored_terms_length n hn] at hi
    omega
  have hload := (stored_loads n i hn term hterm).2
  exact ⟨C.accessor_call_correct globalEnv initialMemory _gauss_pts (Positive.ofNat 1)
      n i term.2 hn hi (by decide) (by decide) rfl hload,
    Normalized.internal, ⟨rfl, trivial⟩,
    accessor_execution Normalized.program.globalenv initialMemory _gauss_pts (Positive.ofNat 1)
      n i term.2 .Kstop hn hi rfl hload⟩

/-- Normalization preserves every initialized weight-table lookup in the stored rules. -/
theorem weight_refinement (n i : Nat) (hn : n ≤ 10) (term : Value × Value)
    (hterm : (storedTerms n)[i]? = some term) :
    CallRefinement globalEnv Normalized.program initialMemory
      (.Internal (Typed.accessor _gauss_wts)) (.Internal f_gauss_weight)
      [.Vint (Integers.Int.repr i), .Vint (Integers.Int.repr n)] (.Vfloat term.1) := by
  have hi : i ≤ 10 := by
    have hi := (List.getElem?_eq_some_iff.mp hterm).1
    rw [stored_terms_length n hn] at hi
    omega
  have hload := (stored_loads n i hn term hterm).1
  exact ⟨C.accessor_call_correct globalEnv initialMemory _gauss_wts (Positive.ofNat 2)
      n i term.1 hn hi (by decide) (by decide) rfl hload,
    Normalized.internal, ⟨rfl, trivial⟩,
    accessor_execution Normalized.program.globalenv initialMemory _gauss_wts (Positive.ofNat 2)
      n i term.1 .Kstop hn hi rfl hload⟩

end Quadrature.CSource.Library
