import Quadrature.Clight.Callbacks
import Quadrature.Clight.Loop

/-!
# Execution with all ten stored rules

The two 55-entry tables of the original C program hold the rules with one
through ten nodes. `storedTerms n` selects the contiguous triangular slice of
the `n`-node rule as (weight, node) pairs, keeping every binary64 encoding.
`stored_table_cells` shows that the initialized memory of `polynomialLibrary`
holds those cells, `stored_context` packages the symbol and memory conditions
of `stored_library_execution`, and the polynomial callback supplies the call
contract. The zero-node case returns positive zero without reading the tables.
These results establish execution and bit-for-bit return values. The integral
error bounds for the ten polynomial applications are in
`Quadrature.Clight.StoredAccuracy`.
-/

namespace Quadrature.Binary64.Clight
open FloatLib.Floats.Formats.BinaryInterchange
open ClightSource

/-- The (weight, node) pairs of the stored `n`-node rule: table entries `n(n-1)/2` through
`n(n-1)/2 + n - 1` of `weightBits` and `nodeBits`, decoded with `Model.ofNatBits`. -/
def storedTerms (n : Nat) : List (Value × Value) :=
  (((ClightTableData.weightBits.zip ClightTableData.nodeBits).drop (n * (n - 1) / 2)).take
    n).map fun term => (Model.ofNatBits term.1, Model.ofNatBits term.2)

-- Evaluate the slice of the 55-entry tables for each `n ≤ 10` and count it.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- For `n ≤ 10`, `storedTerms n` has exactly `n` pairs. -/
theorem stored_terms_length (n : Nat) (hn : n ≤ 10) :
    (storedTerms n).length = n := by
  interval_cases n <;> rfl

-- Read the 110 table cells of the ten rules from the initialized memory and compare them.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- For `n ≤ 10`, `initialMemory` holds the cells of `storedTerms n` in the node block 1 and the
weight block 2 at their C offsets. -/
theorem stored_table_cells (n : Nat) (hn : n ≤ 10) :
    TableCells initialMemory (CC.Positive.ofNat 1) (CC.Positive.ofNat 2)
      n 0 (storedTerms n) := by
  interval_cases n <;>
    dsimp [storedTerms, ClightTableData.weightBits, ClightTableData.nodeBits,
      List.zip, List.drop, List.take, List.map, TableCells] <;>
    (repeat' constructor)

/-- The initialized `callbackLibrary fd` satisfies `StoredLibraryContext` for `storedTerms n`,
with the tables at blocks 1 and 2 and the accessors at blocks 3 and 4. -/
def stored_context (fd : CC.FunDef) (n : Nat) (hn : n ≤ 10) :
    StoredLibraryContext (callbackLibrary fd).globalenv initialMemory (storedTerms n) where
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
  count_bound := by rw [stored_terms_length n hn]; exact hn
  cells := by rw [stored_terms_length n hn]; exact stored_table_cells n hn

/-- Given `CallbackContract fd f`, the call of `integrate` with `n ≤ 10` nodes in
`callbackLibrary fd` runs silently to `Returnstate (Vfloat (integrate f (storedTerms n)))` with
`initialMemory` unchanged. -/
theorem stored_callback_execution [CC.ExternalCalls] (fd : CC.FunDef) (f : Value → Value)
    (contract : CallbackContract fd f) (n : Nat) (hn : n ≤ 10) (k : CC.Cont) :
    CC.StarE0 (CC.Step2 (callbackLibrary fd).globalenv)
      (storedLibraryCall (.Vptr testfunBlock (CC.Integers.Ptrofs.repr 0)) n k initialMemory)
      (.Returnstate (.Vfloat (integrate f (storedTerms n))) (CC.callCont k) initialMemory) := by
  simpa only [stored_terms_length n hn] using
    stored_library_execution _ initialMemory (storedTerms n) (stored_context fd n hn) fd f
      (.Vptr testfunBlock (CC.Integers.Ptrofs.repr 0)) contract.library_contract k

/-- With deterministic external calls, every finished run of the `n`-node call in
`callbackLibrary fd` ends in the stated return state. -/
theorem stored_callback_return_state [calls : CC.ExternalCalls]
    [CC.ExternalCallsDeterministic calls]
    (fd : CC.FunDef) (f : Value → Value) (contract : CallbackContract fd f)
    (n : Nat) (hn : n ≤ 10) (value : CC.Val) (memory : CC.Mem) (trace : CC.Trace)
    (h : CC.Star (CC.Step2 (callbackLibrary fd).globalenv)
      (storedLibraryCall (.Vptr testfunBlock (CC.Integers.Ptrofs.repr 0)) n .Kstop initialMemory)
      trace (.Returnstate value .Kstop memory)) :
    CC.State.Returnstate value .Kstop memory =
      .Returnstate (.Vfloat (integrate f (storedTerms n))) .Kstop initialMemory :=
  stored_library_return_state (callbackLibrary fd) initialMemory (storedTerms n)
    (stored_context fd n hn) fd f
    (.Vptr testfunBlock (CC.Integers.Ptrofs.repr 0)) contract.library_contract
    value memory trace (by simpa only [stored_terms_length n hn] using h)

/-- In `polynomialLibrary`, the `n`-node call with the original callback runs silently to
`Returnstate (Vfloat (integrate (testfun Polynomial.cosine) (storedTerms n)))`, for `n ≤ 10`,
with no assumption on a cosine implementation. -/
theorem stored_polynomial_execution [CC.ExternalCalls]
    (n : Nat) (hn : n ≤ 10) (k : CC.Cont) :
    CC.StarE0 (CC.Step2 polynomialLibrary.globalenv)
      (storedLibraryCall (.Vptr testfunBlock (CC.Integers.Ptrofs.repr 0)) n k initialMemory)
      (.Returnstate (.Vfloat (integrate (testfun Polynomial.cosine) (storedTerms n)))
        (CC.callCont k) initialMemory) :=
  stored_callback_execution (.Internal f_testfun) (testfun Polynomial.cosine)
    polynomial_callback_contract n hn k

/-- Every value returned by the `n`-node polynomial call is
`Vfloat (integrate (testfun Polynomial.cosine) (storedTerms n))` bit for bit. -/
theorem stored_polynomial_return_eq [calls : CC.ExternalCalls]
    [CC.ExternalCallsDeterministic calls]
    (n : Nat) (hn : n ≤ 10) (value : CC.Val) (memory : CC.Mem) (trace : CC.Trace)
    (h : CC.Star (CC.Step2 polynomialLibrary.globalenv)
      (storedLibraryCall (.Vptr testfunBlock (CC.Integers.Ptrofs.repr 0)) n .Kstop initialMemory)
      trace (.Returnstate value .Kstop memory)) :
    value = .Vfloat (integrate (testfun Polynomial.cosine) (storedTerms n)) :=
  (CC.State.Returnstate.inj
    (stored_callback_return_state (.Internal f_testfun) (testfun Polynomial.cosine)
      polynomial_callback_contract n hn value memory trace h)).1

/-- For the four supported orders, `storedTerms (orderCount order)` is `Polynomial.terms order`,
the sample list of the numerical bounds in `Quadrature.Examples.PolynomialRules`. -/
theorem stored_terms_supported (order : Polynomial.Order) :
    storedTerms (orderCount order) = Polynomial.terms order := by
  cases order <;> rfl

end Quadrature.Binary64.Clight
