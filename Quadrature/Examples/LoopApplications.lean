import Quadrature.Binary64.LoopMachine
import Quadrature.Clight.TableData
import Quadrature.Examples.PolynomialRules

/-!
# Loop-machine applications using the imported table encodings

`tableMemory` holds all 55 entries of each Clight table initializer, nodes in
block 0 and weights in block 1, so the memory holds all ten rules. The loop
machine is run for orders one through four with the polynomial cosine callback
of `PolynomialRules`, and Lean checks that the loads at those orders match the
hand-written stored rules, including the three-point C weight. Every terminating
run returns `Polynomial.result order` and satisfies its integral error bound.
-/

namespace Quadrature.Binary64.LoopMachine

open FloatLib.Floats.Formats.BinaryInterchange

/-- The memory of the two Clight table initializers: block 0 holds the 55 node bit patterns and
block 1 the 55 weight bit patterns, at 8-byte offsets from 0. Other blocks and negative offsets
are unmapped. -/
def tableMemory : Memory := fun address =>
  if 0 ≤ address.offset then
    let table := match address.block with
      | 0 => ClightTableData.nodeBits
      | 1 => ClightTableData.weightBits
      | _ => []
    (table[address.offset.toNat / 8]?).map Model.ofNatBits
  else none

/-- The number of samples of each order. -/
def count : Polynomial.Order → Nat
  | .one => 1
  | .two => 2
  | .three => 3
  | .four => 4

/-- The loop context for an order: count `n`, weights in block 1 and nodes in block 0, both at
byte offset `8·n(n−1)/2`, and the given callback. -/
def context (order : Polynomial.Order)
    (callback : Memory → Value → Option (Memory × Value)) : Context :=
  let n := count order
  let offset : Int := 8 * (n * (n - 1) / 2)
  ⟨n, ⟨1, offset⟩, ⟨0, offset⟩, callback⟩

/-- The stored rule of each order has `count order` terms. -/
theorem terms_length (order : Polynomial.Order) :
    (Polynomial.terms order).length = count order := by
  cases order <;> decide

/-- At each of the four orders, the loads from `tableMemory` yield exactly
`Polynomial.terms order`, by evaluation. -/
theorem imported_tables (order : Polynomial.Order)
    (callback : Memory → Value → Option (Memory × Value)) :
    Tables tableMemory (context order callback) 0 (Polynomial.terms order) := by
  cases order <;>
    simp only [Polynomial.terms, StoredRule.terms, oneStored, twoStored, threeStored,
      fourStored, List.ofFn_succ, List.ofFn_zero, Tables, context, count] <;> decide

/-- For any callback that returns `f` at the order's nodes without changing memory, the machine
run of `6·count + 1` steps returns `integrate f (Polynomial.terms order)`. The memory holds all
ten rules, and the machine is run for the four orders. -/
theorem table_application (order : Polynomial.Order)
    (callback : Memory → Value → Option (Memory × Value)) (f : Value → Value)
    (hcallback : ∀ term ∈ Polynomial.terms order,
      callback tableMemory term.2 = some (tableMemory, f term.2)) :
    run (context order callback) (6 * count order + 1) (tableMemory, .test 0 zero) =
      some (tableMemory, .returned (integrate f (Polynomial.terms order))) := by
  rw [← terms_length]
  apply run_integrate
  · simp [context, terms_length]
  · cases order <;> norm_num [context, count]
  · exact imported_tables order callback
  · exact hcallback

/-- The callback that leaves memory unchanged and returns `testfun Polynomial.cosine x`. -/
def polynomialCallback (memory : Memory) (x : Value) : Option (Memory × Value) :=
  some (memory, testfun Polynomial.cosine x)

/-- With the polynomial callback, the machine returns `Polynomial.result order` after
`6·count + 1` steps. -/
theorem polynomial_application (order : Polynomial.Order) :
    run (context order polynomialCallback) (6 * count order + 1)
      (tableMemory, .test 0 zero) =
        some (tableMemory, .returned (Polynomial.result order)) := by
  exact table_application order polynomialCallback (testfun Polynomial.cosine)
    (fun _ _ ↦ rfl)

/-- Every terminating run of the machine with the polynomial callback, whatever its fuel, leaves
`tableMemory` unchanged and returns `Polynomial.result order`. -/
theorem polynomial_return (order : Polynomial.Order) (fuel : Nat)
    (memory : Memory) (value : Value)
    (hreturn : run (context order polynomialCallback) fuel (tableMemory, .test 0 zero) =
      some (memory, .returned value)) :
    memory = tableMemory ∧ value = Polynomial.result order := by
  apply returned_eq_integrate (context order polynomialCallback) tableMemory
    (testfun Polynomial.cosine) (Polynomial.terms order)
  · simp [context, terms_length]
  · cases order <;> norm_num [context, count]
  · exact imported_tables order polynomialCallback
  · intro term _
    rfl
  · exact hreturn

/-- Every value returned by the machine with the polynomial callback is finite and within
`Polynomial.errorBound order` of the integral of the integrand over `[-1, 1]`. -/
theorem polynomial_integral_accuracy (order : Polynomial.Order) (fuel : Nat)
    (memory : Memory) (value : Value)
    (hreturn : run (context order polynomialCallback) fuel (tableMemory, .test 0 zero) =
      some (memory, .returned value)) :
    Model.isFinite value = true ∧
    |Model.toReal value - ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤
      Polynomial.errorBound order := by
  rw [(polynomial_return order fuel memory value hreturn).2]
  exact Polynomial.integral_accuracy order

end Quadrature.Binary64.LoopMachine
