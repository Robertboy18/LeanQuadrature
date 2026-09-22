import Quadrature.CSource.Frontend.TypedFunctions
import Quadrature.CSource.Integrator.State
import Quadrature.Examples.PolynomialRules

/-!
# C source of the polynomial cosine

`source` contains the adjacent `cosine.c`, whose `cos` definition replaces the
external function in the quadrature application. `elaboration` checks the
complete body against `function`; `coefficient_values` identifies its rounded
decimal coefficients with `Binary64.Polynomial.coefficients`.

The routine squares its parameter in place and evaluates a degree-seven
polynomial in that square. Its approximation bounds concern the quadrature
example on `[-1, 1]`; it is not a general implementation of the library cosine.
-/

namespace Quadrature.CSource.Cosine

open CC Binary64 FloatLib.Floats.Formats.BinaryInterchange
open Binary64.ClightSource

/-- The exact text of the C replacement, included from the file shipped with the proofs. -/
def source : List Char := (include_str "cosine.c").toList

/-- Signs and magnitude encodings of the eight decimal coefficients in `cosine.c`. -/
def coefficients : List (Bool × Nat) :=
  [(false, 4607182418800017408), (true, 4602678819172646912),
   (false, 4586165620538955093), (true, 4564047942368979991),
   (false, 4537941361671905306), (true, 4508805057796939612),
   (false, 4477122120089393304), (true, 4443145680587881629)]

/-- The value of a signed C floating literal. Unary minus changes its sign after rounding. -/
def coefficientValue (coefficient : Bool × Nat) : Floats.Float :=
  let magnitude := Model.ofNatBits coefficient.2
  if coefficient.1 then Model.neg magnitude else magnitude

/-- The syntax of a signed C literal, retaining unary minus for negative coefficients. -/
def coefficientExpression (coefficient : Bool × Nat) : C.Expr :=
  let magnitude := C.Expr.Eval (.Vfloat (Model.ofNatBits coefficient.2)) tdouble
  if coefficient.1 then .Eunop .Oneg magnitude tdouble else magnitude

/-- These signed literals denote exactly the coefficients used by the numerical proofs. -/
theorem coefficient_values :
    coefficients.map coefficientValue = Polynomial.coefficients := by
  decide +kernel

/-- Horner evaluation using the squared argument stored in the parameter `x`. -/
def hornerExpression : List (Bool × Nat) → C.Expr
  | [] => .Eval (.Vfloat zero) tdouble
  | c :: cs =>
      .Ebinop .Oadd (coefficientExpression c)
        (.Ebinop .Omul (C.readVar _x tdouble) (hornerExpression cs) tdouble) tdouble

/-- The assignment that replaces the parameter by its rounded square. -/
def squareAssignment : C.Expr :=
  .Eassign (.Evar _x tdouble)
    (.Ebinop .Omul (C.readVar _x tdouble) (C.readVar _x tdouble) tdouble) tdouble

/-- The complete typed C function: square `x`, then return its Horner polynomial. -/
def function : C.Function where
  fn_return := tdouble
  fn_callconv := cc_default
  fn_params := [(_x, tdouble)]
  fn_vars := []
  fn_body := .Ssequence (.Sdo squareAssignment)
    (.Sreturn (some (hornerExpression coefficients)))

-- Parse the included C file and check its types, literals, assignment and return expression.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- Parsing and elaborating the shipped C routine produces exactly `function`. -/
theorem elaboration :
    typedSourceFunction source "cos" = some function := by
  decide +kernel

/-- The replacement introduces no static arrays. -/
theorem no_arrays :
    Typed.sourceArrayBits source "cos" = some [] := by
  decide +kernel

end Quadrature.CSource.Cosine
