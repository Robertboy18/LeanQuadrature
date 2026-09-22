import Quadrature.CSource.Cosine.Source
import Quadrature.CSource.Frontend.ClightFunctions
import Quadrature.Clight.Internal

/-!
# The Clight translation of the shipped C cosine

`translation` identifies the frontend's output for `cosine.c`.
`normalized_execution` proves that this output computes the same rounded
polynomial as the C function. In Clight the parameter is a temporary;
assigning its square therefore requires no memory allocation or store.

This is the actual frontend output, including the source parameter name,
unary minus on negative coefficients and the final multiplication by zero.
-/

namespace Quadrature.CSource.Cosine

open CC Binary64 FloatLib.Floats.Formats.BinaryInterchange Binary64.ClightSource

/-- The Clight expression of a signed source coefficient. -/
def normalizedCoefficient (coefficient : Bool × Nat) : CC.Expr :=
  let magnitude := CC.Expr.Econst_float (Model.ofNatBits coefficient.2) tdouble
  if coefficient.1 then .Eunop .Oneg magnitude tdouble else magnitude

/-- Horner's expression after the source parameter becomes a Clight temporary. -/
def normalizedHorner : List (Bool × Nat) → CC.Expr
  | [] => .Econst_float zero tdouble
  | c :: cs =>
      .Ebinop .Oadd (normalizedCoefficient c)
        (.Ebinop .Omul (.Etempvar _x tdouble) (normalizedHorner cs) tdouble) tdouble

/-- The Clight function produced by normalizing the shipped C polynomial. -/
def normalizedFunction : CC.Function where
  fn_return := tdouble
  fn_callconv := cc_default
  fn_params := [(_x, tdouble)]
  fn_vars := []
  fn_temps := []
  fn_body :=
    .Ssequence
      (.Sset _x (.Ebinop .Omul (.Etempvar _x tdouble) (.Etempvar _x tdouble) tdouble))
      (.Sreturn (some (normalizedHorner coefficients)))

-- Parse and normalize the shipped source, preserving every literal and arithmetic operation.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The frontend translates `cosine.c` to `normalizedFunction`. -/
theorem translation :
    sourceFunction source "cos" = some normalizedFunction := by
  decide +kernel

/-- Normalizing the cosine introduces no static arrays. -/
theorem normalized_no_arrays :
    CSource.sourceArrayBits source "cos" = some [] := by
  decide +kernel

/-- The normalized cosine uses only internal structured statements. -/
theorem normalized_internal : Clight.InternalStmt normalizedFunction.fn_body = true := rfl

-- Evaluate the fixed sequence of Clight control steps; binary64 arguments remain symbolic.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- The normalized cosine returns the exact FloatLib polynomial for every binary64 argument,
under any caller continuation, and leaves memory unchanged. -/
theorem normalized_execution [ExternalCalls] (ge : CGenv) (memory : Mem)
    (x : Value) (cont : CC.Cont) :
    StarE0 (Step2 ge) (.Callstate (.Internal normalizedFunction) [.Vfloat x] cont memory)
      (.Returnstate (.Vfloat (Polynomial.cosine x)) (callCont cont) memory) := by
  repeat'
    first
    | (guard_target =~ StarE0 _ (.Returnstate _ (callCont cont) _) _
       exact StarE0.refl _)
    | refine StarE0.step _ _ _ (doStep_sound _ _ _ _ (by rfl)) ?_

end Quadrature.CSource.Cosine
