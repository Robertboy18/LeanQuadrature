import Quadrature.CSource.Frontend.TypedFunctions

/-!
# Boundaries of the restricted typed elaborator

Concrete examples, checked by kernel evaluation, of the elaborator's name
resolution, value versus location contexts, exact argument and return types,
literal ranges and declaration scope. They are regression tests of the
frontend on inputs other than the original C program.
-/

namespace Quadrature.CSource.Typed

private def rejected (source : String) : Bool :=
  (typedSourceFunction source.toList "test").isNone

/-- An unbound name is rejected. -/
theorem unknown_variable_rejected :
    rejected "int test(void) { return missing; }" = true := by
  decide +kernel

/-- Assigning to a literal is rejected: only variables and subscripts are locations. -/
theorem assignment_to_value_rejected :
    rejected "int test(void) { return (1 = 2); }" = true := by
  decide +kernel

/-- Incrementing an arithmetic value is rejected. -/
theorem increment_of_value_rejected :
    rejected "int test(void) { return (1 + 2)++; }" = true := by
  decide +kernel

/-- Taking the address of a literal is rejected. -/
theorem address_of_value_rejected :
    rejected "int test(void) { return &1; }" = true := by
  decide +kernel

/-- A call with too few arguments is rejected. -/
theorem wrong_call_arity_rejected :
    rejected "extern int f(int); int test(void) { return f(); }" = true := by
  decide +kernel

/-- A `double` argument for an `int` parameter is rejected: no implicit conversion. -/
theorem wrong_call_type_rejected :
    rejected "extern int f(int); int test(void) { return f(1.0); }" = true := by
  decide +kernel

/-- Calling an `int` variable is rejected. -/
theorem nonfunction_call_rejected :
    rejected "int test(int x) { return x(1); }" = true := by
  decide +kernel

/-- Returning a `double` from an `int` function is rejected: no implicit conversion. -/
theorem wrong_return_type_rejected :
    rejected "int test(void) { return 1.0; }" = true := by
  decide +kernel

/-- An integer literal above `2^31 - 1` is rejected. -/
theorem out_of_range_integer_rejected :
    rejected "int test(void) { return 2147483648; }" = true := by
  decide +kernel

/-- Two parameters with the same name are rejected. -/
theorem duplicate_parameter_rejected :
    rejected "int test(int x, int x) { return x; }" = true := by
  decide +kernel

/-- A local with the name of a parameter is rejected. -/
theorem duplicate_local_rejected :
    rejected "int test(int x) { int x; return x; }" = true := by
  decide +kernel

/-- A declaration inside a nested block is rejected. -/
theorem nested_local_rejected :
    rejected "int test(void) { { int x; } return 0; }" = true := by
  decide +kernel

/-- A postfix increment stays an `Epostincr` on the variable location in the typed syntax. -/
theorem source_postincrement_retained :
    sourceReturnExpression "int test(int x) { return x++; }".toList "test" =
      some (.Epostincr .incr (.Evar (CC.identOfString "x") CC.tint) CC.tint) := by
  decide +kernel

/-- An assignment stays an `Eassign` on the variable location in the typed syntax. -/
theorem source_assignment_retained :
    sourceReturnExpression "int test(int x) { return (x = 1); }".toList "test" =
      some (.Eassign (.Evar (CC.identOfString "x") CC.tint)
        (.Eval (.Vint (CC.Integers.Int.repr 1)) CC.tint) CC.tint) := by
  decide +kernel

end Quadrature.CSource.Typed
