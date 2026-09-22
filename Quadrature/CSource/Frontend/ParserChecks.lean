import Quadrature.CSource.Frontend.Translation

/-!
# Boundary checks for the restricted C reader

Concrete examples, checked by kernel evaluation, of the reader's precedence,
associativity, comment handling, whole-input consumption, duplicate-definition
detection and rejected syntax. They are regression tests of the frontend on
inputs other than the original C program.
-/

namespace Quadrature.CSource

private def completeExpression (text : List Char) : Option Expr := do
  let tokens ← lex (text.length + 1) text
  let (value, rest) ← expression (4 * tokens.length + 16) 0 tokens
  if rest.isEmpty then some value else none

/-- `1 + 2 * 3` parses as `1 + (2 * 3)`. -/
theorem multiplication_precedence :
    completeExpression "1 + 2 * 3".toList =
      some (.binary .add (.integer 1) (.binary .mul (.integer 2) (.integer 3))) := by
  have chars : "1 + 2 * 3".toList = ['1', ' ', '+', ' ', '2', ' ', '*', ' ', '3'] := by
    decide +kernel
  rw [chars]
  rfl

/-- `a - b - c` parses as `(a - b) - c`. -/
theorem subtraction_associativity :
    completeExpression "a - b - c".toList =
      some (.binary .sub (.binary .sub (.variable "a") (.variable "b"))
        (.variable "c")) := by
  have chars : "a - b - c".toList = ['a', ' ', '-', ' ', 'b', ' ', '-', ' ', 'c'] := by
    decide +kernel
  rw [chars]
  rfl

/-- `a = b = c` parses as `a = (b = c)`. -/
theorem assignment_associativity :
    completeExpression "a = b = c".toList =
      some (.binary .assign (.variable "a")
        (.binary .assign (.variable "b") (.variable "c"))) := by
  have chars : "a = b = c".toList = ['a', ' ', '=', ' ', 'b', ' ', '=', ' ', 'c'] := by
    decide +kernel
  rw [chars]
  rfl

/-- `&f(x)` parses as the address of the call, since postfix binds tighter than prefix. -/
theorem address_precedence :
    completeExpression "&f(x)".toList =
      some (.address (.call (.variable "f") [.variable "x"])) := by
  have chars : "&f(x)".toList = ['&', 'f', '(', 'x', ')'] := by decide +kernel
  rw [chars]
  rfl

/-- A trailing comma in a call argument list is rejected. -/
theorem call_trailing_comma_rejected :
    (completeExpression "f(x,)".toList).isNone = true := by
  decide +kernel

/-- An integer literal with a leading zero (C octal) is rejected. -/
theorem octal_spelling_rejected : (completeExpression "012".toList).isNone = true := by
  decide +kernel

/-- A block comment separates the words around it, so `in/**/t` is not the keyword `int`. -/
theorem comments_separate_words :
    lex 30 "in/**/t".toList = some [.word "in", .word "t"] := by
  decide +kernel

/-- An unterminated block comment makes lexing fail. -/
theorem unterminated_comment_rejected :
    lex 30 "int /* unfinished".toList = none := by
  decide +kernel

/-- A brace inside a string literal stays in the `quoted` token and does not delimit a block. -/
theorem quoted_brace_retained :
    lex 30 "\"}\"".toList = some [.quoted "}"] := by
  decide +kernel

/-- Two definitions of the same name make `readFunction` fail. -/
theorem duplicate_definition_rejected :
    (readFunction "double f(void) { return 1.0; } double f(void) { return 2.0; }".toList
      "f").isNone = true := by
  decide +kernel

/-- A `while` loop, which the parser does not support, makes the whole function fail. -/
theorem unsupported_body_rejected :
    (readFunction "double f(void) { while (1) {} return 0.0; }".toList "f").isNone = true := by
  decide +kernel

/-- Extra tokens after a `return` expression are not skipped. -/
theorem extra_return_tokens_rejected :
    (readFunction "double f(void) { return 1.0 2.0; }".toList "f").isNone = true := by
  decide +kernel

/-- A preprocessor directive inside a function body makes the parse fail. -/
theorem body_directive_rejected :
    (readFunction "double f(void) {\n#define X 1\nreturn 0.0; }".toList "f").isNone = true := by
  decide +kernel

/-- The translator rejects a declaration inside a nested block. -/
theorem nested_declaration_rejected :
    (translateSource "double f(void) { { double x = 1.0; } return 0.0; }".toList "f").isNone =
      true := by
  decide +kernel

end Quadrature.CSource
