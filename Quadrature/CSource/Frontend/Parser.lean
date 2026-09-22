import Quadrature.CSource.Frontend.Syntax

/-!
# Reading the original one-dimensional C functions

A recursive-descent parser from the tokens of `Quadrature.CSource.Frontend.Lexer` to the
syntax of `Quadrature.CSource.Frontend.Syntax`. Expressions use C's precedence and
associativity for the supported operators, calls and subscripts stay source
expressions, and a function is accepted only when its whole signature and body
are consumed. A preprocessor directive inside a body or an unsupported
statement makes the parse fail rather than being skipped.
-/

namespace Quadrature.CSource

/-- A parser consumes a prefix of the token list and returns its result with the remaining
tokens, or fails. -/
abbrev Parser (α : Type _) := List Token → Option (α × List Token)

private def symbol (text : String) : List Token → Option (List Token)
  | .symbol found :: rest => if found == text then some rest else none
  | _ => none

private def name : Parser String
  | .word text :: rest =>
      if ["void", "int", "double", "return", "for", "static", "const", "extern",
          "switch", "case", "default", "if", "else"].contains text then none
      else some (text, rest)
  | _ => none

private def basicType : Parser CType
  | .word "void" :: rest => some (.void, rest)
  | .word "int" :: rest => some (.int, rest)
  | .word "double" :: rest => some (.double, rest)
  | _ => none

private def pointers (type : CType) : Parser CType
  | .symbol "*" :: rest => pointers (.pointer type) rest
  | rest => some (type, rest)

private def operator : Token → Option (BinaryOp × Nat × Bool)
  | .symbol "=" => some (.assign, 1, true)
  | .symbol "+=" => some (.addAssign, 1, true)
  | .symbol "<" => some (.lt, 5, false)
  | .symbol "+" => some (.add, 10, false)
  | .symbol "-" => some (.sub, 10, false)
  | .symbol "*" => some (.mul, 20, false)
  | .symbol "/" => some (.div, 20, false)
  | _ => none

mutual
/-- `expression fuel precedence` parses an expression whose binary operators all have rank at
least `precedence`, by precedence climbing: a `unary` operand followed by `binary`. -/
def expression : Nat → Nat → Parser Expr
  | 0, _, _ => none
  | fuel + 1, precedence, tokens => do
      let (first, rest) ← unary fuel tokens
      binary fuel precedence first rest

/-- `binary fuel precedence first` continues an expression whose left operand `first` is parsed,
absorbing operators of rank at least `precedence`. Assignments associate to the right, the other
operators to the left. -/
def binary : Nat → Nat → Expr → Parser Expr
  | 0, _, _, _ => none
  | _ + 1, _, first, [] => some (first, [])
  | fuel + 1, precedence, first, token :: rest =>
      match operator token with
      | none => some (first, token :: rest)
      | some (op, rank, rightAssociative) =>
          if rank < precedence then some (first, token :: rest)
          else do
            let (second, last) ← expression fuel
              (if rightAssociative then rank else rank + 1) rest
            binary fuel precedence (.binary op first second) last

/-- Parses a prefix operator (`-`, `&`), a parenthesized expression, a numeric literal or a name,
followed by any postfix operators. Decimal literals go through `CSourceTables.decimal`, and
integer literals with a leading zero are rejected. -/
def unary : Nat → Parser Expr
  | 0, _ => none
  | fuel + 1, .symbol "-" :: rest => do
      let (arg, last) ← unary fuel rest
      return (.negate arg, last)
  | fuel + 1, .symbol "&" :: rest => do
      let (arg, last) ← unary fuel rest
      return (.address arg, last)
  | fuel + 1, .symbol "(" :: rest => do
      let (arg, last) ← expression fuel 0 rest
      parsePostfix fuel arg (← symbol ")" last)
  | fuel + 1, .number text :: rest => do
      let value ←
        if text.toList.contains '.' then Expr.decimal <$> CSourceTables.decimal text.toList
        else if text.toList.head? == some '0' && text.length > 1 then none
        else Expr.integer <$> CSourceTables.digits text.toList
      parsePostfix fuel value rest
  | fuel + 1, tokens => do
      let (text, rest) ← name tokens
      parsePostfix fuel (.variable text) rest

/-- `parsePostfix fuel first` applies postfix operators to `first`: call arguments in
parentheses, a subscript in brackets, or `++`. -/
def parsePostfix : Nat → Expr → Parser Expr
  | 0, _, _ => none
  | fuel + 1, first, .symbol "(" :: rest => do
      let (args, last) ← arguments fuel ")" false rest
      parsePostfix fuel (.call first args) last
  | fuel + 1, first, .symbol "[" :: rest => do
      let (index, last) ← expression fuel 0 rest
      parsePostfix fuel (.subscript first index) (← symbol "]" last)
  | fuel + 1, first, .symbol "++" :: rest =>
      parsePostfix fuel (.increment first) rest
  | _ + 1, first, rest => some (first, rest)

/-- `arguments fuel close trailing` parses a comma-separated expression list up to the closing
symbol `close`. A trailing comma is accepted only when `trailing` is set, as in array
initializers. -/
def arguments : Nat → String → Bool → Parser (List Expr)
  | 0, _, _, _ => none
  | fuel + 1, close, trailing, tokens =>
      match symbol close tokens with
      | some rest => some ([], rest)
      | none => do
          let (first, rest) ← expression fuel 0 tokens
          match rest with
          | .symbol "," :: last => do
              if !trailing && (symbol close last).isSome then none else do
                let (others, last) ← arguments fuel close trailing last
                return (first :: others, last)
          | _ => return ([first], ← symbol close rest)
end

mutual
private def parameter : Nat → Parser (Option String × CType)
  | 0, _ => none
  | fuel + 1, tokens => do
      let (base, rest) ← basicType tokens
      match rest with
      | .symbol "(" :: .symbol "*" :: .word text :: .symbol ")" ::
          .symbol "(" :: last => do
          let (args, last) ← parameters fuel last
          return ((some text, .pointer (.function (args.map Prod.snd) base)), last)
      | _ => do
          let (type, last) ← pointers base rest
          match name last with
          | some (text, final) => return ((some text, type), final)
          | none => return ((none, type), last)

private def parameters : Nat → Parser (List (Option String × CType))
  | 0, _ => none
  | _ + 1, .symbol ")" :: rest => some ([], rest)
  | _ + 1, .word "void" :: .symbol ")" :: rest => some ([], rest)
  | fuel + 1, tokens => do
      let (first, rest) ← parameter fuel tokens
      match rest with
      | .symbol "," :: last => do
          if (symbol ")" last).isSome then none else do
            let (others, last) ← parameters fuel last
            return (first :: others, last)
      | _ => return ([first], ← symbol ")" rest)
end

/-- Parses a whole function header, with an optional leading `extern` and possibly unnamed
prototype parameters. Every token must be consumed. -/
def signature (tokens : List Token) : Option Signature := do
  let tokens := match tokens with | .word "extern" :: rest => rest | _ => tokens
  let (result, rest) ← basicType tokens
  let (text, rest) ← name rest
  let (params, last) ← parameters (tokens.length + 1) (← symbol "(" rest)
  if last.isEmpty then some ⟨text, result, params⟩ else none

mutual
/-- Parses one statement: `;`, a block, `return`, a `for` loop, a `static const` array
declaration, a local declaration, or an expression statement. -/
def statement : Nat → Parser Stmt
  | 0, _ => none
  | _ + 1, .symbol ";" :: rest => some (.skip, rest)
  | fuel + 1, .symbol "{" :: rest => do
      let (statements, last) ← statements fuel rest
      return (.compound statements, last)
  | fuel + 1, .word "return" :: rest => do
      let (value, last) ← expression fuel 0 rest
      return (.returnValue value, ← symbol ";" last)
  | fuel + 1, .word "for" :: rest => do
      let (initial, rest) ← expression fuel 0 (← symbol "(" rest)
      let (condition, rest) ← expression fuel 0 (← symbol ";" rest)
      let (increment, rest) ← expression fuel 0 (← symbol ";" rest)
      let (body, last) ← statement fuel (← symbol ")" rest)
      return (.forLoop initial condition increment body, last)
  | fuel + 1, .word "static" :: .word "const" :: rest => do
      let (type, rest) ← basicType rest
      let (text, rest) ← name rest
      let rest ← symbol "[" rest
      let rest ← symbol "]" rest
      let rest ← symbol "=" rest
      let (values, last) ← arguments fuel "}" true (← symbol "{" rest)
      return (.staticArray type text values, ← symbol ";" last)
  | fuel + 1, tokens =>
      match basicType tokens with
      | some (base, rest) => do
          let (type, rest) ← pointers base rest
          let (text, rest) ← name rest
          match rest with
          | .symbol "=" :: last => do
              let (value, last) ← expression fuel 0 last
              return (.declaration type text (some value), ← symbol ";" last)
          | _ => return (.declaration type text none, ← symbol ";" rest)
      | none => do
          let (value, last) ← expression fuel 0 tokens
          return (.expression value, ← symbol ";" last)

/-- Parses statements up to and including the closing `}` of a block. -/
def statements : Nat → Parser (List Stmt)
  | 0, _ => none
  | _ + 1, .symbol "}" :: rest => some ([], rest)
  | fuel + 1, tokens => do
      let (first, rest) ← statement fuel tokens
      let (others, last) ← statements fuel rest
      return (first :: others, last)
end

/-- Parses a definition from its header tokens and the tokens between its outer braces. Every
body token must be consumed. -/
def function (header contents : List Token) : Option Function := do
  let sig ← signature header
  let (body, last) ← statements (4 * contents.length + 16) (contents ++ [.symbol "}"])
  if last.isEmpty then some ⟨sig, .compound body⟩ else none

/-- The definition named `text` in the translation unit `unit`, provided every definition header
parses and exactly one definition has that name. -/
def findFunction (unit : List TopLevel) (text : String) : Option Function := do
  let foundDefinitions ← unit.filterMapM fun item =>
    match item with
    | .definition header body => do
        let sig ← signature header
        if sig.name == text then some <$> function header body else some none
    | _ => some none
  match foundDefinitions with
  | [result] => some result
  | _ => none

/-- Lexes the whole source text and returns the unique function definition named `text`. -/
def readFunction (source : List Char) (text : String) : Option Function := do
  findFunction (← readUnit source) text

end Quadrature.CSource
