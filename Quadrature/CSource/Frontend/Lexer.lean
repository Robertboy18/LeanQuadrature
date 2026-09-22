import Quadrature.CSource.Tables.Literals

/-!
# Tokens and top-level blocks in the original C file

`lex` turns the ASCII text of the original C program into tokens, keeping
identifiers, number spellings, quoted strings and preprocessor lines distinct,
so that a comment can neither introduce a declaration nor split a token
unnoticed. `topLevels` then cuts the token list into directives, declarations
and function definitions, delimiting bodies by balanced braces after quoted
strings have been separated from punctuation. Preprocessor lines are kept as
tokens and not executed.
-/

namespace Quadrature.CSource

/-- Lexical tokens: identifiers and keywords (`word`), number spellings, punctuation and
operators (`symbol`), string literals (`quoted`), and whole preprocessor lines (`directive`). -/
inductive Token where
  | word (text : String)
  | number (text : String)
  | symbol (text : String)
  | quoted (text : String)
  | directive (text : String)
  deriving DecidableEq, Repr

private def identifierStart (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'

private def digit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

private def identifierContinue (c : Char) : Bool := identifierStart c || digit c

private def span (p : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: rest =>
      if p c then
        let (first, last) := span p rest
        (c :: first, last)
      else ([], c :: rest)

private def afterBlockComment : List Char → Option (List Char)
  | [] => none
  | '*' :: '/' :: rest => some rest
  | _ :: rest => afterBlockComment rest

private def quoted : List Char → Option (List Char × List Char)
  | [] => none
  | '"' :: rest => some ([], rest)
  | '\\' :: c :: rest => do
      let (body, last) ← quoted rest
      return ('\\' :: c :: body, last)
  | c :: rest =>
      if c == '\n' || c == '\r' then none
      else do
        let (body, last) ← quoted rest
        return (c :: body, last)

private def doubleSymbol (a b : Char) : Bool :=
  (a == '+' && (b == '+' || b == '=')) ||
  (a == '-' && (b == '-' || b == '=' || b == '>')) ||
  ((a == '<' || a == '>' || a == '=' || a == '!' ||
    a == '*' || a == '/' || a == '%') && b == '=') ||
  (a == '&' && b == '&') || (a == '|' && b == '|')

private def singleSymbol (c : Char) : Bool :=
  "(){}[],;:+-*/%<>=!&|".toList.contains c

/-- `lex fuel chars` tokenizes `chars`, skipping whitespace and both comment forms. It fails on an
unsupported character, an unterminated comment or string, or exhausted fuel. -/
def lex : Nat → List Char → Option (List Token)
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, '/' :: '*' :: rest => do
      let last ← afterBlockComment rest
      lex fuel last
  | fuel + 1, '/' :: '/' :: rest =>
      lex fuel (span (· != '\n') rest).2
  | fuel + 1, '"' :: rest => do
      let (body, last) ← quoted rest
      (Token.quoted (String.ofList body) :: ·) <$> lex fuel last
  | fuel + 1, '#' :: rest =>
      let (body, last) := span (· != '\n') rest
      (Token.directive (String.ofList body) :: ·) <$> lex fuel last
  | fuel + 1, c :: rest =>
      if CSourceTables.isSpace c then lex fuel rest
      else if identifierStart c then
        let (body, last) := span identifierContinue rest
        (Token.word (String.ofList (c :: body)) :: ·) <$> lex fuel last
      else if digit c then
        let (body, last) := span (fun d ↦ digit d || d == '.') rest
        (Token.number (String.ofList (c :: body)) :: ·) <$> lex fuel last
      else
        match rest with
        | d :: last =>
            if doubleSymbol c d then
              (Token.symbol (String.ofList [c, d]) :: ·) <$> lex fuel last
            else if singleSymbol c then
              (Token.symbol (String.singleton c) :: ·) <$> lex fuel rest
            else none
        | [] =>
            if singleSymbol c then some [.symbol (String.singleton c)] else none

/-- A top-level item: a preprocessor directive, a declaration (the header tokens before `;`), or
a definition (the header tokens and the tokens between its outermost braces). -/
inductive TopLevel where
  | directive (text : String)
  | declaration (header : List Token)
  | definition (header body : List Token)
  deriving DecidableEq, Repr

private def header : List Token → Option (List Token × Bool × List Token)
  | [] => none
  | .symbol ";" :: rest => some ([], false, rest)
  | .symbol "{" :: rest => some ([], true, rest)
  | .symbol "}" :: _ | .directive _ :: _ => none
  | token :: rest => do
      let (first, isBody, last) ← header rest
      return (token :: first, isBody, last)

/-- Reads through the matching closing brace. Nested blocks remain in the body. -/
private def body : Nat → List Token → Option (List Token × List Token)
  | _, [] => none
  | 0, .symbol "}" :: rest => some ([], rest)
  | depth + 1, .symbol "}" :: rest => do
      let (first, last) ← body depth rest
      return (.symbol "}" :: first, last)
  | depth, .symbol "{" :: rest => do
      let (first, last) ← body (depth + 1) rest
      return (.symbol "{" :: first, last)
  | depth, token :: rest => do
      let (first, last) ← body depth rest
      return (token :: first, last)

/-- `topLevels fuel tokens` splits a token list into top-level items, reading each definition body
through its matching closing brace. -/
def topLevels : Nat → List Token → Option (List TopLevel)
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, .directive text :: rest =>
      (TopLevel.directive text :: ·) <$> topLevels fuel rest
  | fuel + 1, tokens => do
      let (first, isBody, rest) ← header tokens
      if isBody then
        let (contents, last) ← body 0 rest
        (TopLevel.definition first contents :: ·) <$> topLevels fuel last
      else (TopLevel.declaration first :: ·) <$> topLevels fuel rest

/-- Lexes and splits the whole source text. Any lexical or delimiter failure gives `none`. -/
def readUnit (source : List Char) : Option (List TopLevel) := do
  let tokens ← lex (source.length + 1) source
  topLevels (tokens.length + 1) tokens

end Quadrature.CSource
