import CCLib.Ctypes
import Quadrature.CSource.Frontend.Lexer

/-!
# Source syntax for the one-dimensional quadrature functions

The untyped abstract syntax produced by `Quadrature.CSource.Frontend.Parser`. It keeps
calls inside expressions, subscripts, compound assignment and the three clauses
of a `for` loop as written, before any normalization to Clight statements.
Unsupported C constructs are rejected by the reader and translator rather than
represented by a default program.
-/

namespace Quadrature.CSource

/-- The C types the reader accepts: `void`, `int`, `double`, pointers, function types and arrays
of known size. -/
inductive CType where
  | void
  | int
  | double
  | pointer (target : CType)
  | function (parameters : List CType) (result : CType)
  | array (element : CType) (count : Nat)
  deriving Repr

mutual
/-- The Clight type of a `CType`. Function types get the default calling convention. -/
def CType.toClight : CType → CC.Ty
  | .void => .Tvoid
  | .int => CC.tint
  | .double => CC.tdouble
  | .pointer target => CC.tptr target.toClight
  | .function parameters result =>
      .Tfunction (CType.listToClight parameters) result.toClight CC.cc_default
  | .array element count => CC.tarray element.toClight count

/-- `CType.toClight` mapped over a parameter list, written out for the mutual recursion. -/
def CType.listToClight : List CType → List CC.Ty
  | [] => []
  | first :: rest => first.toClight :: CType.listToClight rest
end

/-- Two `CType`s are equal when their Clight images are, by CLean's total comparison `tyBeq`. -/
instance : BEq CType := ⟨fun a b ↦ CC.tyBeq a.toClight b.toClight⟩

/-- The binary operators the reader accepts: arithmetic `add sub mul div`, comparison `lt`, and
the assignments `assign` (`=`) and `addAssign` (`+=`). -/
inductive BinaryOp where
  | add | sub | mul | div | lt | assign | addAssign
  deriving DecidableEq, Repr

/-- Parsed expressions: names, integer and decimal literals, unary minus, address-of, binary
operators, calls, subscripts and postfix `++`. -/
inductive Expr where
  | variable (name : String)
  | integer (value : Nat)
  | decimal (value : CSourceTables.Decimal)
  | negate (argument : Expr)
  | address (argument : Expr)
  | binary (op : BinaryOp) (left right : Expr)
  | call (function : Expr) (arguments : List Expr)
  | subscript (array index : Expr)
  | increment (argument : Expr)
  deriving Repr

/-- Parsed statements: the empty statement, an expression statement, a local declaration with an
optional initializer, a `static const` array with its initializer list, `return`, a block, and a
three-clause `for` loop. -/
inductive Stmt where
  | skip
  | expression (value : Expr)
  | declaration (type : CType) (name : String) (initial : Option Expr)
  | staticArray (type : CType) (name : String) (initial : List Expr)
  | returnValue (value : Expr)
  | compound (statements : List Stmt)
  | forLoop (initial condition increment : Expr) (body : Stmt)
  deriving Repr

/-- A function header: name, result type and parameters, each with an optional name (prototypes
may omit names). -/
structure Signature where
  name : String
  result : CType
  parameters : List (Option String × CType)
  deriving Repr

/-- A parsed function definition: its signature and its body. -/
structure Function where
  signature : Signature
  body : Stmt
  deriving Repr

end Quadrature.CSource
