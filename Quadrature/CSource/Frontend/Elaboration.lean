import Quadrature.CSource.Frontend.Translation
import Quadrature.CSource.Semantics.Statements

/-!
# Elaborating parsed expressions and functions to typed C syntax

`elaborateFunction` maps a parsed function to the typed C syntax of
`Quadrature.CSource.Semantics.Syntax`, keeping calls, assignments, increments and `for`
loops in place. Reads of variables and subscripts become explicit `Evalof`
nodes, and every local variable stays in memory. The supported types and
operators are those of the parser. Argument, assignment and return types must
match exactly, so no implicit conversion is inserted. Static double arrays are
hoisted to named declarations as in `Quadrature.CSource.Frontend.Translation`.
-/

namespace Quadrature.CSource

/-- An elaborated expression with its source type and a proof that the C type annotation of the
expression is the Clight image of that type. -/
structure TypedExpression where
  type : CType
  value : C.Expr
  type_eq : C.typeof value = type.toClight

private def checked (condition : Bool) : Option Unit :=
  if condition then some () else none

private def numeric : CType → Bool
  | .int | .double => true
  | _ => false

private def lookup (bindings : List Binding) (name : String) : Option Binding :=
  bindings.find? (fun binding ↦ binding.name == name)

private def arithmeticOperation : BinaryOp → Option CC.Binop
  | .add => some .Oadd
  | .sub => some .Osub
  | .mul => some .Omul
  | .div => some .Odiv
  | .lt => some .Olt
  | _ => none

private def arithmeticType (left right : CType) : CType :=
  if left == .double || right == .double then .double else .int

private def callType : CType → Option (List CType × CType)
  | .function args result | .pointer (.function args result) => some (args, result)
  | _ => none

private def readLocation (read : Bool) (location : TypedExpression) : TypedExpression :=
  if read then ⟨location.type, .Evalof location.value location.type.toClight, rfl⟩
  else location

/-- The `Exprlist` of the expressions of elaborated arguments. -/
def typedArguments : List TypedExpression → C.Exprlist
  | [] => .Enil
  | first :: rest => .Econs first.value (typedArguments rest)

/-- Elaborates an expression in value context (`read = true`) or location context
(`read = false`) against the bindings in scope. Only variables and subscripts are accepted as
locations. Literals, operators, calls and increments are checked in value context. -/
def elaborateExpression : Nat → List Binding → Bool → Expr → Option TypedExpression
  | 0, _, _, _ => none
  | _ + 1, bindings, read, .variable text => do
      let binding ← lookup bindings text
      return readLocation read
        ⟨binding.type, .Evar (CC.identOfString text) binding.type.toClight, rfl⟩
  | fuel + 1, bindings, read, .subscript array index => do
      let base ← elaborateExpression fuel bindings true array
      let offset ← elaborateExpression fuel bindings true index
      checked (offset.type == .int)
      let element ←
        match base.type with
        | .array type _ | .pointer type => some type
        | _ => none
      checked (numeric element)
      let address := C.Expr.Ebinop .Oadd base.value offset.value (CC.tptr element.toClight)
      return readLocation read ⟨element, .Ederef address element.toClight, rfl⟩
  | _, _, false, _ => none
  | _ + 1, _, true, .integer n => do
      checked (n ≤ 2147483647)
      return ⟨.int, .Eval (.Vint (CC.Integers.Int.repr n)) CC.tint, rfl⟩
  | _ + 1, _, true, .decimal d =>
      some ⟨.double, .Eval (.Vfloat d.round) CC.tdouble, rfl⟩
  | fuel + 1, bindings, true, .negate arg => do
      let value ← elaborateExpression fuel bindings true arg
      checked (numeric value.type)
      return ⟨value.type, .Eunop .Oneg value.value value.type.toClight, rfl⟩
  | fuel + 1, bindings, true, .address arg => do
      let location ← elaborateExpression fuel bindings false arg
      return ⟨.pointer location.type,
        .Eaddrof location.value (CC.tptr location.type.toClight), rfl⟩
  | fuel + 1, bindings, true, .binary .assign left right => do
      let location ← elaborateExpression fuel bindings false left
      let value ← elaborateExpression fuel bindings true right
      checked (numeric location.type && location.type == value.type)
      return ⟨location.type, .Eassign location.value value.value location.type.toClight, rfl⟩
  | fuel + 1, bindings, true, .binary .addAssign left right => do
      let location ← elaborateExpression fuel bindings false left
      let value ← elaborateExpression fuel bindings true right
      checked (numeric location.type && location.type == value.type)
      return ⟨location.type, .Eassignop .Oadd location.value value.value
        location.type.toClight location.type.toClight, rfl⟩
  | fuel + 1, bindings, true, .binary op left right => do
      let operation ← arithmeticOperation op
      let a ← elaborateExpression fuel bindings true left
      let b ← elaborateExpression fuel bindings true right
      checked (numeric a.type && numeric b.type)
      let type := if op == .lt then .int else arithmeticType a.type b.type
      return ⟨type, .Ebinop operation a.value b.value type.toClight, rfl⟩
  | fuel + 1, bindings, true, .call fn args => do
      let callee ← elaborateExpression fuel bindings true fn
      let (params, result) ← callType callee.type
      checked (!(result == .void))
      let arguments ← args.mapM (elaborateExpression fuel bindings true)
      checked (arguments.map (·.type) == params)
      return ⟨result, .Ecall callee.value (typedArguments arguments) result.toClight, rfl⟩
  | fuel + 1, bindings, true, .increment arg => do
      let location ← elaborateExpression fuel bindings false arg
      checked (location.type == .int)
      return ⟨location.type, .Epostincr .incr location.value location.type.toClight, rfl⟩

/-- Elaborator state: the bindings in scope, the local variables declared so far with their
Clight types, the hoisted static arrays with their binary64 contents, and the function's result
type. -/
structure ElaborationState where
  bindings : List Binding
  locals : List (CC.Ident × CC.Ty) := []
  arrays : List (String × List CC.Floats.Float) := []
  resultType : CType

/-- The elaboration monad: `ElaborationState` over `Option`, failing on unsupported input. -/
abbrev Elaborate (α : Type _) := StateT ElaborationState Option α

private def require (condition : Bool) : Elaborate Unit :=
  fun state ↦ (checked condition).map fun _ ↦ ((), state)

private def expressionInState (source : Expr) : Elaborate TypedExpression :=
  fun state ↦ (elaborateExpression 1024 state.bindings true source).map (·, state)

private def declare (text : String) (type : CType) (isLocal : Bool) : Elaborate Unit := do
  let state ← get
  let id := CC.identOfString text
  require (!state.bindings.any
    (fun binding ↦ binding.name == text || CC.identOfString binding.name == id))
  set { state with
    bindings := ⟨text, type, isLocal⟩ :: state.bindings
    locals := if isLocal then state.locals ++ [(id, type.toClight)] else state.locals }

private def sequence : List C.Stmt → C.Stmt
  | [] => .Sskip
  | [last] => last
  | first :: rest => .Ssequence first (sequence rest)

private def decimalInitializer : Expr → Option CSourceTables.Decimal
  | .decimal d => some d
  | .negate (.decimal d) => some { d with negative := !d.negative }
  | _ => none

/-- Elaborates a statement, keeping the source control flow. The `Bool` says whether declarations
are allowed here (only at the top level of the body). A declaration without initializer or a
static array emits no statement and gives `none`. -/
def elaborateStatement : Nat → Bool → Stmt → Elaborate (Option C.Stmt)
  | 0, _, _ => fun _ ↦ none
  | _ + 1, _, .skip => pure (some .Sskip)
  | _ + 1, _, .expression value => do
      return some (.Sdo (← expressionInState value).value)
  | _ + 1, true, .declaration type text initial => do
      require (numeric type)
      declare text type true
      match initial with
      | none => pure none
      | some value => do
          let rhs ← expressionInState value
          require (rhs.type == type)
          return some (.Sdo (.Eassign (.Evar (CC.identOfString text) type.toClight)
            rhs.value type.toClight))
  | _ + 1, true, .staticArray type text initial => do
      require (type == .double)
      let some decimals := initial.mapM decimalInitializer | fun _ ↦ none
      require (!decimals.isEmpty)
      declare text (.array .double decimals.length) false
      modify fun state ↦ { state with arrays := state.arrays ++ [(text, decimals.map (·.round))] }
      return none
  | _ + 1, _, .returnValue value => do
      let result ← expressionInState value
      require (result.type == (← get).resultType)
      return some (.Sreturn (some result.value))
  | fuel + 1, top, .compound statements => do
      let translated ← statements.mapM fun statement =>
        match statement with
        | .compound _ => elaborateStatement fuel false statement
        | _ => elaborateStatement fuel top statement
      return some (sequence (translated.filterMap id))
  | fuel + 1, _, .forLoop initial condition increment body => do
      let first ← expressionInState initial
      let test ← expressionInState condition
      require (test.type == .int)
      let last ← expressionInState increment
      let some inside ← elaborateStatement fuel false body | fun _ ↦ none
      return some (.Sfor (.Sdo first.value) test.value (.Sdo last.value) inside)
  | _, _, _ => fun _ ↦ none

/-- An elaborated function together with the static arrays hoisted out of its body. -/
structure FunctionElaboration where
  code : C.Function
  arrays : List (String × List CC.Floats.Float)

/-- Elaborates `source` given the global bindings: parameters and locals become memory variables
(`fn_params` and `fn_vars`), names and their identifiers must be distinct, and the body keeps its
source control flow. -/
def elaborateFunction (globals : List Binding) (source : Function) :
    Option FunctionElaboration := do
  let parameters ← source.signature.parameters.mapM fun (name, type) => do
    let text ← name
    if type == .void then none else some (text, type)
  let bindings := parameters.map fun (name, type) ↦ Binding.mk name type true
  let names := (bindings ++ globals).map (·.name)
  checked (names.length == names.eraseDups.length)
  let ids := names.map CC.identOfString
  checked (ids.length == ids.eraseDups.length)
  let initial : ElaborationState :=
    { bindings := bindings ++ globals, resultType := source.signature.result }
  let (some body, state) ← elaborateStatement 1024 true source.body initial | none
  return ⟨{
    fn_return := source.signature.result.toClight
    fn_callconv := CC.cc_default
    fn_params := parameters.map fun (name, type) ↦ (CC.identOfString name, type.toClight)
    fn_vars := state.locals
    fn_body := body }, state.arrays⟩

/-- Reads the whole source text and elaborates the unique definition named `text`. -/
def elaborateSource (source : List Char) (text : String) : Option FunctionElaboration := do
  let unit ← readUnit source
  elaborateFunction (← globalBindings unit) (← findFunction unit text)

/-- The typed C function obtained by parsing and elaborating the definition named `text` in
`source`. -/
def typedSourceFunction (source : List Char) (text : String) : Option C.Function :=
  (elaborateSource source text).map (·.code)

end Quadrature.CSource
