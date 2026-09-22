import Quadrature.CSource.Frontend.Parser
import Quadrature.Clight.Source

/-!
# Normalizing the supported source syntax to Clight

`translateFunction` maps a parsed function to a CLean Clight `CC.Function`. It
resolves names and types, hoists `static const` tables into a separate list,
extracts calls and array loads into fresh temporaries, and expands `for`, `++`
and `+=` into Clight statements. Calls are extracted left to right, as
clightgen does. `Quadrature.CSource.Frontend.ClightFunctions` checks the output against
clightgen's for the five functions of the original C program.
-/

namespace Quadrature.CSource

/-- A name in scope with its type. The flag `temporary` marks names held in Clight temporaries
rather than in memory. -/
structure Binding where
  name : String
  type : CType
  temporary : Bool

/-- Translator state. It holds the bindings in scope, the declared locals (`declarations`) and
generated temporaries (`temporaries`) with their Clight types, and the hoisted static arrays with
their binary64 contents. It also holds the next fresh temporary number (from 128, as clightgen)
and the function's result type. -/
structure TranslationState where
  bindings : List Binding
  declarations : List (CC.Ident × CC.Ty) := []
  temporaries : List (CC.Ident × CC.Ty) := []
  arrays : List (String × List CC.Floats.Float) := []
  nextTemporary : Nat := 128
  resultType : CType

/-- The translation monad: `TranslationState` over `Option`, failing on unsupported input. -/
abbrev Translate (α : Type _) := StateT TranslationState Option α

private def reject {α : Type _} : Translate α := fun _ ↦ none

private def require (condition : Bool) : Translate Unit :=
  if condition then pure () else reject

private def lookup (name : String) : Translate Binding := do
  match (← get).bindings.find? (fun b ↦ b.name == name) with
  | some binding => pure binding
  | none => reject

private def fresh (type : CType) : Translate CC.Ident := do
  let state ← get
  let id := CC.Positive.ofNat state.nextTemporary
  require (!state.bindings.any (fun b ↦ CC.identOfString b.name == id))
  set { state with
    nextTemporary := state.nextTemporary + 1
    temporaries := (id, type.toClight) :: state.temporaries }
  return id

/-- The Clight image of a source expression: the statements `before` that perform its calls and
loads, the side-effect-free `value` expression, and the source type. -/
structure ExpressionTranslation where
  before : List CC.Stmt
  value : CC.Expr
  type : CType

private def numeric : CType → Bool
  | .int | .double => true
  | _ => false

private def operation : BinaryOp → Option CC.Binop
  | .add => some .Oadd
  | .sub => some .Osub
  | .mul => some .Omul
  | .div => some .Odiv
  | .lt => some .Olt
  | _ => none

private def arithmeticType (left right : CType) : CType :=
  if left == .double || right == .double then .double else .int

private def callType : CType → Option (List CType × CType)
  | .function params result | .pointer (.function params result) => some (params, result)
  | _ => none

/-- Translates an expression, moving calls and subscript loads into `before` in evaluation order
while keeping the arithmetic grouping and argument order of the source. -/
def translateExpression : Nat → Expr → Translate ExpressionTranslation
  | 0, _ => reject
  | _ + 1, .variable text => do
      let binding ← lookup text
      let value :=
        if binding.temporary then CC.Expr.Etempvar (CC.identOfString text) binding.type.toClight
        else CC.Expr.Evar (CC.identOfString text) binding.type.toClight
      return ⟨[], value, binding.type⟩
  | _ + 1, .integer n => do
      require (n ≤ 2147483647)
      return ⟨[], .Econst_int (CC.Integers.Int.repr n) CC.tint, .int⟩
  | _ + 1, .decimal d =>
      pure ⟨[], .Econst_float d.round CC.tdouble, .double⟩
  | fuel + 1, .negate arg => do
      let value ← translateExpression fuel arg
      require (numeric value.type)
      return ⟨value.before, .Eunop .Oneg value.value value.type.toClight, value.type⟩
  | _ + 1, .address (.variable text) => do
      let binding ← lookup text
      require (!binding.temporary)
      let type := CType.pointer binding.type
      return ⟨[], .Eaddrof (.Evar (CC.identOfString text) binding.type.toClight) type.toClight,
        type⟩
  | fuel + 1, .binary op left right => do
      let some binop := operation op | reject
      let a ← translateExpression fuel left
      let b ← translateExpression fuel right
      require (numeric a.type && numeric b.type)
      let type := if op == .lt then .int else arithmeticType a.type b.type
      return ⟨a.before ++ b.before, .Ebinop binop a.value b.value type.toClight, type⟩
  | fuel + 1, .call fn args => do
      let callee ← translateExpression fuel fn
      let some (params, result) := callType callee.type | reject
      require (!(result == .void))
      let arguments ← args.mapM (translateExpression fuel)
      require (arguments.map (·.type) == params)
      let id ← fresh result
      return ⟨callee.before ++ arguments.flatMap (·.before) ++
        [.Scall (some id) callee.value (arguments.map (·.value))],
        .Etempvar id result.toClight, result⟩
  | fuel + 1, .subscript array index => do
      let base ← translateExpression fuel array
      let offset ← translateExpression fuel index
      require (offset.type == .int)
      let element ←
        match base.type with
        | .array type _ | .pointer type => pure type
        | _ => reject
      require (numeric element)
      let id ← fresh element
      let address := CC.Expr.Ebinop .Oadd base.value offset.value
        (CC.tptr element.toClight)
      return ⟨base.before ++ offset.before ++ [.Sset id (.Ederef address element.toClight)],
        .Etempvar id element.toClight, element⟩
  | _, _ => reject

/-- Sequences the extracted `effects` in order before `last`, nested to the left as clightgen
nests them. -/
def sequenceEffects (effects : List CC.Stmt) (last : CC.Stmt) : CC.Stmt :=
  match effects with
  | [] => last
  | first :: rest => .Ssequence (rest.foldl CC.Stmt.Ssequence first) last

private def translateUpdate (fuel : Nat) : Expr → Translate CC.Stmt
  | .binary .assign (.variable text) value => do
      let binding ← lookup text
      require binding.temporary
      let rhs ← translateExpression fuel value
      require (rhs.type == binding.type)
      return sequenceEffects rhs.before (.Sset (CC.identOfString text) rhs.value)
  | .binary .addAssign (.variable text) value => do
      let binding ← lookup text
      require (binding.temporary && numeric binding.type)
      let rhs ← translateExpression fuel value
      require (rhs.type == binding.type)
      let id := CC.identOfString text
      return sequenceEffects rhs.before
        (.Sset id (.Ebinop .Oadd (.Etempvar id binding.type.toClight)
          rhs.value binding.type.toClight))
  | .increment (.variable text) => do
      let binding ← lookup text
      require (binding.temporary && binding.type == .int)
      let id := CC.identOfString text
      return .Sset id (.Ebinop .Oadd (.Etempvar id CC.tint)
        (.Econst_int (CC.Integers.Int.repr 1) CC.tint) CC.tint)
  | _ => reject

private def decimalInitializer : Expr → Option CSourceTables.Decimal
  | .decimal d => some d
  | .negate (.decimal d) => some { d with negative := !d.negative }
  | _ => none

private def declare (name : String) (type : CType) (temporary : Bool) : Translate Unit := do
  let state ← get
  let id := CC.identOfString name
  require (!state.bindings.any (fun b ↦ b.name == name))
  require (!state.declarations.any (fun b ↦ b.1 == id))
  require (!state.temporaries.any (fun b ↦ b.1 == id))
  set { state with
    bindings := ⟨name, type, temporary⟩ :: state.bindings
    declarations := if temporary then state.declarations ++ [(id, type.toClight)]
      else state.declarations }

private def sequenceStatements : List CC.Stmt → CC.Stmt
  | [] => .Sskip
  | [last] => last
  | first :: rest => .Ssequence first (sequenceStatements rest)

/-- Translates a statement. The `Bool` says whether declarations are allowed here (only at the
top level of the body, so the accepted functions have one declaration scope). A declaration or
static array without a statement to emit gives `none`. -/
def translateStatement : Nat → Bool → Stmt → Translate (Option CC.Stmt)
  | 0, _, _ => reject
  | _ + 1, _, .skip => pure (some .Sskip)
  | fuel + 1, _, .expression value => some <$> translateUpdate fuel value
  | fuel + 1, true, .declaration type text initial => do
      require (numeric type)
      declare text type true
      match initial with
      | none => pure none
      | some value => do
          let rhs ← translateExpression fuel value
          require (rhs.type == type)
          return some (sequenceEffects rhs.before (.Sset (CC.identOfString text) rhs.value))
  | _ + 1, true, .staticArray type text initial => do
      require (type == .double)
      let some decimals := initial.mapM decimalInitializer | reject
      require (!decimals.isEmpty)
      declare text (.array .double decimals.length) false
      modify fun state ↦ { state with arrays := state.arrays ++ [(text, decimals.map (·.round))] }
      return none
  | fuel + 1, _, .returnValue value => do
      let result ← translateExpression fuel value
      require (result.type == (← get).resultType)
      return some (sequenceEffects result.before (.Sreturn (some result.value)))
  | fuel + 1, top, .compound statements => do
      let translated ← statements.mapM fun statement =>
        match statement with
        | .compound _ => translateStatement fuel false statement
        | _ => translateStatement fuel top statement
      return some (sequenceStatements (translated.filterMap id))
  | fuel + 1, _, .forLoop initial condition increment body => do
      let first ← translateUpdate fuel initial
      let test ← translateExpression fuel condition
      require (test.before.isEmpty && test.type == .int)
      let last ← translateUpdate fuel increment
      let some inside ← translateStatement fuel false body | reject
      return some (.Ssequence first (.Sloop
        (.Ssequence (.Sifthenelse test.value .Sskip .Sbreak) inside) last))
  | _, _, _ => reject

/-- A translated function together with the static arrays hoisted out of its body. -/
structure FunctionTranslation where
  code : CC.Function
  arrays : List (String × List CC.Floats.Float)

/-- The global bindings of a translation unit: one function-typed binding per top-level
declaration or definition, including `extern double cos(double)`. -/
def globalBindings (unit : List TopLevel) : Option (List Binding) := do
  unit.filterMapM fun item =>
    match item with
    | .directive _ => some none
    | .declaration header | .definition header _ => do
        let sig ← signature header
        return some ⟨sig.name, .function (sig.parameters.map (·.2)) sig.result, false⟩

/-- Translates `source` given the global bindings: parameters become Clight temporaries, names
must be distinct, and the body is translated from a fresh state. The result lists the declared
locals before the generated temporaries in `fn_temps`. -/
def translateFunction (globals : List Binding) (source : Function) :
    Option FunctionTranslation := do
  let parameters ← source.signature.parameters.mapM fun (name, type) => do
    let text ← name
    if type == .void then none else some (text, type)
  let bindings := parameters.map fun (name, type) ↦ Binding.mk name type true
  let names := (bindings ++ globals).map (·.name)
  if !(parameters.map (·.1)).Nodup then none else do
    if names.length != names.eraseDups.length then none else do
      let initial : TranslationState :=
        { bindings := bindings ++ globals, resultType := source.signature.result }
      let (some body, state) ← translateStatement 1024 true source.body initial | none
      return ⟨{
        fn_return := source.signature.result.toClight
        fn_callconv := CC.cc_default
        fn_params := parameters.map fun (name, type) ↦ (CC.identOfString name, type.toClight)
        fn_vars := []
        fn_temps := state.declarations ++ state.temporaries
        fn_body := body }, state.arrays⟩

/-- Reads the whole source text and translates the unique definition named `text`. -/
def translateSource (source : List Char) (text : String) : Option FunctionTranslation := do
  let unit ← readUnit source
  translateFunction (← globalBindings unit) (← findFunction unit text)

/-- The Clight function obtained by parsing and translating the definition named `text` in
`source`. -/
def sourceFunction (source : List Char) (text : String) : Option CC.Function :=
  (translateSource source text).map (·.code)

end Quadrature.CSource
