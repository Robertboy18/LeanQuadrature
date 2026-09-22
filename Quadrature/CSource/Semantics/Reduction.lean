import Quadrature.CSource.Semantics.Strategy

/-!
# C expression reduction with unspecified operand order

These are the expression rules of CompCert's `cfrontend/Csem.v`, at the
revision recorded in `Quadrature.Clight.Source`, instantiated with the same
values, memory and arithmetic as the existing C development.

`Context` permits a step in either operand of an ordinary binary operation,
assignment or call. Sequential operators expose only their first operand.
`NotStuck` requires every exposed subexpression to be immediately safe; this
also detects undefined behavior in a branch that another evaluation order
could postpone.

`Lred` and `Rred` reduce one operation. `Callred` identifies a function call;
the machine in `SmallStep` enters its body and later resumes the context.
Function calls are therefore not assumptions about atomic evaluation.
-/

namespace Quadrature.CSource.C

open CC

/-- Cast arguments that have already reduced to values to the parameter types. -/
inductive CastArguments (memory : Mem) : Exprlist → List Ty → List Val → Prop where
  | nil : CastArguments memory .Enil [] []
  | cons (value type rest parameter parameters cast values) :
      Cop.semCast value type parameter memory = some cast →
      CastArguments memory rest parameters values →
      CastArguments memory (.Econs (.Eval value type) rest)
        (parameter :: parameters) (cast :: values)

/-- A head reduction of a C location. Location computation leaves memory unchanged. -/
inductive Lred (ge : ExpressionEnv) (locals : Env) : Expr → Mem → Expr → Mem → Prop where
  | var_local (name type memory block) :
      locals.get name = some (block, type) →
      Lred ge locals (.Evar name type) memory
        (.Eloc block Integers.Ptrofs.zero .Full type) memory
  | var_global (name type memory block) :
      locals.get name = none →
      ge.symbols.find_symbol name = some block →
      Lred ge locals (.Evar name type) memory
        (.Eloc block Integers.Ptrofs.zero .Full type) memory
  | deref (block offset pointerType type memory) :
      Lred ge locals (.Ederef (.Eval (.Vptr block offset) pointerType) type) memory
        (.Eloc block offset .Full type) memory
  | field_struct (block offset name composite attr field type memory delta bitfield) :
      ge.composites.get name = some composite →
      fieldOffset ge.composites field composite.co_members = .OK (delta, bitfield) →
      Lred ge locals (.Efield (.Eval (.Vptr block offset) (.Tstruct name attr)) field type)
        memory (.Eloc block (Integers.Ptrofs.add offset (Integers.Ptrofs.repr delta))
          bitfield type) memory
  | field_union (block offset name composite attr field type memory delta bitfield) :
      ge.composites.get name = some composite →
      unionFieldOffset ge.composites field composite.co_members = .OK (delta, bitfield) →
      Lred ge locals (.Efield (.Eval (.Vptr block offset) (.Tunion name attr)) field type)
        memory (.Eloc block (Integers.Ptrofs.add offset (Integers.Ptrofs.repr delta))
          bitfield type) memory

variable [ExternalCalls]

/-- A head reduction of a C value expression, including its memory effects and trace. -/
inductive Rred (ge : GlobalEnv) : Expr → Mem → Trace → Expr → Mem → Prop where
  | rvalof (block offset bitfield type memory trace value) :
      DerefLoc ge.expressionEnv type memory block offset bitfield trace value →
      Rred ge (.Evalof (.Eloc block offset bitfield type) type) memory
        trace (.Eval value type) memory
  | addrof (block offset locationType type memory) :
      Rred ge (.Eaddrof (.Eloc block offset .Full locationType) type) memory
        E0 (.Eval (.Vptr block offset) type) memory
  | unop (op arg argType type memory value) :
      Cop.semUnaryOperation op arg argType memory = some value →
      Rred ge (.Eunop op (.Eval arg argType) type) memory E0 (.Eval value type) memory
  | binop (op left leftType right rightType type memory value) :
      Cop.semBinaryOperation ge.composites op left leftType right rightType memory =
        some value →
      Rred ge (.Ebinop op (.Eval left leftType) (.Eval right rightType) type) memory
        E0 (.Eval value type) memory
  | cast (type arg argType memory value) :
      Cop.semCast arg argType type memory = some value →
      Rred ge (.Ecast (.Eval arg argType) type) memory E0 (.Eval value type) memory
  | seqand_true (value valueType right type memory) :
      Cop.boolVal value valueType memory = some true →
      Rred ge (.Eseqand (.Eval value valueType) right type) memory
        E0 (.Eparen right (.Tint .IBool .Signed noattr) type) memory
  | seqand_false (value valueType right type memory) :
      Cop.boolVal value valueType memory = some false →
      Rred ge (.Eseqand (.Eval value valueType) right type) memory
        E0 (.Eval (.Vint Integers.Int.zero) type) memory
  | seqor_true (value valueType right type memory) :
      Cop.boolVal value valueType memory = some true →
      Rred ge (.Eseqor (.Eval value valueType) right type) memory
        E0 (.Eval (.Vint Integers.Int.one) type) memory
  | seqor_false (value valueType right type memory) :
      Cop.boolVal value valueType memory = some false →
      Rred ge (.Eseqor (.Eval value valueType) right type) memory
        E0 (.Eparen right (.Tint .IBool .Signed noattr) type) memory
  | condition (value valueType yes no type flag memory) :
      Cop.boolVal value valueType memory = some flag →
      Rred ge (.Econdition (.Eval value valueType) yes no type) memory
        E0 (.Eparen (if flag then yes else no) type type) memory
  | sizeof (arg type memory) :
      Rred ge (.Esizeof arg type) memory
        E0 (.Eval (Val.Vptrofs (Integers.Ptrofs.repr (CC.sizeof ge.composites arg))) type)
        memory
  | alignof (arg type memory) :
      Rred ge (.Ealignof arg type) memory
        E0 (.Eval (Val.Vptrofs (Integers.Ptrofs.repr (CC.alignof ge.composites arg))) type)
        memory
  | assign (block offset type bitfield rhs rhsType memory cast trace final value) :
      Cop.semCast rhs rhsType type memory = some cast →
      AssignLoc ge.expressionEnv type memory block offset bitfield cast trace final value →
      Rred ge (.Eassign (.Eloc block offset bitfield type) (.Eval rhs rhsType) type)
        memory trace (.Eval value type) final
  | assignop (op block offset type bitfield rhs rhsType resultType memory trace value) :
      DerefLoc ge.expressionEnv type memory block offset bitfield trace value →
      Rred ge (.Eassignop op (.Eloc block offset bitfield type) (.Eval rhs rhsType)
        resultType type) memory trace
        (.Eassign (.Eloc block offset bitfield type)
          (.Ebinop op (.Eval value type) (.Eval rhs rhsType) resultType) type) memory
  | postincr (direction block offset type bitfield memory trace value) :
      DerefLoc ge.expressionEnv type memory block offset bitfield trace value →
      Rred ge (.Epostincr direction (.Eloc block offset bitfield type) type) memory trace
        (.Ecomma (.Eassign (.Eloc block offset bitfield type)
          (.Ebinop (match direction with | .incr => .Oadd | .decr => .Osub)
            (.Eval value type) (.Eval (.Vint Integers.Int.one) type_int32s)
            (incrDecrType type)) type) (.Eval value type) type) memory
  | comma (value valueType right type memory) :
      typeof right = type →
      Rred ge (.Ecomma (.Eval value valueType) right type) memory E0 right memory
  | paren (value valueType castType type memory result) :
      Cop.semCast value valueType castType memory = some result →
      Rred ge (.Eparen (.Eval value valueType) castType type) memory
        E0 (.Eval result type) memory
  | builtin (function argTypes args type memory values trace result final) :
      CastArguments memory args argTypes values →
      externalCall function (Genv.toSenv ge.globals) values memory trace result final →
      Rred ge (.Ebuiltin function argTypes args type) memory trace (.Eval result type) final

/-- Identify the function and converted arguments of a call whose operands are values. -/
inductive Callred (ge : GlobalEnv) :
    Expr → Mem → FunDef → List Val → Ty → Prop where
  | call (callee calleeType memory argTypes resultType cc args type function values) :
      Genv.findFunct ge.globals callee = some function →
      CastArguments memory args argTypes values →
      typeOfFundef function = .Tfunction argTypes resultType cc →
      Cop.classifyFun calleeType = .f argTypes resultType cc →
      Callred ge (.Ecall (.Eval callee calleeType) args type) memory function values type

mutual
/-- An exposed expression position. Both sides of unsequenced operations can reduce. -/
inductive Context : Kind → Kind → (Expr → Expr) → Prop where
  | top (kind) : Context kind kind id
  | deref (kind context type) :
      Context kind .RV context →
      Context kind .LV (fun arg => .Ederef (context arg) type)
  | field (kind context name type) :
      Context kind .RV context →
      Context kind .LV (fun arg => .Efield (context arg) name type)
  | rvalof (kind context type) :
      Context kind .LV context →
      Context kind .RV (fun arg => .Evalof (context arg) type)
  | addrof (kind context type) :
      Context kind .LV context →
      Context kind .RV (fun arg => .Eaddrof (context arg) type)
  | unop (kind context op type) :
      Context kind .RV context →
      Context kind .RV (fun arg => .Eunop op (context arg) type)
  | binop_left (kind context op right type) :
      Context kind .RV context →
      Context kind .RV (fun arg => .Ebinop op (context arg) right type)
  | binop_right (kind context op left type) :
      Context kind .RV context →
      Context kind .RV (fun arg => .Ebinop op left (context arg) type)
  | cast (kind context type) :
      Context kind .RV context →
      Context kind .RV (fun arg => .Ecast (context arg) type)
  | seqand (kind context right type) :
      Context kind .RV context →
      Context kind .RV (fun arg => .Eseqand (context arg) right type)
  | seqor (kind context right type) :
      Context kind .RV context →
      Context kind .RV (fun arg => .Eseqor (context arg) right type)
  | condition (kind context yes no type) :
      Context kind .RV context →
      Context kind .RV (fun arg => .Econdition (context arg) yes no type)
  | assign_left (kind context right type) :
      Context kind .LV context →
      Context kind .RV (fun arg => .Eassign (context arg) right type)
  | assign_right (kind context left type) :
      Context kind .RV context →
      Context kind .RV (fun arg => .Eassign left (context arg) type)
  | assignop_left (kind context op right resultType type) :
      Context kind .LV context →
      Context kind .RV (fun arg => .Eassignop op (context arg) right resultType type)
  | assignop_right (kind context op left resultType type) :
      Context kind .RV context →
      Context kind .RV (fun arg => .Eassignop op left (context arg) resultType type)
  | postincr (kind context op type) :
      Context kind .LV context →
      Context kind .RV (fun arg => .Epostincr op (context arg) type)
  | call_left (kind context args type) :
      Context kind .RV context →
      Context kind .RV (fun arg => .Ecall (context arg) args type)
  | call_right (kind context callee type) :
      ContextList kind context →
      Context kind .RV (fun arg => .Ecall callee (context arg) type)
  | builtin (kind context function argTypes type) :
      ContextList kind context →
      Context kind .RV (fun arg => .Ebuiltin function argTypes (context arg) type)
  | comma (kind context right type) :
      Context kind .RV context →
      Context kind .RV (fun arg => .Ecomma (context arg) right type)
  | paren (kind context castType type) :
      Context kind .RV context →
      Context kind .RV (fun arg => .Eparen (context arg) castType type)

/-- Any argument of a call may reduce before any other argument. -/
inductive ContextList : Kind → (Expr → Exprlist) → Prop where
  | head (kind context rest) :
      Context kind .RV context →
      ContextList kind (fun arg => .Econs (context arg) rest)
  | tail (kind context first) :
      ContextList kind context →
      ContextList kind (fun arg => .Econs first (context arg))
end

/-- An expression is a value of the required kind, or has an exposed reduction or call. -/
inductive ImmSafe (ge : GlobalEnv) (locals : Env) : Kind → Expr → Mem → Prop where
  | value (value type memory) : ImmSafe ge locals .RV (.Eval value type) memory
  | location (block offset bitfield type memory) :
      ImmSafe ge locals .LV (.Eloc block offset bitfield type) memory
  | lred (kind context expr memory result final) :
      Lred ge.expressionEnv locals expr memory result final →
      Context .LV kind context →
      ImmSafe ge locals kind (context expr) memory
  | rred (kind context expr memory trace result final) :
      Rred ge expr memory trace result final →
      Context .RV kind context →
      ImmSafe ge locals kind (context expr) memory
  | callred (kind context expr memory function args type) :
      Callred ge expr memory function args type →
      Context .RV kind context →
      ImmSafe ge locals kind (context expr) memory

/-- Every subexpression that C allows to evaluate next is immediately safe. -/
def NotStuck (ge : GlobalEnv) (locals : Env) (expr : Expr) (memory : Mem) : Prop :=
  ∀ kind context arg, Context kind .RV context → expr = context arg →
    ImmSafe ge locals kind arg memory

end Quadrature.CSource.C
