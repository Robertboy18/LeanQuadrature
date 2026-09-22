import Quadrature.CSource.Semantics.PureTotal

/-!
# Expressions whose calls preserve caller memory

`ReadEval` assigns fixed values to expression operands. Reads and arithmetic
must remain valid after any sequence of calls that preserves the original
memory. Each call carries a `SmallStep.CallCorrect` proof for its actual C
body, including all of that body's permitted execution orders.

This judgment covers the expression forms used by the quadrature library.
Its memory condition permits different orders of local allocation in sibling
calls without identifying the final memory states.
-/

namespace Quadrature.CSource.C

open CC

variable [ExternalCalls]

mutual
/-- An expression has a fixed value while calls preserve `base` memory. -/
inductive ReadEval (ge : GlobalEnv) (locals : Env) (base : Mem) :
    Kind → Expr → PureResult → Prop where
  | value (value type) : ReadEval ge locals base .RV (.Eval value type) (.value value)
  | location (block offset bitfield type) :
      ReadEval ge locals base .LV (.Eloc block offset bitfield type)
        (.location block offset bitfield)
  | var_local (name type block) :
      locals.get name = some (block, type) →
      ReadEval ge locals base .LV (.Evar name type)
        (.location block Integers.Ptrofs.zero .Full)
  | var_global (name type block) :
      locals.get name = none →
      ge.expressionEnv.symbols.find_symbol name = some block →
      ReadEval ge locals base .LV (.Evar name type)
        (.location block Integers.Ptrofs.zero .Full)
  | deref (arg type block offset) :
      ReadEval ge locals base .RV arg (.value (.Vptr block offset)) →
      ReadEval ge locals base .LV (.Ederef arg type) (.location block offset .Full)
  | rvalof (arg type block offset bitfield value) :
      ReadEval ge locals base .LV arg (.location block offset bitfield) →
      type = typeof arg →
      typeIsVolatile type = false →
      (∀ memory, CallMemory base memory →
        DerefLoc ge.expressionEnv type memory block offset bitfield E0 value) →
      ReadEval ge locals base .RV (.Evalof arg type) (.value value)
  | addrof (arg type block offset) :
      ReadEval ge locals base .LV arg (.location block offset .Full) →
      ReadEval ge locals base .RV (.Eaddrof arg type) (.value (.Vptr block offset))
  | unop (op arg type value result) :
      ReadEval ge locals base .RV arg (.value value) →
      (∀ memory, CallMemory base memory →
        Cop.semUnaryOperation op value (typeof arg) memory = some result) →
      ReadEval ge locals base .RV (.Eunop op arg type) (.value result)
  | binop (op left right type leftValue rightValue result) :
      ReadEval ge locals base .RV left (.value leftValue) →
      ReadEval ge locals base .RV right (.value rightValue) →
      (∀ memory, CallMemory base memory →
        Cop.semBinaryOperation ge.composites op leftValue (typeof left)
          rightValue (typeof right) memory = some result) →
      ReadEval ge locals base .RV (.Ebinop op left right type) (.value result)
  | cast (arg type value result) :
      ReadEval ge locals base .RV arg (.value value) →
      (∀ memory, CallMemory base memory →
        Cop.semCast value (typeof arg) type memory = some result) →
      ReadEval ge locals base .RV (.Ecast arg type) (.value result)
  | call (callee args type pointer parameters returnType cc function values result) :
      ReadEval ge locals base .RV callee (.value pointer) →
      ReadList ge locals base args parameters values →
      Genv.findFunct ge.globals pointer = some function →
      typeOfFundef function = .Tfunction parameters returnType cc →
      Cop.classifyFun (typeof callee) = .f parameters returnType cc →
      (∀ memory, CallMemory base memory →
        SmallStep.CallCorrect ge memory function values result) →
      ReadEval ge locals base .RV (.Ecall callee args type) (.value result)

/-- Call arguments have fixed values after conversion to their parameter types. -/
inductive ReadList (ge : GlobalEnv) (locals : Env) (base : Mem) :
    Exprlist → List Ty → List Val → Prop where
  | nil : ReadList ge locals base .Enil [] []
  | cons (arg rest type types value values cast) :
      ReadEval ge locals base .RV arg (.value value) →
      (∀ memory, CallMemory base memory →
        Cop.semCast value (typeof arg) type memory = some cast) →
      ReadList ge locals base rest types values →
      ReadList ge locals base (.Econs arg rest) (type :: types) (cast :: values)
end

/-- A literal retains its value in the read-only judgment. -/
theorem ReadEval.value_iff {ge : GlobalEnv} {locals : Env} {base : Mem}
    {value result : Val} {type : Ty} :
    ReadEval ge locals base .RV (.Eval value type) (.value result) ↔ result = value := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .value _ _

/-- A computed location retains its address in the read-only judgment. -/
theorem ReadEval.location_iff {ge : GlobalEnv} {locals : Env} {base : Mem}
    {block resultBlock : Block} {offset resultOffset : Integers.Ptrofs}
    {bitfield resultBitfield : Bitfield} {type : Ty} :
    ReadEval ge locals base .LV (.Eloc block offset bitfield type)
      (.location resultBlock resultOffset resultBitfield) ↔
      resultBlock = block ∧ resultOffset = offset ∧ resultBitfield = bitfield := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact .location _ _ _ _

/-- Any exposed operand has a fixed meaning, and replacing it by an expression of the same
type and meaning preserves the enclosing expression's proof. -/
theorem ReadEval.in_context {ge : GlobalEnv} {locals : Env} {base : Mem}
    {input output : Kind} {context : Expr → Expr}
    (hcontext : Context input output context) {expr : Expr} {result : PureResult}
    (heval : ReadEval ge locals base output (context expr) result) :
    ∃ operand,
      ReadEval ge locals base input expr operand ∧
      ∀ replacement, typeof replacement = typeof expr →
        ReadEval ge locals base input replacement operand →
        ReadEval ge locals base output (context replacement) result := by
  induction hcontext using Context.rec
      (motive_2 := fun context _ =>
        ∀ {expr types values}, ReadList ge locals base (context expr) types values →
          ∃ operand, ReadEval ge locals base input expr operand ∧
            ∀ replacement, typeof replacement = typeof expr →
              ReadEval ge locals base input replacement operand →
              ReadList ge locals base (context replacement) types values)
      generalizing expr result with
  | top => exact ⟨result, heval, fun _ _ h => h⟩
  | deref context type hcontext ih =>
      cases heval with
      | deref _ _ _ _ harg =>
          obtain ⟨operand, harg, hreplace⟩ := ih harg
          exact ⟨operand, harg, fun replacement htype h =>
            .deref _ _ _ _ (hreplace replacement htype h)⟩
  | rvalof context type hcontext ih =>
      cases heval with
      | rvalof _ _ block offset bitfield value harg ht hv hd =>
          obtain ⟨operand, harg, hreplace⟩ := ih harg
          exact ⟨operand, harg, fun replacement htype h =>
            .rvalof _ _ _ _ _ _ (hreplace replacement htype h)
              (ht.trans (hcontext.typeof_eq htype).symm) hv hd⟩
  | addrof context type hcontext ih =>
      cases heval with
      | addrof _ _ _ _ harg =>
          obtain ⟨operand, harg, hreplace⟩ := ih harg
          exact ⟨operand, harg, fun replacement htype h =>
            .addrof _ _ _ _ (hreplace replacement htype h)⟩
  | unop context op type hcontext ih =>
      cases heval with
      | unop _ _ _ value result harg hop =>
          obtain ⟨operand, harg, hreplace⟩ := ih harg
          refine ⟨operand, harg, fun replacement htype h =>
            .unop _ _ _ _ _ (hreplace replacement htype h) ?_⟩
          simpa only [hcontext.typeof_eq htype] using hop
  | binop_left context op right type hcontext ih =>
      cases heval with
      | binop _ _ _ _ leftValue rightValue result hleft hright hop =>
          obtain ⟨operand, harg, hreplace⟩ := ih hleft
          refine ⟨operand, harg, fun replacement htype h =>
            .binop _ _ _ _ _ _ _ (hreplace replacement htype h) hright ?_⟩
          simpa only [hcontext.typeof_eq htype] using hop
  | binop_right context op left type hcontext ih =>
      cases heval with
      | binop _ _ _ _ leftValue rightValue result hleft hright hop =>
          obtain ⟨operand, harg, hreplace⟩ := ih hright
          refine ⟨operand, harg, fun replacement htype h =>
            .binop _ _ _ _ _ _ _ hleft (hreplace replacement htype h) ?_⟩
          simpa only [hcontext.typeof_eq htype] using hop
  | cast context type hcontext ih =>
      cases heval with
      | cast _ _ value result harg hcast =>
          obtain ⟨operand, harg, hreplace⟩ := ih harg
          refine ⟨operand, harg, fun replacement htype h =>
            .cast _ _ _ _ (hreplace replacement htype h) ?_⟩
          simpa only [hcontext.typeof_eq htype] using hcast
  | call_left context args type hcontext ih =>
      cases heval with
      | call _ _ _ pointer parameters returnType cc function values result
          hcallee hargs hfind ht hc hcall =>
          obtain ⟨operand, harg, hreplace⟩ := ih hcallee
          refine ⟨operand, harg, fun replacement htype h =>
            .call _ _ _ _ _ _ _ _ _ _ (hreplace replacement htype h)
              hargs hfind ht ?_ hcall⟩
          simpa only [hcontext.typeof_eq htype] using hc
  | call_right context callee type hcontext ih =>
      cases heval with
      | call _ _ _ pointer parameters returnType cc function values result
          hcallee hargs hfind ht hc hcall =>
          obtain ⟨operand, harg, hreplace⟩ := ih hargs
          exact ⟨operand, harg, fun replacement htype h =>
            .call _ _ _ _ _ _ _ _ _ _ hcallee (hreplace replacement htype h)
              hfind ht hc hcall⟩
  | head context rest hcontext ih =>
      rename_i expr types values heval
      cases heval with
      | cons _ _ type types value values cast hfirst hcast hrest =>
          obtain ⟨operand, harg, hreplace⟩ := ih hfirst
          refine ⟨operand, harg, fun replacement htype h =>
            .cons _ _ _ _ _ _ _ (hreplace replacement htype h) ?_ hrest⟩
          simpa only [hcontext.typeof_eq htype] using hcast
  | tail context first hcontext ih =>
      rename_i expr types values heval
      cases heval with
      | cons _ _ type types value values cast hfirst hcast hrest =>
          obtain ⟨operand, harg, hreplace⟩ := ih hrest
          exact ⟨operand, harg, fun replacement htype h =>
            .cons _ _ _ _ _ _ _ hfirst hcast (hreplace replacement htype h)⟩
  | field | seqand | seqor | condition | assign_left | assign_right
  | assignop_left | assignop_right | postincr | builtin | comma | paren => cases heval

end Quadrature.CSource.C
