import Quadrature.CSource.Semantics.ExpressionReduction

/-!
# Exposed positions in sequencing and scalar updates

These inversion lemmas describe precisely the contexts allowed by C for the
intermediate expressions of post-increment. They distinguish the whole
expression from its operands without imposing an evaluation order.
-/

namespace Quadrature.CSource.C

open CC

/-- A comma expression exposes itself or a position in its left operand. -/
theorem Context.comma_cases {input : Kind} {context : Expr → Expr}
    {arg left right : Expr} {type : Ty}
    (hcontext : Context input .RV context)
    (heq : Expr.Ecomma left right type = context arg) :
    (input = .RV ∧ context = id ∧ arg = .Ecomma left right type) ∨
      ∃ inner, Context input .RV inner ∧
        context = (fun expr => .Ecomma (inner expr) right type) ∧ left = inner arg := by
  cases hcontext with
  | top => exact .inl ⟨rfl, rfl, heq.symm⟩
  | comma context right type hcontext =>
      obtain ⟨hleft, rfl, rfl⟩ := Expr.Ecomma.inj heq
      exact .inr ⟨context, hcontext, rfl, hleft⟩
  | rvalof | addrof | unop | binop_left | binop_right | cast | seqand | seqor
  | condition | assign_left | assign_right | assignop_left | assignop_right | postincr
  | call_left | call_right | builtin | paren => cases heq

/-- An assignment exposes itself or a position in either operand. -/
theorem Context.assign_cases {input : Kind} {context : Expr → Expr}
    {arg left right : Expr} {type : Ty}
    (hcontext : Context input .RV context)
    (heq : Expr.Eassign left right type = context arg) :
    (input = .RV ∧ context = id ∧ arg = .Eassign left right type) ∨
      (∃ inner, Context input .LV inner ∧
        context = (fun expr => .Eassign (inner expr) right type) ∧ left = inner arg) ∨
      (∃ inner, Context input .RV inner ∧
        context = (fun expr => .Eassign left (inner expr) type) ∧ right = inner arg) := by
  cases hcontext with
  | top => exact .inl ⟨rfl, rfl, heq.symm⟩
  | assign_left context right type hcontext =>
      obtain ⟨hleft, rfl, rfl⟩ := Expr.Eassign.inj heq
      exact .inr (.inl ⟨context, hcontext, rfl, hleft⟩)
  | assign_right context left type hcontext =>
      obtain ⟨rfl, hright, rfl⟩ := Expr.Eassign.inj heq
      exact .inr (.inr ⟨context, hcontext, rfl, hright⟩)
  | rvalof | addrof | unop | binop_left | binop_right | cast | seqand | seqor
  | condition | assignop_left | assignop_right | postincr
  | call_left | call_right | builtin | comma | paren => cases heq

/-- A binary operation exposes itself or a position in either operand. -/
theorem Context.binop_cases {input : Kind} {context : Expr → Expr}
    {arg left right : Expr} {op : Binop} {type : Ty}
    (hcontext : Context input .RV context)
    (heq : Expr.Ebinop op left right type = context arg) :
    (input = .RV ∧ context = id ∧ arg = .Ebinop op left right type) ∨
      (∃ inner, Context input .RV inner ∧
        context = (fun expr => .Ebinop op (inner expr) right type) ∧ left = inner arg) ∨
      (∃ inner, Context input .RV inner ∧
        context = (fun expr => .Ebinop op left (inner expr) type) ∧ right = inner arg) := by
  cases hcontext with
  | top => exact .inl ⟨rfl, rfl, heq.symm⟩
  | binop_left context op right type hcontext =>
      obtain ⟨rfl, hleft, rfl, rfl⟩ := Expr.Ebinop.inj heq
      exact .inr (.inl ⟨context, hcontext, rfl, hleft⟩)
  | binop_right context op left type hcontext =>
      obtain ⟨rfl, rfl, hright, rfl⟩ := Expr.Ebinop.inj heq
      exact .inr (.inr ⟨context, hcontext, rfl, hright⟩)
  | rvalof | addrof | unop | cast | seqand | seqor | condition
  | assign_left | assign_right | assignop_left | assignop_right | postincr
  | call_left | call_right | builtin | comma | paren => cases heq

/-- Post-increment exposes itself or a position in its lvalue operand. -/
theorem Context.postincr_cases {input : Kind} {context : Expr → Expr}
    {arg left : Expr} {direction : IncrOrDecr} {type : Ty}
    (hcontext : Context input .RV context)
    (heq : Expr.Epostincr direction left type = context arg) :
    (input = .RV ∧ context = id ∧ arg = .Epostincr direction left type) ∨
      ∃ inner, Context input .LV inner ∧
        context = (fun expr => .Epostincr direction (inner expr) type) ∧ left = inner arg := by
  cases hcontext with
  | top => exact .inl ⟨rfl, rfl, heq.symm⟩
  | postincr context direction type hcontext =>
      obtain ⟨rfl, hleft, rfl⟩ := Expr.Epostincr.inj heq
      exact .inr ⟨context, hcontext, rfl, hleft⟩
  | rvalof | addrof | unop | binop_left | binop_right | cast | seqand | seqor
  | condition | assign_left | assign_right | assignop_left | assignop_right
  | call_left | call_right | builtin | comma | paren => cases heq

/-- A variable has no proper exposed positions. -/
theorem Context.variable_cases {input : Kind} {context : Expr → Expr}
    {arg : Expr} {name : Ident} {type : Ty}
    (hcontext : Context input .LV context)
    (heq : Expr.Evar name type = context arg) :
    input = .LV ∧ context = id ∧ arg = .Evar name type := by
  cases hcontext with
  | top => exact ⟨rfl, rfl, heq.symm⟩
  | deref | field => cases heq

/-- A comma expression with a computed left operand is in head form. -/
theorem HeadForm.comma (value : Val) (valueType : Ty) (right : Expr) (type : Ty) :
    HeadForm (.Ecomma (.Eval value valueType) right type) := by
  intro kind context arg hcontext heq
  rcases hcontext.comma_cases heq with ⟨hk, hc, _⟩ | ⟨inner, hi, _, he⟩
  · exact .inl ⟨hk, hc⟩
  · exact .inr ((he ▸ Normal.value value valueType).in_context hi)

/-- Post-increment of a computed location is in head form. -/
theorem HeadForm.postincr (direction : IncrOrDecr) (block : Block) (offset : Integers.Ptrofs)
    (bitfield : Bitfield) (type : Ty) :
    HeadForm (.Epostincr direction (.Eloc block offset bitfield type) type) := by
  intro kind context arg hcontext heq
  rcases hcontext.postincr_cases heq with ⟨hk, hc, _⟩ | ⟨inner, hi, _, he⟩
  · exact .inl ⟨hk, hc⟩
  · exact .inr ((he ▸ Normal.location block offset bitfield type).in_context hi)

/-- Assignment of a computed value to a computed location is in head form. -/
theorem HeadForm.assign (block : Block) (offset : Integers.Ptrofs) (bitfield : Bitfield)
    (type : Ty) (value : Val) (valueType : Ty) :
    HeadForm (.Eassign (.Eloc block offset bitfield type) (.Eval value valueType) type) := by
  intro kind context arg hcontext heq
  rcases hcontext.assign_cases heq with
    ⟨hk, hc, _⟩ | ⟨inner, hi, _, he⟩ | ⟨inner, hi, _, he⟩
  · exact .inl ⟨hk, hc⟩
  · exact .inr ((he ▸ Normal.location block offset bitfield type).in_context hi)
  · exact .inr ((he ▸ Normal.value value valueType).in_context hi)

/-- A binary operation on computed values is in head form. -/
theorem HeadForm.binop (op : Binop) (left right : Val)
    (leftType rightType type : Ty) :
    HeadForm (.Ebinop op (.Eval left leftType) (.Eval right rightType) type) := by
  intro kind context arg hcontext heq
  rcases hcontext.binop_cases heq with
    ⟨hk, hc, _⟩ | ⟨inner, hi, _, he⟩ | ⟨inner, hi, _, he⟩
  · exact .inl ⟨hk, hc⟩
  · exact .inr ((he ▸ Normal.value left leftType).in_context hi)
  · exact .inr ((he ▸ Normal.value right rightType).in_context hi)

end Quadrature.CSource.C
