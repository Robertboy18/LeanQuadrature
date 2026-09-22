import Quadrature.CSource.Semantics.Reduction

/-!
# Composition and size of C expression contexts

`Context.comp` permits reductions beneath several enclosing operators.
`Expr.work` counts syntax constructors, without counting the representation
of a value or type. Reducing arithmetic therefore decreases this measure
even when the resulting binary64 value has a larger bit pattern.
-/

namespace Quadrature.CSource.C

open CC

/-- Composing two exposed positions gives an exposed position of the whole expression. -/
theorem Context.comp {middle output : Kind} {outer : Expr → Expr}
    (houter : Context middle output outer) {input : Kind} {inner : Expr → Expr}
    (hinner : Context input middle inner) :
    Context input output (fun expr => outer (inner expr)) := by
  induction houter using Context.rec
      (motive_2 := fun outer _ =>
        ∀ {input inner}, Context input middle inner →
          ContextList input (fun expr => outer (inner expr)))
      generalizing input inner with
  | top => exact hinner
  | deref _ _ _ ih => exact .deref _ _ _ (ih hinner)
  | field _ _ _ _ ih => exact .field _ _ _ _ (ih hinner)
  | rvalof _ _ _ ih => exact .rvalof _ _ _ (ih hinner)
  | addrof _ _ _ ih => exact .addrof _ _ _ (ih hinner)
  | unop _ _ _ _ ih => exact .unop _ _ _ _ (ih hinner)
  | binop_left _ _ _ _ _ ih => exact .binop_left _ _ _ _ _ (ih hinner)
  | binop_right _ _ _ _ _ ih => exact .binop_right _ _ _ _ _ (ih hinner)
  | cast _ _ _ ih => exact .cast _ _ _ (ih hinner)
  | seqand _ _ _ _ ih => exact .seqand _ _ _ _ (ih hinner)
  | seqor _ _ _ _ ih => exact .seqor _ _ _ _ (ih hinner)
  | condition _ _ _ _ _ ih => exact .condition _ _ _ _ _ (ih hinner)
  | assign_left _ _ _ _ ih => exact .assign_left _ _ _ _ (ih hinner)
  | assign_right _ _ _ _ ih => exact .assign_right _ _ _ _ (ih hinner)
  | assignop_left _ _ _ _ _ _ ih => exact .assignop_left _ _ _ _ _ _ (ih hinner)
  | assignop_right _ _ _ _ _ _ ih => exact .assignop_right _ _ _ _ _ _ (ih hinner)
  | postincr _ _ _ _ ih => exact .postincr _ _ _ _ (ih hinner)
  | call_left _ _ _ _ ih => exact .call_left _ _ _ _ (ih hinner)
  | call_right _ _ _ _ ih => exact .call_right _ _ _ _ (ih hinner)
  | builtin _ _ _ _ _ ih => exact .builtin _ _ _ _ _ (ih hinner)
  | comma _ _ _ _ ih => exact .comma _ _ _ _ (ih hinner)
  | paren _ _ _ _ ih => exact .paren _ _ _ _ (ih hinner)
  | head _ _ _ ih =>
      exact .head _ _ _ (ih (by assumption))
  | tail _ _ _ ih =>
      exact .tail _ _ _ (ih (by assumption))

mutual
/-- The number of operations remaining in an expression, ignoring values and types. -/
def Expr.work : Expr → Nat
  | .Eval .. | .Eloc .. => 0
  | .Evar .. | .Esizeof .. | .Ealignof .. => 1
  | .Efield arg _ _ | .Evalof arg _ | .Ederef arg _ | .Eaddrof arg _
  | .Eunop _ arg _ | .Ecast arg _ | .Eparen arg _ _ =>
      arg.work + 1
  | .Ebinop _ left right _ | .Eseqand left right _ | .Eseqor left right _
  | .Eassign left right _ | .Ecomma left right _ =>
      left.work + right.work + 1
  | .Eassignop _ left right _ _ => left.work + right.work + 3
  | .Epostincr _ arg _ => arg.work + 4
  | .Econdition test yes no _ => test.work + yes.work + no.work + 1
  | .Ecall fn args _ => fn.work + args.work + 1
  | .Ebuiltin _ _ args _ => args.work + 1

/-- The sum of the work remaining in a call's arguments. -/
def Exprlist.work : Exprlist → Nat
  | .Enil => 0
  | .Econs first rest => first.work + rest.work
end

/-- Decreasing the work at an exposed position decreases it in the whole expression. -/
theorem Context.work_lt {input output : Kind} {context : Expr → Expr}
    (hcontext : Context input output context) {left right : Expr}
    (hwork : left.work < right.work) :
    (context left).work < (context right).work := by
  induction hcontext using Context.rec
      (motive_2 := fun context _ => (context left).work < (context right).work) <;>
    simp only [Expr.work, Exprlist.work, id_eq] at * <;> omega

end Quadrature.CSource.C
