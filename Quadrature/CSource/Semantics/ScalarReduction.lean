import Quadrature.CSource.Semantics.ReductionContexts
import Quadrature.CSource.Semantics.StoreExpression

/-!
# Unique reductions for scalar operations

Computed arithmetic, nonvolatile stores, and comma sequencing have unique
successors. Post-increment first resolves its local variable and then reads
the old value before expanding into a store followed by that value.
-/

namespace Quadrature.CSource.C

open CC hiding State Cont Step
open SmallStep

variable [ExternalCalls]

/-- Computed binary operands reduce to the value given by C arithmetic. -/
theorem ExpressionReduction.binop {ge : GlobalEnv} {locals : Env} {memory : Mem}
    {op : Binop} {left right value : Val} {leftType rightType type : Ty}
    (hoperation : Cop.semBinaryOperation ge.composites op left leftType right rightType
      memory = some value) :
    ExpressionReduction ge locals memory
      (.Ebinop op (.Eval left leftType) (.Eval right rightType) type)
      (.Eval value type) memory := by
  apply ExpressionReduction.head (.binop _ _ _ _ _ _) (.binop _ _ _ _ _ _ _ _ hoperation)
  intro trace reduced final hred
  cases hred with
  | binop _ _ _ _ _ _ _ actual hactual =>
      have heq := Option.some.inj (hactual.symm.trans hoperation)
      subst actual
      exact ⟨rfl, rfl, rfl⟩

/-- A nonvolatile scalar assignment performs exactly the specified store. -/
theorem ExpressionReduction.assign {ge : GlobalEnv} {locals : Env} {memory final : Mem}
    {block : Block} {offset : Integers.Ptrofs} {type rhsType : Ty} {chunk : Chunk}
    {rhs value : Val}
    (hmode : accessMode type = .By_value chunk) (hv : typeIsVolatile type = false)
    (hcast : Cop.semCast rhs rhsType type memory = some value)
    (hstore : Mem.storev chunk memory (.Vptr block offset) value = some final) :
    ExpressionReduction ge locals memory
      (.Eassign (.Eloc block offset .Full type) (.Eval rhs rhsType) type)
      (.Eval value type) final := by
  apply ExpressionReduction.head (.assign _ _ _ _ _ _)
    (.assign _ _ _ _ _ _ _ _ _ _ _ hcast (.value _ _ _ hmode hv hstore))
  intro trace reduced last hred
  cases hred with
  | assign _ _ _ _ _ _ _ cast _ _ result hc hs =>
      have heq := Option.some.inj (hc.symm.trans hcast)
      subst cast
      obtain ⟨rfl, rfl, hs⟩ := (assignLoc_value_iff hmode hv).mp hs
      have heq := Option.some.inj (hs.symm.trans hstore)
      subst last
      exact ⟨rfl, rfl, rfl⟩

/-- Comma sequencing discards the computed left operand. -/
theorem ExpressionReduction.comma_value {ge : GlobalEnv} {locals : Env} {memory : Mem}
    (value : Val) (valueType : Ty) (right : Expr) (type : Ty)
    (htype : typeof right = type) :
    ExpressionReduction ge locals memory (.Ecomma (.Eval value valueType) right type)
      right memory := by
  apply ExpressionReduction.head (.comma _ _ _ _) (.comma _ _ _ _ _ htype)
  intro trace reduced final hred
  cases hred
  exact ⟨rfl, rfl, rfl⟩

/-- Resolving a local variable is the unique first step of its post-increment. -/
theorem ExpressionReduction.postincr_local {ge : GlobalEnv} {locals : Env} {memory : Mem}
    {name : Ident} {block : Block} {type : Ty}
    (hlocal : locals.get name = some (block, type)) (direction : IncrOrDecr) :
    ExpressionReduction ge locals memory (.Epostincr direction (.Evar name type) type)
      (.Epostincr direction (.Eloc block Integers.Ptrofs.zero .Full type) type) memory := by
  have hl : Lred ge.expressionEnv locals (.Evar name type) memory
      (.Eloc block Integers.Ptrofs.zero .Full type) memory :=
    .var_local _ _ _ _ hlocal
  have hi : ImmSafe ge locals .LV (.Evar name type) memory :=
    .lred _ id _ _ _ _ hl (.top _)
  constructor
  · intro function cont
    exact .lred (fun expr => .Epostincr direction expr type) _ _ _ _ _ _ _ hl
      (.postincr _ id _ _ (.top _))
  · intro function cont trace next hmachine
    generalize hexpr : Expr.Epostincr direction (.Evar name type) type = whole at hmachine
    cases hmachine with
    | lred context _ arg _ _ _ reduced last hred hcontext =>
        rcases hcontext.postincr_cases hexpr with ⟨hk, _, _⟩ | ⟨inner, hi, rfl, he⟩
        · cases hk
        · obtain ⟨_, rfl, rfl⟩ := hi.variable_cases he
          cases hred with
          | var_local _ _ _ actual ha =>
              have heq := Option.some.inj (ha.symm.trans hlocal)
              have hb := Prod.mk.inj heq |>.1
              subst actual
              exact ⟨rfl, rfl⟩
          | var_global _ _ _ _ hn _ => simp [hlocal] at hn
    | rred context _ arg _ _ _ trace reduced last hred hcontext =>
        rcases hcontext.postincr_cases hexpr with ⟨_, rfl, rfl⟩ | ⟨inner, hi, _, he⟩
        · cases hred
        · obtain ⟨hk, _, _⟩ := hi.variable_cases he
          cases hk
    | call context _ arg _ _ _ callee args callType hcall hcontext =>
        rcases hcontext.postincr_cases hexpr with ⟨_, rfl, rfl⟩ | ⟨inner, hi, _, he⟩
        · cases hcall
        · obtain ⟨hk, _, _⟩ := hi.variable_cases he
          cases hk
    | stuck context _ arg _ _ _ kind hcontext hunsafe =>
        rcases hcontext.postincr_cases hexpr with ⟨rfl, rfl, rfl⟩ | ⟨inner, hc, _, he⟩
        · apply False.elim
          apply hunsafe
          exact .lred _ (fun expr => .Epostincr direction expr type) _ _ _ _ hl
            (.postincr _ id _ _ (.top _))
        · obtain ⟨rfl, rfl, rfl⟩ := hc.variable_cases he
          exact False.elim (hunsafe hi)

/-- A nonvolatile post-increment reads the old value before expanding to assignment
and comma sequencing. -/
theorem ExpressionReduction.postincr_location {ge : GlobalEnv} {locals : Env} {memory : Mem}
    {block : Block} {offset : Integers.Ptrofs} {type : Ty} {value : Val}
    (direction : IncrOrDecr) (hv : typeIsVolatile type = false)
    (hload : DerefLoc ge.expressionEnv type memory block offset .Full E0 value) :
    ExpressionReduction ge locals memory (.Epostincr direction (.Eloc block offset .Full type)
      type)
      (.Ecomma (.Eassign (.Eloc block offset .Full type)
        (.Ebinop (match direction with | .incr => .Oadd | .decr => .Osub)
          (.Eval value type) (.Eval (.Vint Integers.Int.one) type_int32s)
          (incrDecrType type)) type) (.Eval value type) type) memory := by
  apply ExpressionReduction.head (.postincr _ _ _ _ _) (.postincr _ _ _ _ _ _ _ _ hload)
  intro trace reduced final hred
  cases hred with
  | postincr _ _ _ _ _ _ trace actual hd =>
      obtain ⟨rfl, hactual⟩ := (derefLoc_iff hv).mp hd
      obtain ⟨_, hexpected⟩ := (derefLoc_iff hv).mp hload
      have heq := CC.derefLoc_determ hactual hexpected
      subst actual
      exact ⟨rfl, rfl, rfl⟩

end Quadrature.CSource.C
