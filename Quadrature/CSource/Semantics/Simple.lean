import Quadrature.CSource.Semantics.Memory

/-!
# Simple C expressions

`simple`, `EvalLvalue`, `EvalRvalue` and `EvalList` adapt `simple`,
`eval_simple_lvalue`, `eval_simple_rvalue` and `eval_simple_list` of CompCert's
`cfrontend/Cstrategy.v`. They form the pure phase of the strategy semantics
(vocabulary: see `Quadrature.CSource.Semantics.Strategy`). Variables denote memory
locations and are read with `Evalof`, as there is no C temporary environment.
Calls, assignments and increments have no rule here, since the effect phase
removes them first.
-/

namespace Quadrature.CSource.C

open CC

/-- Whether an expression is free of side effects: constants, locations, variables, `sizeof` and
`alignof`, and nonvolatile reads, dereferences, field accesses, casts and operators built from
such expressions. -/
def simple : Expr → Bool
  | .Eloc .. | .Evar .. | .Eval .. | .Esizeof .. | .Ealignof .. => true
  | .Ederef r _ | .Efield r _ _ | .Eaddrof r _ | .Eunop _ r _ | .Ecast r _ => simple r
  | .Evalof l _ => simple l && !typeIsVolatile (typeof l)
  | .Ebinop _ l r _ => simple l && simple r
  | _ => false

/-- Whether every expression of the list is `simple`. -/
def simplelist : Exprlist → Bool
  | .Enil => true
  | .Econs r rs => simple r && simplelist rs

mutual
/-- `EvalLvalue ge e m a b ofs bf`: the simple expression `a` denotes block `b` at offset `ofs`
with bitfield designation `bf`. Local variables are looked up in `e`, globals in `ge.symbols`
when `e` does not bind them. -/
inductive EvalLvalue (ge : ExpressionEnv) (e : Env) (m : Mem) :
    Expr → Block → Integers.Ptrofs → Bitfield → Prop where
  | loc (b ofs ty bf) : EvalLvalue ge e m (.Eloc b ofs bf ty) b ofs bf
  | var_local (id ty b) :
      e.get id = some (b, ty) →
      EvalLvalue ge e m (.Evar id ty) b Integers.Ptrofs.zero .Full
  | var_global (id ty b) :
      e.get id = none →
      ge.symbols.find_symbol id = some b →
      EvalLvalue ge e m (.Evar id ty) b Integers.Ptrofs.zero .Full
  | deref (r ty b ofs) :
      EvalRvalue ge e m r (.Vptr b ofs) →
      EvalLvalue ge e m (.Ederef r ty) b ofs .Full
  | field_struct (r field ty b ofs id co att delta bf) :
      EvalRvalue ge e m r (.Vptr b ofs) →
      typeof r = .Tstruct id att →
      ge.composites.get id = some co →
      fieldOffset ge.composites field co.co_members = .OK (delta, bf) →
      EvalLvalue ge e m (.Efield r field ty) b
        (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr delta)) bf
  | field_union (r field ty b ofs id co att delta bf) :
      EvalRvalue ge e m r (.Vptr b ofs) →
      typeof r = .Tunion id att →
      unionFieldOffset ge.composites field co.co_members = .OK (delta, bf) →
      ge.composites.get id = some co →
      EvalLvalue ge e m (.Efield r field ty) b
        (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr delta)) bf

/-- `EvalRvalue ge e m a v`: the simple expression `a` has value `v` in environment `e` and
memory `m`. Reads go through `EvalLvalue` and a nonvolatile `DerefLoc`, and operators and casts
use CompCert's `Cop` semantics. -/
inductive EvalRvalue (ge : ExpressionEnv) (e : Env) (m : Mem) : Expr → Val → Prop where
  | value (v ty) : EvalRvalue ge e m (.Eval v ty) v
  | rvalof (b ofs bf l ty v) :
      EvalLvalue ge e m l b ofs bf →
      ty = typeof l →
      typeIsVolatile ty = false →
      DerefLoc ge ty m b ofs bf E0 v →
      EvalRvalue ge e m (.Evalof l ty) v
  | addrof (b ofs l ty) :
      EvalLvalue ge e m l b ofs .Full →
      EvalRvalue ge e m (.Eaddrof l ty) (.Vptr b ofs)
  | unop (op r ty v₁ v) :
      EvalRvalue ge e m r v₁ →
      Cop.semUnaryOperation op v₁ (typeof r) m = some v →
      EvalRvalue ge e m (.Eunop op r ty) v
  | binop (op r₁ r₂ ty v₁ v₂ v) :
      EvalRvalue ge e m r₁ v₁ →
      EvalRvalue ge e m r₂ v₂ →
      Cop.semBinaryOperation ge.composites op v₁ (typeof r₁) v₂ (typeof r₂) m = some v →
      EvalRvalue ge e m (.Ebinop op r₁ r₂ ty) v
  | cast (ty r v₁ v) :
      EvalRvalue ge e m r v₁ →
      Cop.semCast v₁ (typeof r) ty m = some v →
      EvalRvalue ge e m (.Ecast r ty) v
  | sizeof (arg ty) :
      EvalRvalue ge e m (.Esizeof arg ty)
        (Val.Vptrofs (Integers.Ptrofs.repr (CC.sizeof ge.composites arg)))
  | alignof (arg ty) :
      EvalRvalue ge e m (.Ealignof arg ty)
        (Val.Vptrofs (Integers.Ptrofs.repr (CC.alignof ge.composites arg)))
end

/-- `EvalList ge e m args types values`: each argument evaluates and is cast to the corresponding
parameter type, giving the argument values of a call. -/
inductive EvalList (ge : ExpressionEnv) (e : Env) (m : Mem) :
    Exprlist → List Ty → List Val → Prop where
  | nil : EvalList ge e m .Enil [] []
  | cons (r rs ty tys v vs v') :
      EvalRvalue ge e m r v' →
      Cop.semCast v' (typeof r) ty m = some v →
      EvalList ge e m rs tys vs →
      EvalList ge e m (.Econs r rs) (ty :: tys) (v :: vs)

end Quadrature.CSource.C
