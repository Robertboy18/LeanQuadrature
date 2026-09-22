import Quadrature.CSource.Semantics.Simple

/-!
# Replacing simple-expression temporaries by C memory reads

`reifyExpr` maps a Clight expression to typed C syntax, making Clight's
implicit reads explicit and turning a temporary reference into a read of the C
variable of the same name. `LocalMatch` relates the Clight temporary
environment to the contents of the C variables. Under that invariant,
`evalRvalue_of_clight` and `evalLvalue_of_clight` turn an evaluation of a
supported Clight expression into an evaluation of its C image with the same
value, in the same memory. This is an expression lemma. The concrete
`LocalMatch` instance for the accessors is built in
`Quadrature.CSource.Accessors.TableExpressions`.
-/

namespace Quadrature.CSource.C

open CC

/-- The typed C image of a Clight expression. With `read = true` the result is a value expression
(reads through `Evalof`), with `read = false` a location expression. -/
def reifyExpr (read : Bool) : CC.Expr → Expr
  | .Econst_int n ty => .Eval (.Vint n) ty
  | .Econst_float n ty => .Eval (.Vfloat n) ty
  | .Econst_single n ty => .Eval (.Vsingle n) ty
  | .Econst_long n ty => .Eval (.Vlong n) ty
  | .Evar id ty | .Etempvar id ty =>
      if read then .Evalof (.Evar id ty) ty else .Evar id ty
  | .Ederef a ty =>
      let loc := Expr.Ederef (reifyExpr true a) ty
      if read then .Evalof loc ty else loc
  | .Efield a field ty =>
      let loc := Expr.Efield (reifyExpr true a) field ty
      if read then .Evalof loc ty else loc
  | .Eaddrof a ty => .Eaddrof (reifyExpr false a) ty
  | .Eunop op a ty => .Eunop op (reifyExpr true a) ty
  | .Ebinop op a b ty => .Ebinop op (reifyExpr true a) (reifyExpr true b) ty
  | .Ecast a ty => .Ecast (reifyExpr true a) ty
  | .Esizeof a ty => .Esizeof a ty
  | .Ealignof a ty => .Ealignof a ty

/-- Reification preserves the type annotation. -/
@[simp]
theorem typeof_reifyExpr (read : Bool) (a : CC.Expr) :
    typeof (reifyExpr read a) = CC.typeof a := by
  cases a <;> cases read <;> rfl

/-- The Clight expressions the refinement covers: every read is nonvolatile, each temporary has
the type recorded in `temps`, and each memory variable is not a name that was moved to a
temporary. -/
def Supported (temps : PTree Ty) : CC.Expr → Prop
  | .Etempvar id ty => temps.get id = some ty ∧ typeIsVolatile ty = false
  | .Evar id ty => temps.get id = none ∧ typeIsVolatile ty = false
  | .Ederef a ty | .Efield a _ ty => Supported temps a ∧ typeIsVolatile ty = false
  | .Eaddrof a _ | .Eunop _ a _ | .Ecast a _ => Supported temps a
  | .Ebinop _ a b _ => Supported temps a ∧ Supported temps b
  | _ => True

/-- Clight moves some C locals into the temporary environment `le`. C keeps them all in memory.
`LocalMatch temps source target le m` says each Clight temporary of type `ty` (per `temps`)
holding `v` in `le` has a C block in `source` of type `ty` containing `v` in `m`. Every other
identifier is bound identically in `source` and in the Clight environment `target`. Established
for the accessors in `Quadrature.CSource.Accessors.TableExpressions`. -/
structure LocalMatch (temps : PTree Ty) (source target : Env) (le : TempEnv) (m : Mem) :
    Prop where
  retained : ∀ id, temps.get id = none → source.get id = target.get id
  moved : ∀ id ty, temps.get id = some ty → ∀ v, le.get id = some v →
    ∃ b, source.get id = some (b, ty) ∧
      CC.DerefLoc ty m b Integers.Ptrofs.zero .Full v

private theorem reifyExpr_read_of_lvalue {ge : CGenv} {e : Env} {le : TempEnv}
    {m : Mem} {a : CC.Expr} {b : Block} {ofs : Integers.Ptrofs} {bf : Bitfield}
    (h : CC.EvalLvalue ge e le m a b ofs bf) :
    reifyExpr true a = .Evalof (reifyExpr false a) (CC.typeof a) := by
  cases h <;> rfl

private theorem nonvolatile_of_lvalue {ge : CGenv} {e : Env} {le : TempEnv}
    {m : Mem} {a : CC.Expr} {b : Block} {ofs : Integers.Ptrofs} {bf : Bitfield}
    {temps : PTree Ty} (h : CC.EvalLvalue ge e le m a b ofs bf)
    (hs : Supported temps a) : typeIsVolatile (CC.typeof a) = false := by
  cases h <;> exact hs.2

mutual
/-- Given `LocalMatch`, a supported Clight expression evaluating to `v` in `target`, `le`, `m` has
a C image `reifyExpr true a` evaluating to `v` in `source` and `m`. -/
theorem evalRvalue_of_clight {ge : CGenv} {source target : Env} {le : TempEnv}
    {m : Mem} {temps : PTree Ty} (hm : LocalMatch temps source target le m)
    {a : CC.Expr} {v : Val} (h : CC.EvalExpr ge target le m a v)
    (hs : Supported temps a) :
    EvalRvalue (.ofClight ge) source m (reifyExpr true a) v := by
  cases h with
  | Econst_int n ty => exact .value _ _
  | Econst_float n ty => exact .value _ _
  | Econst_single n ty => exact .value _ _
  | Econst_long n ty => exact .value _ _
  | Etempvar id ty v hv =>
      obtain ⟨b, hb, hd⟩ := hm.moved id ty hs.1 v hv
      exact .rvalof b _ .Full (.Evar id ty) ty v
        (.var_local id ty b hb) rfl hs.2 (derefLoc_of_clight hs.2 hd)
  | Eaddrof a ty b ofs ha =>
      exact .addrof b ofs _ ty (evalLvalue_of_clight hm ha hs)
  | Eunop op a ty v₁ v ha hop =>
      apply EvalRvalue.unop op _ ty v₁ v (evalRvalue_of_clight hm ha hs)
      simpa only [typeof_reifyExpr] using hop
  | Ebinop op a₁ a₂ ty v₁ v₂ v ha hb hop =>
      apply EvalRvalue.binop op _ _ ty v₁ v₂ v
        (evalRvalue_of_clight hm ha hs.1) (evalRvalue_of_clight hm hb hs.2)
      simpa only [typeof_reifyExpr, ExpressionEnv.ofClight] using hop
  | Ecast a ty v₁ v ha hc =>
      apply EvalRvalue.cast ty _ v₁ v (evalRvalue_of_clight hm ha hs)
      simpa only [typeof_reifyExpr] using hc
  | Esizeof arg ty => exact .sizeof arg ty
  | Ealignof arg ty => exact .alignof arg ty
  | Elvalue a b ofs bf v ha hd =>
      rw [reifyExpr_read_of_lvalue ha]
      exact .rvalof b ofs bf _ _ v (evalLvalue_of_clight hm ha hs)
        (typeof_reifyExpr false a).symm (nonvolatile_of_lvalue ha hs)
        (derefLoc_of_clight (nonvolatile_of_lvalue ha hs) hd)
termination_by (sizeOf a, 1)
decreasing_by all_goals (subst_vars; decreasing_tactic)

/-- Given `LocalMatch`, a supported Clight location expression denoting `b`, `ofs`, `bf` has a C
image `reifyExpr false a` denoting the same block, offset and bitfield in `source`. -/
theorem evalLvalue_of_clight {ge : CGenv} {source target : Env} {le : TempEnv}
    {m : Mem} {temps : PTree Ty} (hm : LocalMatch temps source target le m)
    {a : CC.Expr} {b : Block} {ofs : Integers.Ptrofs} {bf : Bitfield}
    (h : CC.EvalLvalue ge target le m a b ofs bf) (hs : Supported temps a) :
    EvalLvalue (.ofClight ge) source m (reifyExpr false a) b ofs bf := by
  cases h with
  | Evar_local id b ty hb =>
      exact .var_local id ty b ((hm.retained id hs.1).trans hb)
  | Evar_global id b ty hn hb =>
      exact .var_global id ty b ((hm.retained id hs.1).trans hn) hb
  | Ederef a ty b ofs ha =>
      exact .deref _ ty b ofs (evalRvalue_of_clight hm ha hs.1)
  | Efield_struct a field ty b ofs id co att delta bf ha ht hc hf =>
      apply EvalLvalue.field_struct _ field ty b ofs id co att delta bf
        (evalRvalue_of_clight hm ha hs.1)
      · simpa only [typeof_reifyExpr] using ht
      · exact hc
      · exact hf
  | Efield_union a field ty b ofs id co att delta bf ha ht hc hf =>
      apply EvalLvalue.field_union _ field ty b ofs id co att delta bf
        (evalRvalue_of_clight hm ha hs.1)
      · simpa only [typeof_reifyExpr] using ht
      · exact hf
      · exact hc
termination_by (sizeOf a, 0)
decreasing_by all_goals (subst_vars; decreasing_tactic)
end

end Quadrature.CSource.C
