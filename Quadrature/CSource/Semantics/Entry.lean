import Quadrature.CSource.Semantics.Statements

/-!
# C assignment and function entry

`AssignLoc` and `BindParameters` adapt `assign_loc` and `bind_parameters` of
CompCert's `cfrontend/Csem.v` (revision recorded in `Quadrature.Clight.Source`).
Assignment keeps its trace and result value, including the volatile and
bitfield cases, and copy assignment requires alignment even at size zero.
Variable allocation is CLean's Clight rule, reused unchanged. `FunctionEntry`
groups the premises of `Cstrategy.eval_funcall_internal` that precede the body.
-/

namespace Quadrature.CSource.C

open CC

/-- `AssignLoc ge ty m b ofs bf v trace m' v'`: storing `v` of type `ty` at block `b`, offset
`ofs` (bitfield designation `bf`) takes memory `m` to `m'` with trace `trace` and result value
`v'`. By-value types store a chunk (volatile ones through `VolatileStore`, with a trace), by-copy
types copy `sizeof ty` bytes from the pointer `v`, and bitfields use `StoreBitfield`, whose
result may be truncated. -/
inductive AssignLoc (ge : ExpressionEnv) (ty : Ty) (m : Mem) (b : Block)
    (ofs : Integers.Ptrofs) : Bitfield → Val → Trace → Mem → Val → Prop where
  | value (v chunk m') :
      accessMode ty = .By_value chunk →
      typeIsVolatile ty = false →
      Mem.storev chunk m (.Vptr b ofs) v = some m' →
      AssignLoc ge ty m b ofs .Full v E0 m' v
  | volatile (v chunk trace m') :
      accessMode ty = .By_value chunk →
      typeIsVolatile ty = true →
      VolatileStore ge.symbols chunk m b ofs v trace m' →
      AssignLoc ge ty m b ofs .Full v trace m' v
  | copy (b' ofs' bytes m') :
      accessMode ty = .By_copy →
      alignofBlockcopy ge.composites ty ∣ Integers.Ptrofs.unsigned ofs' →
      alignofBlockcopy ge.composites ty ∣ Integers.Ptrofs.unsigned ofs →
      (b' ≠ b
        ∨ Integers.Ptrofs.unsigned ofs' = Integers.Ptrofs.unsigned ofs
        ∨ Integers.Ptrofs.unsigned ofs' + sizeof ge.composites ty ≤
          Integers.Ptrofs.unsigned ofs
        ∨ Integers.Ptrofs.unsigned ofs + sizeof ge.composites ty ≤
          Integers.Ptrofs.unsigned ofs') →
      Mem.loadbytes m b' (Integers.Ptrofs.unsigned ofs') (sizeof ge.composites ty) =
        some bytes →
      Mem.storebytes m b (Integers.Ptrofs.unsigned ofs) bytes = some m' →
      AssignLoc ge ty m b ofs .Full (.Vptr b' ofs') E0 m' (.Vptr b' ofs')
  | bitfield (sz sg pos width v m' v') :
      Cop.StoreBitfield ty sz sg pos width m (.Vptr b ofs) v m' v' →
      AssignLoc ge ty m b ofs (.Bits sz sg pos width) v E0 m' v'

/-- Allocation of local variables, CLean's Clight rule over the shared memory model. -/
abbrev AllocVariables (ge : ExpressionEnv) := CC.AllocVariables ge.composites

/-- `BindParameters ge locals m params args m'`: each argument of `args` is stored into the block
that `locals` assigns to the corresponding parameter, in declaration order, taking `m` to
`m'`. -/
inductive BindParameters (ge : ExpressionEnv) (locals : Env) :
    Mem → List (Ident × Ty) → List Val → Mem → Prop where
  | nil (m) : BindParameters ge locals m [] [] m
  | cons (m id ty params value values result block m₁ m₂) :
      locals.get id = some (block, ty) →
      AssignLoc ge ty m block Integers.Ptrofs.zero .Full value E0 m₁ result →
      BindParameters ge locals m₁ params values m₂ →
      BindParameters ge locals m ((id, ty) :: params) (value :: values) m₂

/-- `FunctionEntry ge function arguments initial locals entered`: the parameter and local names
of `function` are distinct, allocating them from `initial` produced the environment `locals`,
and binding `arguments` to the parameters produced memory `entered`. Discharged for the concrete
functions in `Quadrature.CSource.Accessors.Entry`, `IntegratorEntry` and `TestfunEntry`. -/
structure FunctionEntry (ge : ExpressionEnv) (function : Function) (arguments : List Val)
    (initial : Mem) (locals : Env) (entered : Mem) : Prop where
  names_unique : (function.fn_params.map Prod.fst ++ function.fn_vars.map Prod.fst).Nodup
  allocated_and_bound : ∃ allocated,
    AllocVariables ge emptyEnv initial (function.fn_params ++ function.fn_vars)
      locals allocated ∧
    BindParameters ge locals allocated function.fn_params arguments entered

end Quadrature.CSource.C
