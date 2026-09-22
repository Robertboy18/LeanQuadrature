import Quadrature.CSource.Semantics.Control

/-!
# Variable reads preserved by calls

The expression proofs use `ReadEval.local` for scalar locals and
`ReadEval.global_function` for function symbols. `CallMemory.range_perm`
preserves the permissions needed to free a caller's locals after nested calls.
-/

namespace Quadrature.CSource.C

open CC

/-- Permissions over an old block's range survive a call. -/
theorem CallMemory.range_perm {initial final : Mem} (h : CallMemory initial final)
    {block : Block} {lo hi : Z} {kind : PermKind} {permission : Permission}
    (hb : block < initial.nextblock)
    (hrange : Mem.rangePerm initial block lo hi kind permission = true) :
    Mem.rangePerm final block lo hi kind permission = true := by
  apply Mem.rangePerm_intro
  intro offset hlo hhi
  rw [h.permissions _ _ _ _ hb]
  exact Mem.rangePerm_perm _ _ _ _ _ _ hrange offset hlo hhi

variable [ExternalCalls]

/-- A scalar local retains its loaded value throughout nested calls. -/
theorem ReadEval.local (ge : GlobalEnv) (locals : Env) (base : Mem)
    (name : Ident) (type : Ty) (block : Block) (chunk : Chunk) (value : Val)
    (hmode : accessMode type = .By_value chunk) (hv : typeIsVolatile type = false)
    (hname : locals.get name = some (block, type))
    (hload : Mem.load chunk base block 0 = some value) :
    ReadEval ge locals base .RV (.Evalof (.Evar name type) type) (.value value) :=
  .rvalof _ _ _ _ _ _ (.var_local _ _ _ hname) rfl hv
    (fun _ hmemory => .value _ _ hmode hv (hmemory.load hload))

/-- A global function symbol has a fixed pointer, independently of call allocation order. -/
theorem ReadEval.global_function (ge : GlobalEnv) (locals : Env) (base : Mem)
    (name : Ident) (block : Block) (parameters : List Ty) (result : Ty) (cc : CallConv)
    (hname : locals.get name = none)
    (hsymbol : Genv.findSymbol ge.globals name = some block) :
    ReadEval ge locals base .RV
      (.Evalof (.Evar name (.Tfunction parameters result cc)) (.Tfunction parameters result cc))
      (.value (.Vptr block Integers.Ptrofs.zero)) :=
  .rvalof _ _ _ _ _ _ (.var_global _ _ _ hname hsymbol) rfl rfl
    (fun _ _ => .reference rfl)

end Quadrature.CSource.C
