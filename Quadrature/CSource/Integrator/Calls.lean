import Quadrature.CSource.Integrator.State

/-!
# The integrator's nested source-C calls

Accessor calls are proved from their typed bodies through
`Quadrature.CSource.Accessors.Calls`. The callback is governed by
`SourceCallbackContract`, an explicit hypothesis on the callback alone: silent
terminating calls satisfying `CallMemory`. `weighted_sample_effects` evaluates
the source product with its nested weight, node and callback calls in the
effect phase of the strategy semantics.
-/

namespace Quadrature.CSource.C

open CC Binary64.ClightSource

/-- Reading a local variable `name`, bound in `locals` to `block` with a nonvolatile by-value
type, yields the value loaded from offset 0 of that block. -/
theorem read_local (ge : ExpressionEnv) (locals : Env) (memory : Mem)
    (name : Ident) (type : Ty) (block : Block) (chunk : Chunk) (value : Val)
    (hmode : accessMode type = .By_value chunk) (hvolatile : typeIsVolatile type = false)
    (hname : locals.get name = some (block, type))
    (hload : Mem.load chunk memory block 0 = some value) :
    EvalRvalue ge locals memory (readVar name type) value :=
  .rvalof _ _ _ _ _ _ (.var_local _ _ _ hname) rfl hvolatile
    (.value chunk value hmode hvolatile hload)

/-- Reading a global function name not bound in `locals` yields the pointer to its symbol's
block at offset zero. -/
theorem read_global_function (ge : GlobalEnv) (locals : Env) (memory : Mem)
    (name : Ident) (block : Block) (arguments : List Ty) (result : Ty) (cc : CallConv)
    (hname : locals.get name = none)
    (hsym : Genv.findSymbol ge.globals name = some block) :
    EvalRvalue ge.expressionEnv locals memory
      (readVar name (.Tfunction arguments result cc)) (.Vptr block Integers.Ptrofs.zero) :=
  .rvalof _ _ _ _ _ _ (.var_global _ _ _ hname hsym) rfl rfl (.reference rfl)

/-- `SourceTableFunctions ge`: the two table symbols `gauss_pts` and `gauss_wts` and the two
accessor symbols `gauss_point` and `gauss_weight` resolve to blocks, and the accessor pointers are
bound to the typed accessor bodies `Typed.accessor`. -/
structure SourceTableFunctions (ge : GlobalEnv) where
  nodes : Block
  weights : Block
  point : Block
  weight : Block
  nodes_symbol : Genv.findSymbol ge.globals _gauss_pts = some nodes
  weights_symbol : Genv.findSymbol ge.globals _gauss_wts = some weights
  point_symbol : Genv.findSymbol ge.globals _gauss_point = some point
  weight_symbol : Genv.findSymbol ge.globals _gauss_weight = some weight
  point_function : Genv.findFunct ge.globals (.Vptr point Integers.Ptrofs.zero) =
    some (.Internal (Typed.accessor _gauss_pts))
  weight_function : Genv.findFunct ge.globals (.Vptr weight Integers.Ptrofs.zero) =
    some (.Internal (Typed.accessor _gauss_wts))

variable [ExternalCalls]

/-- A nonvolatile variable read has no effects: the effect phase leaves it unchanged. -/
theorem read_var_effects (ge : GlobalEnv) (locals : Env) (memory : Mem)
    (name : Ident) (type : Ty) (hvolatile : typeIsVolatile type = false) :
    EvalExpr ge locals memory .RV (readVar name type) E0 memory (readVar name type) :=
  .valof _ _ _ _ _ _ _ hvolatile (.var _ _ _ _)

/-- `SourceCallbackContract ge pointer function f`: `pointer` resolves to `function`, which has
type `double (double)`, and calling it on `Vfloat x` from any memory returns `Vfloat (f x)`
silently in a memory satisfying `CallMemory`. The callback may allocate and free its own storage.
Discharged for the original callback by `testfun_callback_contract`. -/
structure SourceCallbackContract (ge : GlobalEnv) (pointer : Val)
    (function : FunDef) (f : Floats.Float → Floats.Float) : Prop where
  function_eq : Genv.findFunct ge.globals pointer = some function
  type_eq : typeOfFundef function = callbackType
  execution : ∀ memory x, ∃ final,
    EvalFuncall ge memory function [.Vfloat x] E0 final (.Vfloat (f x)) ∧
    CallMemory memory final

/-- Under `IntegratorState`, the call `name(i, n)` of an accessor bound to `Typed.accessor table`
evaluates in the effect phase to `Eval (Vfloat value)` and satisfies `CallMemory`, when `table`
resolves to `tableBlock` holding `value` at `8 * tableOffset n i`. -/
theorem accessor_call_effects (ge : GlobalEnv) (frame : IntegratorFrame) (memory : Mem)
    (name table : Ident) (functionBlock tableBlock : Block)
    (callback : Val) (n i : Nat) (accumulator value : Floats.Float)
    (hn : n ≤ 10) (hi : i ≤ 10)
    (state : IntegratorState frame memory callback n i accumulator)
    (hname : frame.locals.get name = none)
    (hnamei : table ≠ _i) (hnamen : table ≠ _npts)
    (hsym : Genv.findSymbol ge.globals name = some functionBlock)
    (hfun : Genv.findFunct ge.globals (.Vptr functionBlock Integers.Ptrofs.zero) =
      some (.Internal (Typed.accessor table)))
    (htable : Genv.findSymbol ge.globals table = some tableBlock)
    (hload : Mem.load .Mfloat64 memory tableBlock
      (8 * Binary64.Clight.tableOffset n i : Nat) = some (.Vfloat value)) :
    ∃ final,
      EvalExpr ge frame.locals memory .RV (accessorCall name)
        E0 final (.Eval (.Vfloat value) tdouble) ∧ CallMemory memory final := by
  obtain ⟨final, hcall, hmemory, _⟩ := accessor_call_memory ge memory table tableBlock n i value
    hn hi hnamei hnamen htable hload
  refine ⟨final, ?_, hmemory⟩
  apply EvalExpr.call (t₁ := E0) (t₂ := E0) (t₃ := E0) (m₁ := memory) (m₂ := memory)
    (vf := .Vptr functionBlock Integers.Ptrofs.zero)
    (types := [tint, tint]) (result := tdouble) (cc := cc_default)
    (fd := .Internal (Typed.accessor table))
  · exact read_var_effects ge frame.locals memory name accessorType rfl
  · exact .cons _ _ _ _ E0 _ _ E0 _ _
      (read_var_effects ge frame.locals memory _i tint rfl)
      (.cons _ _ _ _ E0 _ _ E0 _ _
        (read_var_effects ge frame.locals memory _n tint rfl) (.nil _ _))
  · exact read_global_function ge frame.locals memory name functionBlock
      [tint, tint] tdouble cc_default hname hsym
  · exact .cons _ _ _ _ _ _ _
      (read_local ge.expressionEnv frame.locals memory _i tint frame.index .Mint32
        (.Vint (Integers.Int.repr i)) rfl rfl rfl state.index_load) rfl
      (.cons _ _ _ _ _ _ _
        (read_local ge.expressionEnv frame.locals memory _n tint frame.count .Mint32
          (.Vint (Integers.Int.repr n)) rfl rfl rfl state.count_load) rfl .nil)
  · rfl
  · exact hfun
  · rfl
  · exact hcall

/-- Under `IntegratorState`, `SourceTableFunctions` and `SourceCallbackContract`, with `weight`
and `node` in the table cells for `n` and `i`, the effect phase evaluates `weightedSample` to the
residual product `Eval weight * Eval (f node)` and satisfies `CallMemory`. -/
theorem weighted_sample_effects (ge : GlobalEnv) (frame : IntegratorFrame) (memory : Mem)
    (ctx : SourceTableFunctions ge) (callback : Val) (function : FunDef)
    (f : Floats.Float → Floats.Float) (n i : Nat) (accumulator weight node : Floats.Float)
    (hn : n ≤ 10) (hi : i ≤ 10)
    (state : IntegratorState frame memory callback n i accumulator)
    (contract : SourceCallbackContract ge callback function f)
    (hweight : Mem.load .Mfloat64 memory ctx.weights
      (8 * Binary64.Clight.tableOffset n i : Nat) = some (.Vfloat weight))
    (hnode : Mem.load .Mfloat64 memory ctx.nodes
      (8 * Binary64.Clight.tableOffset n i : Nat) = some (.Vfloat node)) :
    ∃ final,
      EvalExpr ge frame.locals memory .RV weightedSample E0 final
        (.Ebinop .Omul (.Eval (.Vfloat weight) tdouble)
          (.Eval (.Vfloat (f node)) tdouble) tdouble) ∧ CallMemory memory final := by
  obtain ⟨weighted, hwcall, hwmem⟩ := accessor_call_effects ge frame memory
    _gauss_weight _gauss_wts ctx.weight ctx.weights callback n i accumulator weight hn hi
    state rfl (by decide +kernel) (by decide +kernel) ctx.weight_symbol ctx.weight_function
    ctx.weights_symbol hweight
  obtain ⟨pointed, hpcall, hpmem⟩ := accessor_call_effects ge frame weighted
    _gauss_point _gauss_pts ctx.point ctx.nodes callback n i accumulator node hn hi
    (state.after_call hwmem) rfl (by decide +kernel) (by decide +kernel)
    ctx.point_symbol ctx.point_function ctx.nodes_symbol (hwmem.load hnode)
  obtain ⟨final, hcallback, hcmem⟩ := contract.execution pointed node
  refine ⟨final, ?_, (hwmem.trans hpmem).trans hcmem⟩
  apply EvalExpr.binop (t₁ := E0) (t₂ := E0) (m₁ := weighted)
  · exact hwcall
  · apply EvalExpr.call (t₁ := E0) (t₂ := E0) (t₃ := E0)
      (m₁ := weighted) (m₂ := pointed) (vf := callback)
      (types := [tdouble]) (result := tdouble) (cc := cc_default) (fd := function)
    · exact read_var_effects ge frame.locals weighted _f (tptr callbackType) rfl
    · exact .cons _ _ _ _ E0 _ _ E0 _ _ hpcall (.nil _ _)
    · exact read_local ge.expressionEnv frame.locals pointed _f (tptr callbackType)
        frame.callback Mptr callback rfl rfl rfl ((hwmem.trans hpmem).load state.callback_load)
    · exact .cons _ _ _ _ _ _ _ (.value _ _) rfl .nil
    · rfl
    · exact contract.function_eq
    · exact contract.type_eq
    · exact hcallback

end Quadrature.CSource.C
