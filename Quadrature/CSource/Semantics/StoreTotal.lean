import Quadrature.CSource.Semantics.StoreExpression

/-!
# Total correctness of scalar stores

`StoreExpr.total` permits every operand and argument order, executes nested
calls, and performs the final store. Its postcondition records the memory
immediately before the store, so existing load and permission lemmas can
establish the next loop invariant.
-/

namespace Quadrature.CSource.C

open CC hiding State Cont Step
open SmallStep

variable [ExternalCalls]

/-- A pending store can take a machine step. -/
theorem StoreExpr.progress {ge : GlobalEnv} {locals : Env} {base memory : Mem}
    {block : Block} {offset : Integers.Ptrofs} {type : Ty} {value : Val}
    {chunk : Chunk} {expr : Expr} {function : Function} {cont : Cont}
    (heval : StoreExpr ge locals base block offset type value expr)
    (hframe : CallMemory base memory)
    (hmode : accessMode type = .By_value chunk) (hv : typeIsVolatile type = false)
    (hstore : ∃ final, Mem.storev chunk memory (.Vptr block offset) value = some final) :
    ∃ trace next, Step ge (.expression function expr cont locals memory) trace next := by
  cases heval.imm_safe hframe hmode hv hstore with
  | value => cases heval
  | lred _ context arg memory result final hstep hcontext =>
      exact ⟨_, _, .inl (.lred _ _ _ _ _ _ _ _ hstep hcontext)⟩
  | rred _ context arg memory trace result final hstep hcontext =>
      exact ⟨_, _, .inl (.rred _ _ _ _ _ _ _ _ _ hstep hcontext)⟩
  | callred _ context arg memory callee args type hstep hcontext =>
      exact ⟨_, _, .inl (.call _ _ _ _ _ _ _ _ _ hstep hcontext)⟩

/-- Statement control cannot consume a pending store. -/
theorem StoreExpr.expression_step {ge : GlobalEnv} {locals : Env} {base memory : Mem}
    {block : Block} {offset : Integers.Ptrofs} {type : Ty} {value : Val}
    {expr : Expr} {function : Function} {cont : Cont} {trace : Trace} {next : State}
    (heval : StoreExpr ge locals base block offset type value expr)
    (hstep : Step ge (.expression function expr cont locals memory) trace next) :
    ExprStep ge (.expression function expr cont locals memory) trace next := by
  rcases hstep with hstep | hstep
  · exact hstep
  · obtain ⟨value, type, rfl⟩ := hstep.expression_value
    cases heval

/-- A pending nonvolatile scalar store has no observable expression-step trace. -/
theorem StoreExpr.step_silent {ge : GlobalEnv} {locals : Env} {base memory : Mem}
    {block : Block} {offset : Integers.Ptrofs} {type : Ty} {value : Val}
    {chunk : Chunk} {expr : Expr} {function : Function} {cont : Cont}
    {trace : Trace} {next : State}
    (heval : StoreExpr ge locals base block offset type value expr)
    (hframe : CallMemory base memory)
    (hmode : accessMode type = .By_value chunk) (hv : typeIsVolatile type = false)
    (hstep : ExprStep ge (.expression function expr cont locals memory) trace next) :
    trace = E0 := by
  cases hstep with
  | lred | call | stuck => rfl
  | rred context function arg cont locals memory trace result final hred hcontext =>
      rcases heval.in_context hcontext with ⟨_, rfl⟩ | ⟨operand, harg, _⟩
      · exact (heval.head_step hframe hmode hv hred).1
      · exact (hred.read_eval harg hframe).1

/-- Every evaluation order reaches the specified scalar store after finitely many silent
steps. All preceding calls preserve the initial memory. -/
theorem StoreExpr.total {ge : GlobalEnv} {locals : Env} {base memory : Mem}
    {block : Block} {offset : Integers.Ptrofs} {type : Ty} {value : Val}
    {chunk : Chunk} {expr : Expr}
    (heval : StoreExpr ge locals base block offset type value expr)
    (hframe : CallMemory base memory)
    (hmode : accessMode type = .By_value chunk) (hv : typeIsVolatile type = false)
    (hstore : ∀ memory, CallMemory base memory →
      ∃ final, Mem.storev chunk memory (.Vptr block offset) value = some final)
    (function : Function) (cont : Cont) :
    Total ge (fun state => ∃ before final,
      CallMemory memory before ∧
      Mem.storev chunk before (.Vptr block offset) value = some final ∧
      state = .expression function (.Eval value type) cont locals final)
      (.expression function expr cont locals memory) := by
  refine .step (heval.progress hframe hmode hv (hstore _ hframe)) ?_ ?_
  · intro trace next hstep
    exact heval.step_silent hframe hmode hv (heval.expression_step hstep)
  · intro trace next hmachine
    cases heval.expression_step hmachine with
    | lred context function arg cont locals memory result final hred hcontext =>
        rcases heval.in_context hcontext with ⟨heq, _⟩ | ⟨operand, harg, hreplace⟩
        · cases heq
        · have hwork := hcontext.work_lt hred.work_lt
          have hresult := hreplace result hred.typeof_eq (hred.read_eval harg)
          cases hred.memory_eq
          exact hresult.total hframe hmode hv hstore function cont
    | rred context function arg cont locals memory trace result final hred hcontext =>
        rcases heval.in_context hcontext with ⟨_, rfl⟩ | ⟨operand, harg, hreplace⟩
        · obtain ⟨rfl, hdone | ⟨hmemory, hresult, hwork⟩⟩ :=
            heval.head_step hframe hmode hv hred
          · obtain ⟨rfl, hwrite⟩ := hdone
            exact .done ⟨memory, final, .refl _, hwrite, rfl⟩
          · subst final
            exact hresult.total hframe hmode hv hstore function cont
        · have hwork := hcontext.work_lt (hred.read_work_lt harg)
          obtain ⟨rfl, hmemory, hresult⟩ := hred.read_eval harg hframe
          subst final
          exact (hreplace result hred.typeof_eq hresult).total
            hframe hmode hv hstore function cont
    | call context function arg cont locals memory callee args callType hcall hcontext =>
        rcases heval.in_context hcontext with ⟨_, rfl⟩ | ⟨operand, harg, hreplace⟩
        · cases hcall
          cases heval
        · obtain ⟨htype, callValue, rfl, hbody⟩ := hcall.read_eval harg hframe
          have hwork := hcontext.work_lt (hcall.work_lt callValue)
          have hresult := hreplace (.Eval callValue callType) htype.symm (.value _ _)
          apply (hbody (.call function locals context callType cont) trivial).bind
          rintro state ⟨final, rfl, hmemory⟩
          apply Total.resume
          exact (hresult.total (hframe.trans hmemory) hmode hv hstore function cont).mono
            (fun state ⟨before, last, hbefore, hwrite, hstate⟩ =>
              ⟨before, last, hmemory.trans hbefore, hwrite, hstate⟩)
    | stuck context function arg cont locals memory kind hcontext hunsafe =>
        exact False.elim (hunsafe
          (heval.not_stuck hframe hmode hv (hstore _ hframe) _ _ _ hcontext rfl))
termination_by expr.work

end Quadrature.CSource.C
