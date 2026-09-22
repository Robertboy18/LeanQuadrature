import Quadrature.CSource.Semantics.ReadOnlyProgress

/-!
# All evaluation orders for expressions with calls

`ReadEval.total` executes the actual C bodies of nested calls and resumes
their enclosing expressions. Different operand orders may allocate local
blocks in different sequences. The returned value agrees in every order,
and `CallMemory` composes their preservation of caller memory.
-/

namespace Quadrature.CSource.C

open CC hiding State Cont Step
open SmallStep

variable [ExternalCalls]

/-- A read-only nonvalue expression has a machine successor. -/
theorem ReadEval.progress {ge : GlobalEnv} {locals : Env} {base memory : Mem}
    {expr : Expr} {value : Val} {function : Function} {cont : Cont}
    (heval : ReadEval ge locals base .RV expr (.value value))
    (hframe : CallMemory base memory) (hnormal : expr ≠ .Eval value (typeof expr)) :
    ∃ trace next, Step ge (.expression function expr cont locals memory) trace next := by
  cases heval.imm_safe hframe with
  | value value type memory =>
      cases heval
      exact False.elim (hnormal rfl)
  | lred _ context arg memory result final hstep hcontext =>
      exact ⟨_, _, .inl (.lred _ _ _ _ _ _ _ _ hstep hcontext)⟩
  | rred _ context arg memory trace result final hstep hcontext =>
      exact ⟨_, _, .inl (.rred _ _ _ _ _ _ _ _ _ hstep hcontext)⟩
  | callred _ context arg memory callee args type hstep hcontext =>
      exact ⟨_, _, .inl (.call _ _ _ _ _ _ _ _ _ hstep hcontext)⟩

/-- Statement control cannot intervene before a read-only expression becomes its value. -/
theorem ReadEval.expression_step {ge : GlobalEnv} {locals : Env} {base memory : Mem}
    {expr : Expr} {value : Val} {function : Function} {cont : Cont}
    {trace : Trace} {next : State}
    (heval : ReadEval ge locals base .RV expr (.value value))
    (hnormal : expr ≠ .Eval value (typeof expr))
    (hstep : Step ge (.expression function expr cont locals memory) trace next) :
    ExprStep ge (.expression function expr cont locals memory) trace next := by
  rcases hstep with hstep | hstep
  · exact hstep
  · obtain ⟨value, type, rfl⟩ := hstep.expression_value
    cases heval
    exact False.elim (hnormal rfl)

/-- Read-only expression steps produce no observable event. -/
theorem ReadEval.step_silent {ge : GlobalEnv} {locals : Env} {base memory : Mem}
    {expr : Expr} {value : Val} {function : Function} {cont : Cont}
    {trace : Trace} {next : State}
    (heval : ReadEval ge locals base .RV expr (.value value))
    (hframe : CallMemory base memory)
    (hstep : ExprStep ge (.expression function expr cont locals memory) trace next) :
    trace = E0 := by
  cases hstep with
  | lred | call | stuck => rfl
  | rred context function arg cont locals memory trace result final hstep hcontext =>
      obtain ⟨operand, harg, _⟩ := heval.in_context hcontext
      exact (hstep.read_eval harg hframe).1

/-- A read-only expression terminates in every permitted C evaluation order with its recorded
value, preserving all memory owned by its caller. -/
theorem ReadEval.total {ge : GlobalEnv} {locals : Env} {base memory : Mem}
    {expr : Expr} {value : Val} (heval : ReadEval ge locals base .RV expr (.value value))
    (hframe : CallMemory base memory) (function : Function) (cont : Cont) :
    Total ge (fun state => ∃ final,
      state = .expression function (.Eval value (typeof expr)) cont locals final ∧
      CallMemory memory final)
      (.expression function expr cont locals memory) := by
  by_cases hnormal : expr = .Eval value (typeof expr)
  · exact .done ⟨memory, congrArg (fun expr =>
      State.expression function expr cont locals memory) hnormal, .refl _⟩
  · refine .step (heval.progress hframe hnormal) ?_ ?_
    · intro trace next hstep
      exact heval.step_silent hframe (heval.expression_step hnormal hstep)
    · intro trace next hmachine
      cases heval.expression_step hnormal hmachine with
      | lred context function arg cont locals memory result final hred hcontext =>
          obtain ⟨operand, harg, hreplace⟩ := heval.in_context hcontext
          have htype := hcontext.typeof_eq hred.typeof_eq
          have hwork := hcontext.work_lt hred.work_lt
          have hresult := hreplace result hred.typeof_eq (hred.read_eval harg)
          cases hred.memory_eq
          exact (hresult.total hframe function cont).mono
            (fun state h => by simpa only [htype] using h)
      | rred context function arg cont locals memory trace result final hred hcontext =>
          obtain ⟨operand, harg, hreplace⟩ := heval.in_context hcontext
          have htype := hcontext.typeof_eq hred.typeof_eq
          have hwork := hcontext.work_lt (hred.read_work_lt harg)
          obtain ⟨rfl, hmemory, hresult⟩ := hred.read_eval harg hframe
          subst final
          have hresult := hreplace result hred.typeof_eq hresult
          exact (hresult.total hframe function cont).mono
            (fun state h => by simpa only [htype] using h)
      | call context function arg cont locals memory callee args type hcall hcontext =>
          obtain ⟨operand, harg, hreplace⟩ := heval.in_context hcontext
          obtain ⟨htype, callValue, rfl, hbody⟩ := hcall.read_eval harg hframe
          have hreplacementType : typeof (.Eval callValue type) = typeof arg := htype.symm
          have houterType := hcontext.typeof_eq hreplacementType
          have hwork := hcontext.work_lt (hcall.work_lt callValue)
          have hresult := hreplace (.Eval callValue type) hreplacementType (.value _ _)
          apply (hbody (.call function locals context type cont) trivial).bind
          rintro state ⟨final, rfl, hmemory⟩
          apply Total.resume
          exact (hresult.total (hframe.trans hmemory) function cont).mono
            (fun state ⟨last, hstate, hlast⟩ =>
              ⟨last, by simpa only [houterType] using hstate, hmemory.trans hlast⟩)
      | stuck context function arg cont locals memory kind hcontext hunsafe =>
          exact False.elim (hunsafe (heval.not_stuck hframe _ _ _ hcontext rfl))
termination_by expr.work

end Quadrature.CSource.C
