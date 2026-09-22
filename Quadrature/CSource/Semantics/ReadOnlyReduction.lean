import Quadrature.CSource.Semantics.ReadOnly

/-!
# Reduction preserves read-only expression proofs

`Lred.read_eval` and `Rred.read_eval` preserve the operand values recorded
in `ReadEval`. `Callred.read_eval` retrieves a full C call proof when a call
is ready to execute. Argument conversions are checked against the same
memory as the transition.
-/

namespace Quadrature.CSource.C

open CC

variable [ExternalCalls]

/-- A location reduction preserves its read-only meaning. -/
theorem Lred.read_eval {ge : GlobalEnv} {locals : Env} {base memory final : Mem}
    {expr result : Expr} {value : PureResult}
    (hstep : Lred ge.expressionEnv locals expr memory result final)
    (heval : ReadEval ge locals base .LV expr value) :
    ReadEval ge locals base .LV result value := by
  cases hstep <;> cases heval <;> simp_all [ReadEval.value_iff]
  all_goals exact .location _ _ _ _

/-- A value head reduction is silent, preserves memory, and preserves the read-only value. -/
theorem Rred.read_eval {ge : GlobalEnv} {locals : Env} {base memory final : Mem}
    {expr result : Expr} {trace : Trace} {value : PureResult}
    (hstep : Rred ge expr memory trace result final)
    (heval : ReadEval ge locals base .RV expr value) (hframe : CallMemory base memory) :
    trace = E0 ∧ final = memory ∧ ReadEval ge locals base .RV result value := by
  cases hstep with
  | rvalof block offset bitfield type memory trace result hread =>
      cases heval with
      | rvalof _ _ _ _ _ value hloc _ hv hd =>
          cases hloc
          obtain ⟨htrace, hread'⟩ := (derefLoc_iff hv).mp hread
          subst trace
          have heq := CC.derefLoc_determ hread' ((derefLoc_iff hv).mp (hd _ hframe)).2
          cases heq
          exact ⟨rfl, rfl, .value _ _⟩
  | addrof =>
      cases heval with
      | addrof _ _ _ _ hloc =>
          cases hloc
          exact ⟨rfl, rfl, .value _ _⟩
  | unop op arg argType type memory result hstep =>
      cases heval with
      | unop _ _ _ _ _ harg hsem =>
          cases harg
          have heq := Option.some.inj (hstep.symm.trans (hsem _ hframe))
          cases heq
          exact ⟨rfl, rfl, .value _ _⟩
  | binop op left leftType right rightType type memory result hstep =>
      cases heval with
      | binop _ _ _ _ _ _ _ hleft hright hsem =>
          cases hleft
          cases hright
          have heq := Option.some.inj (hstep.symm.trans (hsem _ hframe))
          cases heq
          exact ⟨rfl, rfl, .value _ _⟩
  | cast type arg argType memory result hstep =>
      cases heval with
      | cast _ _ _ _ harg hsem =>
          cases harg
          have heq := Option.some.inj (hstep.symm.trans (hsem _ hframe))
          cases heq
          exact ⟨rfl, rfl, .value _ _⟩
  | seqand_true | seqand_false | seqor_true | seqor_false | condition
  | sizeof | alignof | assign | assignop | postincr | comma | paren | builtin => cases heval

/-- A read-only value head reduction strictly decreases expression work. -/
theorem Rred.read_work_lt {ge : GlobalEnv} {locals : Env} {base memory final : Mem}
    {expr result : Expr} {trace : Trace} {value : PureResult}
    (hstep : Rred ge expr memory trace result final)
    (heval : ReadEval ge locals base .RV expr value) :
    result.work < expr.work := by
  cases hstep <;> cases heval <;> simp [Expr.work]

/-- Once all arguments are values, their conversions agree with the read-only proof. -/
theorem CastArguments.read_values {ge : GlobalEnv} {locals : Env} {base memory : Mem}
    {args : Exprlist} {types : List Ty} {values results : List Val}
    (hargs : CastArguments memory args types values)
    (heval : ReadList ge locals base args types results) (hframe : CallMemory base memory) :
    values = results := by
  induction hargs generalizing results with
  | nil =>
      cases heval
      rfl
  | cons value type rest parameter parameters cast values hcast hrest ih =>
      cases heval with
      | cons _ _ _ _ _ _ _ harg hconvert hargs =>
          cases harg
          have heq := Option.some.inj (hcast.symm.trans (hconvert _ hframe))
          cases heq
          exact congrArg (cast :: ·) (ih hargs)

/-- A call head reduction selects exactly the callee, arguments, and result whose full C
execution is justified by the read-only proof. -/
theorem Callred.read_eval {ge : GlobalEnv} {locals : Env} {base memory : Mem}
    {expr : Expr} {function : FunDef} {args : List Val} {type : Ty} {result : PureResult}
    (hcall : Callred ge expr memory function args type)
    (heval : ReadEval ge locals base .RV expr result) (hframe : CallMemory base memory) :
    typeof expr = type ∧ ∃ value,
      result = .value value ∧ SmallStep.CallCorrect ge memory function args value := by
  cases hcall with
  | call callee calleeType memory argTypes resultType cc args type function values
      hfind hargs ht hc =>
      cases heval with
      | call _ _ _ _ parameters returnType callingConvention calleeFunction castValues value
          hcallee hread hlookup htype hclass hbody =>
          cases hcallee
          have hfunction := Option.some.inj (hfind.symm.trans hlookup)
          cases hfunction
          have hsignature := hc.symm.trans hclass
          cases hsignature
          have hvalues := hargs.read_values hread hframe
          cases hvalues
          exact ⟨rfl, value, rfl, hbody _ hframe⟩

omit [ExternalCalls] in
/-- Returning from a call removes that call's operation and its evaluated operands. -/
theorem Callred.work_lt {ge : GlobalEnv} {memory : Mem} {expr : Expr}
    {function : FunDef} {args : List Val} {type : Ty}
    (hcall : Callred ge expr memory function args type) (value : Val) :
    (Expr.Eval value type).work < expr.work := by
  cases hcall
  simp [Expr.work]

end Quadrature.CSource.C
