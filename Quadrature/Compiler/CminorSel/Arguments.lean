import Quadrature.Compiler.CminorSel.Expressions

/-!
# Switch exits, call targets, and builtin arguments

Relational and executable evaluation of `ExitExpr`, call targets, and `BuiltinArg`,
after `backend/CminorSel.v` at the revision recorded in `Syntax.lean`. `EvalExitExpr`
yields the exit depth of a switch, `EvalExprOrSymbol` the function value of a call
target, and `EvalBuiltinArg` the value of a builtin argument. Switch indices are
unsigned 32-bit integers. Direct calls resolve a symbol and require its presence.
Split-word builtin arguments accept exactly two `BA` expressions, unlike the more
general rule in `common/Events.v`. The evaluators follow these relations exactly.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.CminorSel

open CC

/-- `EvalExitExpr ge sp e m le x d` says the exit expression `x` selects the exit depth `d` under
the let environment `le`. -/
inductive EvalExitExpr (ge : Genv) (stack : Val) (env : Env) (memory : Mem) :
    LetEnv → ExitExpr → Nat → Prop where
  | exit (locals depth) : EvalExitExpr ge stack env memory locals (.XEexit depth) depth
  | jumpTable (locals index table value depth) :
      EvalExpr ge stack env memory locals index (.Vint value) →
      table[(Integers.Int.unsigned value).toNat]? = some depth →
      EvalExitExpr ge stack env memory locals (.XEjumptable index table) depth
  | condition (locals condition yes no result depth) :
      EvalCondExpr ge stack env memory locals condition result →
      EvalExitExpr ge stack env memory locals (if result then yes else no) depth →
      EvalExitExpr ge stack env memory locals (.XEcondition condition yes no) depth
  | letValue (locals value body input depth) :
      EvalExpr ge stack env memory locals value input →
      EvalExitExpr ge stack env memory (input :: locals) body depth →
      EvalExitExpr ge stack env memory locals (.XElet value body) depth

/-- `evalExitExpr ge sp e m le x` computes the exit depth selected by `x`, or fails. -/
def evalExitExpr (ge : Genv) (stack : Val) (env : Env) (memory : Mem) :
    LetEnv → ExitExpr → Option Nat
  | _, .XEexit depth => some depth
  | locals, .XEjumptable index table => do
      let value ← evalExpr ge stack env memory locals index
      match value with
      | .Vint value => table[(Integers.Int.unsigned value).toNat]?
      | _ => none
  | locals, .XEcondition condition yes no => do
      let result ← evalCondExpr ge stack env memory locals condition
      if result then evalExitExpr ge stack env memory locals yes
      else evalExitExpr ge stack env memory locals no
  | locals, .XElet value body => do
      let input ← evalExpr ge stack env memory locals value
      evalExitExpr ge stack env memory (input :: locals) body

/-- `EvalExprOrSymbol ge sp e m le target v` says the call target `target`, an expression or a
global symbol, denotes the function value `v`. -/
inductive EvalExprOrSymbol (ge : Genv) (stack : Val) (env : Env) (memory : Mem) :
    LetEnv → Sum Expr Ident → Val → Prop where
  | expr (locals expr value) :
      EvalExpr ge stack env memory locals expr value →
      EvalExprOrSymbol ge stack env memory locals (.inl expr) value
  | symbol (locals name block) :
      CC.Genv.findSymbol ge name = some block →
      EvalExprOrSymbol ge stack env memory locals (.inr name) (.Vptr block Integers.Ptrofs.zero)

/-- `evalExprOrSymbol ge sp e m le target` computes the function value of a call target, or fails
when the symbol is absent. -/
def evalExprOrSymbol (ge : Genv) (stack : Val) (env : Env) (memory : Mem)
    (locals : LetEnv) : Sum Expr Ident → Option Val
  | .inl expr => evalExpr ge stack env memory locals expr
  | .inr name => do
      let block ← CC.Genv.findSymbol ge name
      pure (.Vptr block Integers.Ptrofs.zero)

/-- `EvalBuiltinArg ge sp e m arg v` says the builtin argument `arg` evaluates to `v`. Expressions
inside arguments are evaluated with an empty let environment. -/
inductive EvalBuiltinArg (ge : Genv) (stack : Val) (env : Env) (memory : Mem) :
    BuiltinArg → Val → Prop where
  | expr (expr value) :
      EvalExpr ge stack env memory [] expr value →
      EvalBuiltinArg ge stack env memory (.BA expr) value
  | int (value) : EvalBuiltinArg ge stack env memory (.BA_int value) (.Vint value)
  | long (value) : EvalBuiltinArg ge stack env memory (.BA_long value) (.Vlong value)
  | float (value) : EvalBuiltinArg ge stack env memory (.BA_float value) (.Vfloat value)
  | single (value) : EvalBuiltinArg ge stack env memory (.BA_single value) (.Vsingle value)
  | loadStack (chunk offset value) :
      Mem.loadv chunk memory (Val.offsetPtr stack offset) = some value →
      EvalBuiltinArg ge stack env memory (.BA_loadstack chunk offset) value
  | addrStack (offset) :
      EvalBuiltinArg ge stack env memory (.BA_addrstack offset) (Val.offsetPtr stack offset)
  | loadGlobal (chunk name offset value) :
      Mem.loadv chunk memory (CC.Genv.symbolAddress ge name offset) = some value →
      EvalBuiltinArg ge stack env memory (.BA_loadglobal chunk name offset) value
  | addrGlobal (name offset) :
      EvalBuiltinArg ge stack env memory (.BA_addrglobal name offset)
        (CC.Genv.symbolAddress ge name offset)
  | splitLong (hi lo high low) :
      EvalExpr ge stack env memory [] hi high →
      EvalExpr ge stack env memory [] lo low →
      EvalBuiltinArg ge stack env memory (.BA_splitlong (.BA hi) (.BA lo))
        (Val.longofwords high low)
  | addPtr (left right a b) :
      EvalBuiltinArg ge stack env memory left a →
      EvalBuiltinArg ge stack env memory right b →
      EvalBuiltinArg ge stack env memory (.BA_addptr left right)
        (if Archi.ptr64 then Val.addl a b else Val.add a b)

/-- `EvalBuiltinArgs ge sp e m args vs` evaluates the builtin arguments pointwise to `vs`. -/
abbrev EvalBuiltinArgs (ge : Genv) (stack : Val) (env : Env) (memory : Mem) :=
  List.Forall₂ (EvalBuiltinArg ge stack env memory)

/-- `evalBuiltinArg ge sp e m arg` computes the value of one builtin argument, or fails. -/
def evalBuiltinArg (ge : Genv) (stack : Val) (env : Env) (memory : Mem) :
    BuiltinArg → Option Val
  | .BA expr => evalExpr ge stack env memory [] expr
  | .BA_int value => some (.Vint value)
  | .BA_long value => some (.Vlong value)
  | .BA_float value => some (.Vfloat value)
  | .BA_single value => some (.Vsingle value)
  | .BA_loadstack chunk offset => Mem.loadv chunk memory (Val.offsetPtr stack offset)
  | .BA_addrstack offset => some (Val.offsetPtr stack offset)
  | .BA_loadglobal chunk name offset =>
      Mem.loadv chunk memory (CC.Genv.symbolAddress ge name offset)
  | .BA_addrglobal name offset => some (CC.Genv.symbolAddress ge name offset)
  | .BA_splitlong (.BA hi) (.BA lo) => do
      let high ← evalExpr ge stack env memory [] hi
      let low ← evalExpr ge stack env memory [] lo
      pure (Val.longofwords high low)
  | .BA_splitlong _ _ => none
  | .BA_addptr left right => do
      let a ← evalBuiltinArg ge stack env memory left
      let b ← evalBuiltinArg ge stack env memory right
      pure (if Archi.ptr64 then Val.addl a b else Val.add a b)

/-- `evalBuiltinArgs ge sp e m args` computes the values of the builtin arguments in order, failing
if any fails. -/
def evalBuiltinArgs (ge : Genv) (stack : Val) (env : Env) (memory : Mem) :
    List BuiltinArg → Option (List Val)
  | [] => some []
  | arg :: args => do
      let value ← evalBuiltinArg ge stack env memory arg
      let values ← evalBuiltinArgs ge stack env memory args
      pure (value :: values)

variable {ge : Genv} {stack : Val} {env : Env} {memory : Mem}

/-- If `EvalExitExpr ge sp e m le x d` holds, then `evalExitExpr ge sp e m le x` returns
`some d`. -/
theorem eval_exit_expr_complete {locals : LetEnv} {expr : ExitExpr} {depth : Nat}
    (h : EvalExitExpr ge stack env memory locals expr depth) :
    evalExitExpr ge stack env memory locals expr = some depth := by
  induction h with
  | exit => rfl
  | jumpTable _ _ _ _ _ hvalue htable =>
      simp [evalExitExpr, eval_expr_complete hvalue, htable]
  | condition _ _ _ _ result _ hcondition _ ih =>
      cases result <;> simpa [evalExitExpr, eval_cond_expr_complete hcondition] using ih
  | letValue _ _ _ _ _ hvalue _ ih =>
      simpa [evalExitExpr, eval_expr_complete hvalue] using ih

/-- If `evalExitExpr ge sp e m le x` returns `some d`, then `EvalExitExpr ge sp e m le x d`
holds. -/
theorem eval_exit_expr_sound {locals : LetEnv} {expr : ExitExpr} {depth : Nat}
    (h : evalExitExpr ge stack env memory locals expr = some depth) :
    EvalExitExpr ge stack env memory locals expr depth := by
  induction expr generalizing locals depth with
  | XEexit value =>
      cases h
      exact .exit _ _
  | XEjumptable index table =>
      simp only [evalExitExpr, bind, Option.bind_eq_some_iff] at h
      obtain ⟨value, hvalue, htable⟩ := h
      cases value <;> try cases htable
      exact .jumpTable _ _ _ _ _ (eval_expr_sound hvalue) htable
  | XEcondition condition yes no ihyes ihno =>
      simp only [evalExitExpr, bind, Option.bind_eq_some_iff] at h
      obtain ⟨result, hcondition, hbranch⟩ := h
      cases result
      · exact .condition _ _ _ _ _ _ (eval_cond_expr_sound hcondition) (ihno hbranch)
      · exact .condition _ _ _ _ _ _ (eval_cond_expr_sound hcondition) (ihyes hbranch)
  | XElet value body ih =>
      simp only [evalExitExpr, bind, Option.bind_eq_some_iff] at h
      obtain ⟨input, hvalue, hbody⟩ := h
      exact .letValue _ _ _ _ _ (eval_expr_sound hvalue) (ih hbody)

/-- If `EvalExprOrSymbol` holds for a call target, then `evalExprOrSymbol` returns that value. -/
theorem eval_expr_or_symbol_complete {locals : LetEnv} {expr : Sum Expr Ident} {value : Val}
    (h : EvalExprOrSymbol ge stack env memory locals expr value) :
    evalExprOrSymbol ge stack env memory locals expr = some value := by
  cases h with
  | expr _ _ hvalue => exact eval_expr_complete hvalue
  | symbol _ _ hsymbol => simp [evalExprOrSymbol, hsymbol]

/-- If `evalExprOrSymbol` returns `some v` for a call target, then `EvalExprOrSymbol` holds. -/
theorem eval_expr_or_symbol_sound {locals : LetEnv} {expr : Sum Expr Ident} {value : Val}
    (h : evalExprOrSymbol ge stack env memory locals expr = some value) :
    EvalExprOrSymbol ge stack env memory locals expr value := by
  cases expr with
  | inl expr => exact .expr _ _ _ (eval_expr_sound h)
  | inr name =>
      simp only [evalExprOrSymbol, bind, Option.bind_eq_some_iff,
        pure, Option.some.injEq] at h
      obtain ⟨block, hblock, rfl⟩ := h
      exact .symbol _ _ _ hblock

/-- If `EvalBuiltinArg ge sp e m arg v` holds, then `evalBuiltinArg ge sp e m arg` returns
`some v`. -/
theorem eval_builtin_arg_complete {arg : BuiltinArg} {value : Val}
    (h : EvalBuiltinArg ge stack env memory arg value) :
    evalBuiltinArg ge stack env memory arg = some value := by
  induction h with
  | expr _ _ hvalue => exact eval_expr_complete hvalue
  | int | long | float | single | addrStack | addrGlobal => rfl
  | loadStack _ _ _ hload | loadGlobal _ _ _ _ hload => exact hload
  | splitLong _ _ _ _ hhi hlo =>
      simp [evalBuiltinArg, eval_expr_complete hhi, eval_expr_complete hlo]
  | addPtr _ _ _ _ _ _ ihleft ihright => simp [evalBuiltinArg, ihleft, ihright]

/-- If `evalBuiltinArg ge sp e m arg` returns `some v`, then `EvalBuiltinArg ge sp e m arg v`
holds. -/
theorem eval_builtin_arg_sound {arg : BuiltinArg} {value : Val}
    (h : evalBuiltinArg ge stack env memory arg = some value) :
    EvalBuiltinArg ge stack env memory arg value := by
  induction arg generalizing value with
  | BA expr => exact .expr _ _ (eval_expr_sound h)
  | BA_int input => cases h; exact .int _
  | BA_long input => cases h; exact .long _
  | BA_float input => cases h; exact .float _
  | BA_single input => cases h; exact .single _
  | BA_loadstack chunk offset => exact .loadStack _ _ _ h
  | BA_addrstack offset => cases h; exact .addrStack _
  | BA_loadglobal chunk name offset => exact .loadGlobal _ _ _ _ h
  | BA_addrglobal name offset => cases h; exact .addrGlobal _ _
  | BA_splitlong hi lo _ _ =>
      cases hi <;> cases lo <;> try cases h
      simp only [evalBuiltinArg, bind, Option.bind_eq_some_iff,
        pure, Option.some.injEq] at h
      obtain ⟨high, hhi, low, hlo, rfl⟩ := h
      exact .splitLong _ _ _ _ (eval_expr_sound hhi) (eval_expr_sound hlo)
  | BA_addptr left right ihleft ihright =>
      simp only [evalBuiltinArg, bind, Option.bind_eq_some_iff,
        pure, Option.some.injEq] at h
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      exact .addPtr _ _ _ _ (ihleft ha) (ihright hb)

/-- If `EvalBuiltinArgs` holds for an argument list, then `evalBuiltinArgs` returns those values. -/
theorem eval_builtin_args_complete {args : List BuiltinArg} {values : List Val}
    (h : EvalBuiltinArgs ge stack env memory args values) :
    evalBuiltinArgs ge stack env memory args = some values := by
  induction h with
  | nil => rfl
  | cons hhead _ ih => simp [evalBuiltinArgs, eval_builtin_arg_complete hhead, ih]

/-- If `evalBuiltinArgs` returns `some vs` for an argument list, then `EvalBuiltinArgs` holds. -/
theorem eval_builtin_args_sound {args : List BuiltinArg} {values : List Val}
    (h : evalBuiltinArgs ge stack env memory args = some values) :
    EvalBuiltinArgs ge stack env memory args values := by
  induction args generalizing values with
  | nil => cases h; exact .nil
  | cons arg args ih =>
      simp only [evalBuiltinArgs, bind, Option.bind_eq_some_iff,
        pure, Option.some.injEq] at h
      obtain ⟨value, hvalue, rest, hrest, rfl⟩ := h
      exact .cons (eval_builtin_arg_sound hvalue) (ih hrest)

/-- `EvalExitExpr` holds exactly when `evalExitExpr` returns that depth. -/
theorem eval_exit_expr_iff {locals : LetEnv} {expr : ExitExpr} {depth : Nat} :
    EvalExitExpr ge stack env memory locals expr depth ↔
      evalExitExpr ge stack env memory locals expr = some depth :=
  ⟨eval_exit_expr_complete, eval_exit_expr_sound⟩

/-- `EvalExprOrSymbol` holds exactly when `evalExprOrSymbol` returns that value. -/
theorem eval_expr_or_symbol_iff {locals : LetEnv} {expr : Sum Expr Ident} {value : Val} :
    EvalExprOrSymbol ge stack env memory locals expr value ↔
      evalExprOrSymbol ge stack env memory locals expr = some value :=
  ⟨eval_expr_or_symbol_complete, eval_expr_or_symbol_sound⟩

/-- `EvalBuiltinArg` holds exactly when `evalBuiltinArg` returns that value. -/
theorem eval_builtin_arg_iff {arg : BuiltinArg} {value : Val} :
    EvalBuiltinArg ge stack env memory arg value ↔
      evalBuiltinArg ge stack env memory arg = some value :=
  ⟨eval_builtin_arg_complete, eval_builtin_arg_sound⟩

/-- `EvalBuiltinArgs` holds exactly when `evalBuiltinArgs` returns those values. -/
theorem eval_builtin_args_iff {args : List BuiltinArg} {values : List Val} :
    EvalBuiltinArgs ge stack env memory args values ↔
      evalBuiltinArgs ge stack env memory args = some values :=
  ⟨eval_builtin_args_complete, eval_builtin_args_sound⟩

end Quadrature.CminorSel
