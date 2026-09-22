import Quadrature.Compiler.LTL.Syntax

/-!
# LTL builtin arguments

Relational and executable evaluation of `BuiltinArg`, after the generic
`eval_builtin_arg` rules in `common/Events.v`. `EvalBuiltinArg ge sp ls m arg v` says
`arg` evaluates to `v`. Locations are read directly, and split-word arguments
recursively evaluate both subarguments. `eval_builtin_arg_iff` shows the evaluator
agrees with the relation.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.LTL

open CC

variable {F V : Type}

/-- `EvalBuiltinArg ge sp ls m arg v` says the builtin argument `arg` evaluates to `v` with stack
pointer `sp`, location map `ls`, and memory `m`. -/
inductive EvalBuiltinArg (ge : CC.Genv F V) (stack : Val) (env : Locset) (memory : Mem) :
    BuiltinArg → Val → Prop where
  | register (reg) : EvalBuiltinArg ge stack env memory (.BA reg) (env.get reg)
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
      EvalBuiltinArg ge stack env memory hi high →
      EvalBuiltinArg ge stack env memory lo low →
      EvalBuiltinArg ge stack env memory (.BA_splitlong hi lo)
        (Val.longofwords high low)
  | addPtr (left right a b) :
      EvalBuiltinArg ge stack env memory left a →
      EvalBuiltinArg ge stack env memory right b →
      EvalBuiltinArg ge stack env memory (.BA_addptr left right)
        (if Archi.ptr64 then Val.addl a b else Val.add a b)

/-- `EvalBuiltinArgs ge sp ls m args vs` evaluates the builtin arguments pointwise to `vs`. -/
abbrev EvalBuiltinArgs (ge : CC.Genv F V) (stack : Val) (env : Locset) (memory : Mem) :=
  List.Forall₂ (EvalBuiltinArg ge stack env memory)

/-- `evalBuiltinArg ge sp ls m arg` computes the value of one builtin argument, or fails. -/
def evalBuiltinArg (ge : CC.Genv F V) (stack : Val) (env : Locset) (memory : Mem) :
    BuiltinArg → Option Val
  | .BA reg => some (env.get reg)
  | .BA_int value => some (.Vint value)
  | .BA_long value => some (.Vlong value)
  | .BA_float value => some (.Vfloat value)
  | .BA_single value => some (.Vsingle value)
  | .BA_loadstack chunk offset => Mem.loadv chunk memory (Val.offsetPtr stack offset)
  | .BA_addrstack offset => some (Val.offsetPtr stack offset)
  | .BA_loadglobal chunk name offset =>
      Mem.loadv chunk memory (CC.Genv.symbolAddress ge name offset)
  | .BA_addrglobal name offset => some (CC.Genv.symbolAddress ge name offset)
  | .BA_splitlong hi lo => do
      let high ← evalBuiltinArg ge stack env memory hi
      let low ← evalBuiltinArg ge stack env memory lo
      pure (Val.longofwords high low)
  | .BA_addptr left right => do
      let a ← evalBuiltinArg ge stack env memory left
      let b ← evalBuiltinArg ge stack env memory right
      pure (if Archi.ptr64 then Val.addl a b else Val.add a b)

/-- `evalBuiltinArgs ge sp ls m args` computes the values of the builtin arguments in order,
failing if any fails. -/
def evalBuiltinArgs (ge : CC.Genv F V) (stack : Val) (env : Locset) (memory : Mem) :
    List BuiltinArg → Option (List Val)
  | [] => some []
  | arg :: args => do
      let value ← evalBuiltinArg ge stack env memory arg
      let values ← evalBuiltinArgs ge stack env memory args
      pure (value :: values)

variable {ge : CC.Genv F V} {stack : Val} {env : Locset} {memory : Mem}

/-- If `EvalBuiltinArg ge sp ls m arg v` holds, then `evalBuiltinArg ge sp ls m arg` returns
`some v`. -/
theorem eval_builtin_arg_complete {arg : BuiltinArg} {value : Val}
    (h : EvalBuiltinArg ge stack env memory arg value) :
    evalBuiltinArg ge stack env memory arg = some value := by
  induction h with
  | register | int | long | float | single | addrStack | addrGlobal => rfl
  | loadStack _ _ _ hload | loadGlobal _ _ _ _ hload => exact hload
  | splitLong _ _ _ _ _ _ ihhi ihlo => simp [evalBuiltinArg, ihhi, ihlo]
  | addPtr _ _ _ _ _ _ ihleft ihright => simp [evalBuiltinArg, ihleft, ihright]

/-- If `evalBuiltinArg ge sp ls m arg` returns `some v`, then `EvalBuiltinArg ge sp ls m arg v`
holds. -/
theorem eval_builtin_arg_sound {arg : BuiltinArg} {value : Val}
    (h : evalBuiltinArg ge stack env memory arg = some value) :
    EvalBuiltinArg ge stack env memory arg value := by
  induction arg generalizing value with
  | BA reg => cases h; exact .register _
  | BA_int input => cases h; exact .int _
  | BA_long input => cases h; exact .long _
  | BA_float input => cases h; exact .float _
  | BA_single input => cases h; exact .single _
  | BA_loadstack chunk offset => exact .loadStack _ _ _ h
  | BA_addrstack offset => cases h; exact .addrStack _
  | BA_loadglobal chunk name offset => exact .loadGlobal _ _ _ _ h
  | BA_addrglobal name offset => cases h; exact .addrGlobal _ _
  | BA_splitlong hi lo ihhi ihlo =>
      simp only [evalBuiltinArg, bind, Option.bind_eq_some_iff,
        pure, Option.some.injEq] at h
      obtain ⟨high, hhi, low, hlo, rfl⟩ := h
      exact .splitLong _ _ _ _ (ihhi hhi) (ihlo hlo)
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

end Quadrature.LTL
