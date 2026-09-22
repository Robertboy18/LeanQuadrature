import Quadrature.Compiler.Mach.State

/-!
# Mach builtin arguments

Builtin-argument evaluation for Mach, after the generic rules of `common/Events.v`. Read
`EvalBuiltinArg` first: machine registers are read directly, and split-word arguments
evaluate both halves. `eval_builtin_args_iff` shows the executable evaluator sound and
complete for the relation. The second half does the same for external-call arguments
under the ELF64 convention.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Mach

open CC

variable {F V : Type}

/-- The relational evaluation of one builtin argument from registers, the stack, global
addresses, and memory. -/
inductive EvalBuiltinArg (ge : CC.Genv F V) (stack : Val) (env : Regset) (memory : Mem) :
    BuiltinArg → Val → Prop where
  | register (reg) : EvalBuiltinArg ge stack env memory (.BA reg) (env reg)
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

/-- Pointwise evaluation of a list of builtin arguments. -/
abbrev EvalBuiltinArgs (ge : CC.Genv F V) (stack : Val) (env : Regset) (memory : Mem) :=
  List.Forall₂ (EvalBuiltinArg ge stack env memory)

/-- The executable evaluation of one builtin argument, `none` when a load fails. -/
def evalBuiltinArg (ge : CC.Genv F V) (stack : Val) (env : Regset) (memory : Mem) :
    BuiltinArg → Option Val
  | .BA reg => some (env reg)
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

/-- The executable evaluation of a list of builtin arguments, `none` when any load fails. -/
def evalBuiltinArgs (ge : CC.Genv F V) (stack : Val) (env : Regset) (memory : Mem) :
    List BuiltinArg → Option (List Val)
  | [] => some []
  | arg :: args => do
      let value ← evalBuiltinArg ge stack env memory arg
      let values ← evalBuiltinArgs ge stack env memory args
      pure (value :: values)

variable {ge : CC.Genv F V} {stack : Val} {env : Regset} {memory : Mem}

/-- Every relational evaluation `h` is computed by `evalBuiltinArg`. -/
theorem eval_builtin_arg_complete {arg : BuiltinArg} {value : Val}
    (h : EvalBuiltinArg ge stack env memory arg value) :
    evalBuiltinArg ge stack env memory arg = some value := by
  induction h with
  | register | int | long | float | single | addrStack | addrGlobal => rfl
  | loadStack _ _ _ hload | loadGlobal _ _ _ _ hload => exact hload
  | splitLong _ _ _ _ _ _ ihhi ihlo => simp [evalBuiltinArg, ihhi, ihlo]
  | addPtr _ _ _ _ _ _ ihleft ihright => simp [evalBuiltinArg, ihleft, ihright]

/-- Every value computed by `evalBuiltinArg` satisfies `EvalBuiltinArg`. -/
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

/-- Every relational evaluation `h` of an argument list is computed by `evalBuiltinArgs`. -/
theorem eval_builtin_args_complete {args : List BuiltinArg} {values : List Val}
    (h : EvalBuiltinArgs ge stack env memory args values) :
    evalBuiltinArgs ge stack env memory args = some values := by
  induction h with
  | nil => rfl
  | cons hhead _ ih => simp [evalBuiltinArgs, eval_builtin_arg_complete hhead, ih]

/-- Every list computed by `evalBuiltinArgs` satisfies `EvalBuiltinArgs`. -/
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

/-- The relation and the evaluator agree on single arguments. -/
theorem eval_builtin_arg_iff {arg : BuiltinArg} {value : Val} :
    EvalBuiltinArg ge stack env memory arg value ↔
      evalBuiltinArg ge stack env memory arg = some value :=
  ⟨eval_builtin_arg_complete, eval_builtin_arg_sound⟩

/-- The relation and the evaluator agree on argument lists. -/
theorem eval_builtin_args_iff {args : List BuiltinArg} {values : List Val} :
    EvalBuiltinArgs ge stack env memory args values ↔
      evalBuiltinArgs ge stack env memory args = some values :=
  ⟨eval_builtin_args_complete, eval_builtin_args_sound⟩

/-!
ELF64 arguments each occupy one register or one outgoing stack location.
`fe_ofs_arg` is zero for this ABI. Abstract outgoing offsets are in four-byte
units, so external argument loads multiply them by four.
-/

/-- One argument of an external call: a register, or an outgoing stack slot loaded at four
times its abstract offset. -/
inductive ExternalArg (registers : Regset) (memory : Mem) (stack : Val) :
    LTL.Location → Val → Prop where
  | register (reg) : ExternalArg registers memory stack (.R reg) (registers reg)
  | stack (offset type value) :
      loadStack memory stack type (Integers.Ptrofs.repr (4 * offset)) = some value →
      ExternalArg registers memory stack (.S .Outgoing offset type) value

/-- The arguments of an external call, one per location of the signature's convention. -/
abbrev ExternalArgs (registers : Regset) (memory : Mem) (stack : Val)
    (signature : Signature) :=
  List.Forall₂ (ExternalArg registers memory stack) (locArguments signature)

/-- Reads one external-call argument, `none` for local or incoming slots. -/
def externalArg (registers : Regset) (memory : Mem) (stack : Val) :
    LTL.Location → Option Val
  | .R reg => some (registers reg)
  | .S .Outgoing offset type =>
      loadStack memory stack type (Integers.Ptrofs.repr (4 * offset))
  | .S .Local _ _ | .S .Incoming _ _ => none

/-- Reads the arguments at a list of locations, `none` when any read fails. -/
def externalArgList (registers : Regset) (memory : Mem) (stack : Val) :
    List LTL.Location → Option (List Val)
  | [] => some []
  | arg :: args => do
      let value ← externalArg registers memory stack arg
      let values ← externalArgList registers memory stack args
      pure (value :: values)

/-- Reads the arguments of an external call with the given signature. -/
def externalArgs (registers : Regset) (memory : Mem) (stack : Val)
    (signature : Signature) : Option (List Val) :=
  externalArgList registers memory stack (locArguments signature)

/-- Every relational argument `h` is read by `externalArg`. -/
theorem external_arg_complete {registers : Regset} {location : LTL.Location} {value : Val}
    (h : ExternalArg registers memory stack location value) :
    externalArg registers memory stack location = some value := by
  cases h with
  | register => rfl
  | stack _ _ _ hload => exact hload

/-- Every value read by `externalArg` satisfies `ExternalArg`. -/
theorem external_arg_sound {registers : Regset} {location : LTL.Location} {value : Val}
    (h : externalArg registers memory stack location = some value) :
    ExternalArg registers memory stack location value := by
  cases location with
  | R register => cases h; exact .register _
  | S slot offset type =>
      cases slot with
      | Local | Incoming => cases h
      | Outgoing => exact .stack _ _ _ h

/-- Every relational argument list `h` is read by `externalArgList`. -/
theorem external_arg_list_complete {registers : Regset} {locations : List LTL.Location}
    {values : List Val} (h : List.Forall₂ (ExternalArg registers memory stack) locations values) :
    externalArgList registers memory stack locations = some values := by
  induction h with
  | nil => rfl
  | cons hhead _ ih => simp [externalArgList, external_arg_complete hhead, ih]

/-- Every list read by `externalArgList` satisfies the pointwise `ExternalArg` relation. -/
theorem external_arg_list_sound {registers : Regset} {locations : List LTL.Location}
    {values : List Val} (h : externalArgList registers memory stack locations = some values) :
    List.Forall₂ (ExternalArg registers memory stack) locations values := by
  induction locations generalizing values with
  | nil => cases h; exact .nil
  | cons arg args ih =>
      simp only [externalArgList, bind, Option.bind_eq_some_iff,
        pure, Option.some.injEq] at h
      obtain ⟨value, hvalue, rest, hrest, rfl⟩ := h
      exact .cons (external_arg_sound hvalue) (ih hrest)

/-- The relation and the reader agree on the arguments of a signature. -/
theorem external_args_iff {registers : Regset} {signature : Signature} {values : List Val} :
    ExternalArgs registers memory stack signature values ↔
      externalArgs registers memory stack signature = some values :=
  ⟨external_arg_list_complete, external_arg_list_sound⟩

end Quadrature.Mach
