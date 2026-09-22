import Quadrature.Compiler.CminorSel.Syntax

/-!
# Operations selected by the x86-64 backend

Evaluation of `Operation`, `Addressing`, and `Condition`, after `x86/Op.v` at the
revision recorded in `Syntax.lean`. `evalOperation ge sp op vs` computes the result of
`op` on the argument values `vs`, or fails. `Olea` uses 32-bit arithmetic even on this
64-bit target, and `Oleal` and memory addressing use 64-bit arithmetic. Global-based
addressing cases that the upstream 64-bit evaluator rejects are rejected here too.

`Oshrximm` is signed division by a power of two, rounding toward zero. It differs from
an arithmetic right shift on negative odd inputs. Amounts of at least 31 fail, as in
`Val.shrx`.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.CminorSel

open CC

variable {F V : Type}

/-- `evalCondition c vs` evaluates the comparison `c` on the arguments `vs`, failing on undefined
operands or the wrong number of arguments. -/
def evalCondition (condition : Condition) (values : List Val) : Option Bool :=
  match condition, values with
  | .Ccomp comparison, [left, right] => Val.cmp_bool comparison left right
  | .Ccompimm comparison value, [left] => Val.cmp_bool comparison left (.Vint value)
  | _, _ => none

/-- `evalAddressing32 ge sp a vs` computes the address denoted by `a` on `vs` with 32-bit
arithmetic, after `eval_addressing32`. Global and stack cases fail when `Archi.ptr64`. -/
def evalAddressing32 (ge : CC.Genv F V) (stack : Val) (address : Addressing)
    (values : List Val) : Option Val :=
  match address, values with
  | .Aindexed offset, [value] => some (Val.add value (.Vint (Integers.Int.repr offset)))
  | .Aindexed2 offset, [left, right] =>
      some (Val.add (Val.add left right) (.Vint (Integers.Int.repr offset)))
  | .Ascaled scale offset, [value] =>
      some (Val.add (Val.mul value (.Vint (Integers.Int.repr scale)))
        (.Vint (Integers.Int.repr offset)))
  | .Aindexed2scaled scale offset, [left, right] =>
      some (Val.add left (Val.add (Val.mul right (.Vint (Integers.Int.repr scale)))
        (.Vint (Integers.Int.repr offset))))
  | .Aglobal symbol offset, [] =>
      if Archi.ptr64 then none else some (CC.Genv.symbolAddress ge symbol offset)
  | .Abased symbol offset, [value] =>
      if Archi.ptr64 then none else some (Val.add (CC.Genv.symbolAddress ge symbol offset) value)
  | .Abasedscaled scale symbol offset, [value] =>
      if Archi.ptr64 then none else
        some (Val.add (CC.Genv.symbolAddress ge symbol offset)
          (Val.mul value (.Vint (Integers.Int.repr scale))))
  | .Ainstack offset, [] =>
      if Archi.ptr64 then none else some (Val.offsetPtr stack offset)
  | _, _ => none

/-- `evalAddressing64 ge sp a vs` computes the address denoted by `a` on `vs` with 64-bit
arithmetic, after `eval_addressing64`. Based global modes are rejected. -/
def evalAddressing64 (ge : CC.Genv F V) (stack : Val) (address : Addressing)
    (values : List Val) : Option Val :=
  match address, values with
  | .Aindexed offset, [value] => some (Val.addl value (.Vlong (Integers.Int64.repr offset)))
  | .Aindexed2 offset, [left, right] =>
      some (Val.addl (Val.addl left right) (.Vlong (Integers.Int64.repr offset)))
  | .Ascaled scale offset, [value] =>
      some (Val.addl (Val.mull value (.Vlong (Integers.Int64.repr scale)))
        (.Vlong (Integers.Int64.repr offset)))
  | .Aindexed2scaled scale offset, [left, right] =>
      some (Val.addl left (Val.addl (Val.mull right (.Vlong (Integers.Int64.repr scale)))
        (.Vlong (Integers.Int64.repr offset))))
  | .Aglobal symbol offset, [] =>
      if Archi.ptr64 then some (CC.Genv.symbolAddress ge symbol offset) else none
  | .Ainstack offset, [] =>
      if Archi.ptr64 then some (Val.offsetPtr stack offset) else none
  | _, _ => none

/-- `evalAddressing` selects the 64-bit or the 32-bit evaluator according to `Archi.ptr64`. -/
def evalAddressing (ge : CC.Genv F V) (stack : Val) (address : Addressing)
    (values : List Val) : Option Val :=
  if Archi.ptr64 then evalAddressing64 ge stack address values
  else evalAddressing32 ge stack address values

/-- `shiftRightTowardZero v k` divides the 32-bit integer `v` by `2 ^ k` rounding toward zero,
failing unless `k < 31`. -/
def shiftRightTowardZero (value : Val) (amount : Integers.Int) : Option Val :=
  match value with
  | .Vint value =>
      if Integers.Int.ltu amount (Integers.Int.repr 31) then
        some (.Vint (Integers.Int.divs value (Integers.Int.shl Integers.Int.one amount)))
      else none
  | _ => none

/-- `evalOperation ge sp op vs` computes `op` on `vs`, failing on the wrong number of arguments,
division by zero, or an out-of-range shift. -/
def evalOperation (ge : CC.Genv F V) (stack : Val) (operation : Operation)
    (values : List Val) : Option Val :=
  match operation, values with
  | .Ointconst value, [] => some (.Vint value)
  | .Ofloatconst value, [] => some (.Vfloat value)
  | .Omul, [left, right] => some (Val.mul left right)
  | .Odiv, [left, right] => Val.divs left right
  | .Omod, [left, right] => Val.mods left right
  | .Oshrximm amount, [value] => shiftRightTowardZero value amount
  | .Olea address, _ => evalAddressing32 ge stack address values
  | .Ocast32signed, [value] => some (Val.longofint value)
  | .Oleal address, _ => evalAddressing64 ge stack address values
  | .Oaddf, [left, right] => some (Val.addf left right)
  | .Osubf, [left, right] => some (Val.subf left right)
  | .Omulf, [left, right] => some (Val.mulf left right)
  | .Odivf, [left, right] => some (Val.divf left right)
  | _, _ => none

/-- `Oshrximm 1` on a 32-bit integer is signed division by two, rounding toward zero. -/
theorem shift_right_one (value : Integers.Int) :
    shiftRightTowardZero (.Vint value) (Integers.Int.repr 1) =
      some (.Vint (Integers.Int.divs value (Integers.Int.repr 2))) := rfl

/-- `Oshrximm 1` agrees with the source division `Odiv` by two on every 32-bit integer, negatives
included. -/
theorem shift_right_one_eq_div (value : Integers.Int) :
    shiftRightTowardZero (.Vint value) (Integers.Int.repr 1) =
      Val.divs (.Vint value) (.Vint (Integers.Int.repr 2)) := by
  rw [shift_right_one]
  have hzero : Integers.Int.eq (Integers.Int.repr 2) Integers.Int.zero = false := rfl
  have hmone : Integers.Int.eq (Integers.Int.repr 2) Integers.Int.mone = false := rfl
  simp [Val.divs, hzero, hmone]

end Quadrature.CminorSel
