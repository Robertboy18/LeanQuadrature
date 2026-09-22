import Quadrature.Compiler.Asm.State

/-!
# Assembly addressing and condition flags

Addressing modes, comparison flags, and signed division, after `x86/Asm.v`. Read
`evalAddrMode` first, the address denoted by an addressing mode. Subtraction flags and
extended signed division use the definitions of `lib/Integers.v`, including division by
zero and quotient overflow. Both address widths are needed on x86-64: `Pleal` performs
32-bit arithmetic even in the 64-bit ABI.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Asm

open CC

/-- The 32-bit value of an addressing mode: base plus scaled index plus displacement. -/
def evalAddrMode32 (ge : Genv) (address : AddrMode) (registers : Regset) : Val :=
  match address with
  | .Addrmode base index displacement =>
      Val.add
        (match base with
         | none => .Vint Integers.Int.zero
         | some register => registers (.IR register))
        (Val.add
          (match index with
           | none => .Vint Integers.Int.zero
           | some (register, scale) =>
               if scale = 1 then registers (.IR register)
               else Val.mul (registers (.IR register)) (.Vint (Integers.Int.repr scale)))
          (match displacement with
           | .inl offset => .Vint (Integers.Int.repr offset)
           | .inr (name, offset) => CC.Genv.symbolAddress ge name offset))

/-- The 64-bit value of an addressing mode: base plus scaled index plus displacement. -/
def evalAddrMode64 (ge : Genv) (address : AddrMode) (registers : Regset) : Val :=
  match address with
  | .Addrmode base index displacement =>
      Val.addl
        (match base with
         | none => .Vlong Integers.Int64.zero
         | some register => registers (.IR register))
        (Val.addl
          (match index with
           | none => .Vlong Integers.Int64.zero
           | some (register, scale) =>
               if scale = 1 then registers (.IR register)
               else Val.mull (registers (.IR register)) (.Vlong (Integers.Int64.repr scale)))
          (match displacement with
           | .inl offset => .Vlong (Integers.Int64.repr offset)
           | .inr (name, offset) => CC.Genv.symbolAddress ge name offset))

/-- The address denoted by an addressing mode at the pointer width of the target. -/
def evalAddrMode (ge : Genv) (address : AddrMode) (registers : Regset) : Val :=
  if Archi.ptr64 then evalAddrMode64 ge address registers
  else evalAddrMode32 ge address registers

/-- The sign flag of a 32-bit integer, `Vundef` for other values. -/
def negative32 : Val → Val
  | .Vint value => Val.ofBool (Integers.Int.lt value Integers.Int.zero)
  | _ => .Vundef

/-- The overflow flag of a 32-bit signed subtraction, `Vundef` for non-integer operands. -/
def subOverflow32 : Val → Val → Val
  | .Vint left, .Vint right =>
      let difference := Integers.Int.signed left - Integers.Int.signed right
      Val.ofBool (!(decide (Integers.Int.min_signed ≤ difference) &&
        decide (difference ≤ Integers.Int.max_signed)))
  | _, _ => .Vundef

/-- The flags after comparing `left` with `right`, as `Pcmpl` sets them. `PF` is undefined. -/
def compareInts (left right : Val) (registers : Regset) (memory : Mem) : Regset :=
  let registers := registers.set (.CR .ZF)
    (Val.ofOptbool (Val.cmpu_bool (Mem.validPointer memory) .Ceq left right))
  let registers := registers.set (.CR .CF)
    (Val.ofOptbool (Val.cmpu_bool (Mem.validPointer memory) .Clt left right))
  let registers := registers.set (.CR .SF) (negative32 (Val.sub left right))
  let registers := registers.set (.CR .OF) (subOverflow32 left right)
  registers.set (.CR .PF) .Vundef

/-- `Int.divmods2`: a signed double-width numerator divided by a signed word. -/
def divmods32 (hi lo denominator : Integers.Int) :
    Option (Integers.Int × Integers.Int) :=
  if denominator = Integers.Int.zero then none
  else
    let numerator := Integers.Int.signed hi * Integers.Int.modulus + Integers.Int.unsigned lo
    let quotient := numerator.tdiv (Integers.Int.signed denominator)
    let remainder := numerator.tmod (Integers.Int.signed denominator)
    if Integers.Int.min_signed ≤ quotient ∧ quotient ≤ Integers.Int.max_signed then
      some (Integers.Int.repr quotient, Integers.Int.repr remainder)
    else none

/-- Decides a test condition from the flags, `none` when a needed flag is undefined. -/
def evalTestCond (condition : TestCond) (registers : Regset) : Option Bool :=
  match condition with
  | .Cond_e =>
      match registers (.CR .ZF) with
      | .Vint value => some (Integers.Int.eq value Integers.Int.one)
      | _ => none
  | .Cond_ne =>
      match registers (.CR .ZF) with
      | .Vint value => some (Integers.Int.eq value Integers.Int.zero)
      | _ => none
  | .Cond_b =>
      match registers (.CR .CF) with
      | .Vint value => some (Integers.Int.eq value Integers.Int.one)
      | _ => none
  | .Cond_be =>
      match registers (.CR .CF), registers (.CR .ZF) with
      | .Vint carry, .Vint zero =>
          some (Integers.Int.eq carry Integers.Int.one || Integers.Int.eq zero Integers.Int.one)
      | _, _ => none
  | .Cond_ae =>
      match registers (.CR .CF) with
      | .Vint value => some (Integers.Int.eq value Integers.Int.zero)
      | _ => none
  | .Cond_a =>
      match registers (.CR .CF), registers (.CR .ZF) with
      | .Vint carry, .Vint zero =>
          some (Integers.Int.eq carry Integers.Int.zero && Integers.Int.eq zero Integers.Int.zero)
      | _, _ => none
  | .Cond_l =>
      match registers (.CR .OF), registers (.CR .SF) with
      | .Vint overflow, .Vint sign =>
          some (Integers.Int.eq (Integers.Int.xor overflow sign) Integers.Int.one)
      | _, _ => none
  | .Cond_le =>
      match registers (.CR .OF), registers (.CR .SF), registers (.CR .ZF) with
      | .Vint overflow, .Vint sign, .Vint zero =>
          some (Integers.Int.eq (Integers.Int.xor overflow sign) Integers.Int.one ||
            Integers.Int.eq zero Integers.Int.one)
      | _, _, _ => none
  | .Cond_ge =>
      match registers (.CR .OF), registers (.CR .SF) with
      | .Vint overflow, .Vint sign =>
          some (Integers.Int.eq (Integers.Int.xor overflow sign) Integers.Int.zero)
      | _, _ => none
  | .Cond_g =>
      match registers (.CR .OF), registers (.CR .SF), registers (.CR .ZF) with
      | .Vint overflow, .Vint sign, .Vint zero =>
          some (Integers.Int.eq (Integers.Int.xor overflow sign) Integers.Int.zero &&
            Integers.Int.eq zero Integers.Int.zero)
      | _, _, _ => none
  | .Cond_p =>
      match registers (.CR .PF) with
      | .Vint value => some (Integers.Int.eq value Integers.Int.one)
      | _ => none
  | .Cond_np =>
      match registers (.CR .PF) with
      | .Vint value => some (Integers.Int.eq value Integers.Int.zero)
      | _ => none

end Quadrature.Asm
