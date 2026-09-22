import Quadrature.Compiler.Asm.State
import Quadrature.Compiler.Mach.Syntax

/-!
# Assembly generation for the Mach fragment of the ten programs

A Lean mirror of the x86-64 cases of CompCert's `x86/Asmgen.v`, for the Mach instructions
the ten programs use. Read `translateFunction` first: the prologue `Pallocframe`, the
translated body from `code`, and the code-size check. `code` translates a Mach
instruction list and `instruction` one instruction, tracking whether `RAX` still holds
the parent frame pointer for `Mgetparam`. Register classes, two-address constraints,
addressing modes, and frame accesses are checked as in Asmgen, and unsupported
combinations return `none`. `Asm/GeneratedReturnAddresses.lean` compares the translation
of each imported Mach program with the imported assembly.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Asm.Generation

open CC

/-- The integer register of a Mach register, `none` for float registers. -/
def iregOf (register : Mach.MachineReg) : Option IReg :=
  match pregOf register with
  | .IR result => some result
  | _ => none

/-- The SSE register of a Mach register, `none` for integer registers or `FP0`. -/
def fregOf (register : Mach.MachineReg) : Option FReg :=
  match pregOf register with
  | .FR result => some result
  | _ => none

/-- A register move within one class, as Asmgen's `mk_mov`. -/
def move (target source : PReg) : Option Code :=
  match target, source with
  | .IR rd, .IR rs => some [.Pmov_rr rd rs]
  | .FR rd, .FR rs => some [.Pmovsd_ff rd rs]
  | _, _ => none

/-- A typed load from `base` plus `offset` into a Mach register, as Asmgen's `loadind`. -/
def loadIndirect (base : IReg) (offset : Integers.Ptrofs) (type : ATyp)
    (target : Mach.MachineReg) : Option Code :=
  let address := AddrMode.Addrmode (some base) none (.inl (Integers.Ptrofs.unsigned offset))
  match type, pregOf target with
  | .Tint, .IR r => some [.Pmovl_rm r address]
  | .Tlong, .IR r => some [.Pmovq_rm r address]
  | .Tsingle, .FR r => some [.Pmovss_fm r address]
  | .Tsingle, .ST0 => some [.Pflds_m address]
  | .Tfloat, .FR r => some [.Pmovsd_fm r address]
  | .Tfloat, .ST0 => some [.Pfldl_m address]
  | .Tany64, .IR r => some [.Pmov_rm_a r address]
  | .Tany64, .FR r => some [.Pmovsd_fm_a r address]
  | _, _ => none

/-- A typed store of a Mach register to `base` plus `offset`, as Asmgen's `storeind`. -/
def storeIndirect (source : Mach.MachineReg) (base : IReg) (offset : Integers.Ptrofs)
    (type : ATyp) : Option Code :=
  let address := AddrMode.Addrmode (some base) none (.inl (Integers.Ptrofs.unsigned offset))
  match type, pregOf source with
  | .Tint, .IR r => some [.Pmovl_mr address r]
  | .Tlong, .IR r => some [.Pmovq_mr address r]
  | .Tsingle, .FR r => some [.Pmovss_mf address r]
  | .Tsingle, .ST0 => some [.Pfstps_m address]
  | .Tfloat, .FR r => some [.Pmovsd_mf address r]
  | .Tfloat, .ST0 => some [.Pfstpl_m address]
  | .Tany64, .IR r => some [.Pmov_mr_a address r]
  | .Tany64, .FR r => some [.Pmovsd_mf_a address r]
  | _, _ => none

/-- Translates a Mach addressing mode and its argument registers, as Asmgen's
`transl_addressing`. -/
def addressing : Mach.Addressing → List Mach.MachineReg → Option AddrMode
  | .Aindexed offset, [a] => do
      return .Addrmode (some (← iregOf a)) none (.inl offset)
  | .Aindexed2 offset, [a, b] => do
      return .Addrmode (some (← iregOf a)) (some (← iregOf b, 1)) (.inl offset)
  | .Ascaled scale offset, [a] => do
      return .Addrmode none (some (← iregOf a, scale)) (.inl offset)
  | .Aindexed2scaled scale offset, [a, b] => do
      return .Addrmode (some (← iregOf a)) (some (← iregOf b, scale)) (.inl offset)
  | .Aglobal name offset, [] => some (.Addrmode none none (.inr (name, offset)))
  | .Abased name offset, [a] => do
      return .Addrmode (some (← iregOf a)) none (.inr (name, offset))
  | .Abasedscaled scale name offset, [a] => do
      return .Addrmode none (some (← iregOf a, scale)) (.inr (name, offset))
  | .Ainstack offset, [] =>
      some (.Addrmode (some .RSP) none (.inl (Integers.Ptrofs.signed offset)))
  | _, _ => none

/-- Reduces a constant displacement to its signed 32-bit value, as Asmgen's
`normalize_addrmode_32`. -/
def normalizeAddress32 : AddrMode → AddrMode
  | .Addrmode base index (.inl offset) =>
      .Addrmode base index (.inl (Integers.Int.signed (Integers.Int.repr offset)))
  | address => address

/-- Splits a displacement outside the 32-bit range into a zero-displacement mode and an added
constant, as Asmgen's `normalize_addrmode_64`. -/
def normalizeAddress64 : AddrMode → AddrMode × Option Integers.Int64
  | .Addrmode base index (.inl offset) =>
      if -(2 ^ 31) ≤ offset ∧ offset ≤ 2 ^ 31 - 1 then
        (.Addrmode base index (.inl offset), none)
      else
        (.Addrmode base index (.inl 0), some (Integers.Int64.repr offset))
  | .Addrmode base index (.inr (name, offset)) =>
      if -(2 ^ 24) ≤ Integers.Ptrofs.signed offset ∧
          Integers.Ptrofs.signed offset ≤ 2 ^ 24 - 1 then
        (.Addrmode base index (.inr (name, offset)), none)
      else
        (.Addrmode base index (.inr (name, Integers.Ptrofs.zero)),
          some (Integers.Ptrofs.to_int64 offset))

/-- A two-address float operation, requiring the first operand to be the target. -/
def floatBinary (instruction : FReg → FReg → Instruction)
    (first second target : Mach.MachineReg) : Option Code := do
  if first = target then
    return [instruction (← fregOf target) (← fregOf second)]
  else none

/-- Translates a Mach operation, as Asmgen's `transl_op` for the cases the ten programs use. -/
def operation (op : Mach.Operation) (args : List Mach.MachineReg)
    (target : Mach.MachineReg) : Option Code :=
  match op, args with
  | .Omove, [source] => move (pregOf target) (pregOf source)
  | .selected (.Ointconst value), [] => do
      let r ← iregOf target
      return [if value = Integers.Int.zero then .Pxorl_r r else .Pmovl_ri r value]
  | .selected (.Ofloatconst value), [] => do
      let r ← fregOf target
      return [if value = Floats.Float.zero then .Pxorpd_f r else .Pmovsd_fi r value]
  | .selected .Omul, [a, b] => do
      if a = target then return [.Pimull_rr (← iregOf target) (← iregOf b)] else none
  | .selected .Odiv, [a, b] =>
      if a = .AX ∧ b = .CX ∧ target = .AX then some [.Pcltd, .Pidivl .RCX] else none
  | .selected .Omod, [a, b] =>
      if a = .AX ∧ b = .CX ∧ target = .DX then some [.Pcltd, .Pidivl .RCX] else none
  | .selected (.Oshrximm amount), [a] =>
      if a = .AX ∧ target = .AX then
        let mask := Integers.Int.sub (Integers.Int.shl Integers.Int.one amount) Integers.Int.one
        some [.Ptestl_rr .RAX .RAX,
          .Pleal .RCX (.Addrmode (some .RAX) none (.inl (Integers.Int.unsigned mask))),
          .Pcmov .Cond_l .RAX .RCX, .Psarl_ri .RAX amount]
      else none
  | .selected (.Olea address), _ => do
      let mode ← addressing address args
      return [.Pleal (← iregOf target) (normalizeAddress32 mode)]
  | .selected .Ocast32signed, [a] => do
      return [.Pmovsl_rr (← iregOf target) (← iregOf a)]
  | .selected (.Oleal address), _ => do
      let mode ← addressing address args
      let r ← iregOf target
      match normalizeAddress64 mode with
      | (normalized, none) => return [.Pleaq r normalized]
      | (normalized, some delta) => return [.Pleaq r normalized, .Paddq_ri r delta]
  | .selected .Oaddf, [a, b] => floatBinary .Paddd_ff a b target
  | .selected .Osubf, [a, b] => floatBinary .Psubd_ff a b target
  | .selected .Omulf, [a, b] => floatBinary .Pmuld_ff a b target
  | .selected .Odivf, [a, b] => floatBinary .Pdivd_ff a b target
  | _, _ => none

/-- Translates a Mach load by chunk, as Asmgen's `transl_load`. -/
def load (chunk : Chunk) (address : Mach.Addressing) (args : List Mach.MachineReg)
    (target : Mach.MachineReg) : Option Code := do
  let mode ← addressing address args
  match chunk with
  | .Mint8unsigned => return [.Pmovzb_rm (← iregOf target) mode]
  | .Mint8signed => return [.Pmovsb_rm (← iregOf target) mode]
  | .Mint16unsigned => return [.Pmovzw_rm (← iregOf target) mode]
  | .Mint16signed => return [.Pmovsw_rm (← iregOf target) mode]
  | .Mint32 => return [.Pmovl_rm (← iregOf target) mode]
  | .Mint64 => return [.Pmovq_rm (← iregOf target) mode]
  | .Mfloat32 => return [.Pmovss_fm (← fregOf target) mode]
  | .Mfloat64 => return [.Pmovsd_fm (← fregOf target) mode]
  | _ => none

/-- Translates a Mach store by chunk, as Asmgen's `transl_store`. -/
def store (chunk : Chunk) (address : Mach.Addressing) (args : List Mach.MachineReg)
    (source : Mach.MachineReg) : Option Code := do
  let mode ← addressing address args
  match chunk with
  | .Mint8unsigned => return [.Pmovb_mr mode (← iregOf source)]
  | .Mint16unsigned => return [.Pmovw_mr mode (← iregOf source)]
  | .Mint32 => return [.Pmovl_mr mode (← iregOf source)]
  | .Mint64 => return [.Pmovq_mr mode (← iregOf source)]
  | .Mfloat32 => return [.Pmovss_mf mode (← fregOf source)]
  | .Mfloat64 => return [.Pmovsd_mf mode (← fregOf source)]
  | _ => none

/-- The test condition of a signed comparison, as Asmgen's `testcond_for_signed_comparison`. -/
def signedCondition : Comparison → TestCond
  | .Ceq => .Cond_e
  | .Cne => .Cond_ne
  | .Clt => .Cond_l
  | .Cle => .Cond_le
  | .Cgt => .Cond_g
  | .Cge => .Cond_ge

/-- Translates a conditional branch into a compare or test followed by `Pjcc`, as Asmgen's
`transl_cond` and the jump it guards. -/
def conditional (condition : Mach.Condition) (args : List Mach.MachineReg)
    (label : Label) : Option Code :=
  match condition, args with
  | .Ccomp comparison, [a, b] => do
      return [.Pcmpl_rr (← iregOf a) (← iregOf b), .Pjcc (signedCondition comparison) label]
  | .Ccompimm comparison value, [a] => do
      let r ← iregOf a
      return [if value = Integers.Int.zero then .Ptestl_rr r r else .Pcmpl_ri r value,
        .Pjcc (signedCondition comparison) label]
  | _, _ => none

/-- Maps Mach builtin arguments to assembly ones through `pregOf`. -/
def builtinArg : Mach.BuiltinArg → BuiltinArg
  | .BA register => .BA (pregOf register)
  | .BA_int value => .BA_int value
  | .BA_long value => .BA_long value
  | .BA_float value => .BA_float value
  | .BA_single value => .BA_single value
  | .BA_loadstack chunk offset => .BA_loadstack chunk offset
  | .BA_addrstack offset => .BA_addrstack offset
  | .BA_loadglobal chunk name offset => .BA_loadglobal chunk name offset
  | .BA_addrglobal name offset => .BA_addrglobal name offset
  | .BA_splitlong hi lo => .BA_splitlong (builtinArg hi) (builtinArg lo)
  | .BA_addptr left right => .BA_addptr (builtinArg left) (builtinArg right)

/-- Maps Mach builtin results to assembly ones through `pregOf`. -/
def builtinRes : Mach.BuiltinRes → BuiltinRes
  | .BR register => .BR (pregOf register)
  | .BR_none => .BR_none
  | .BR_splitlong hi lo => .BR_splitlong (builtinRes hi) (builtinRes lo)

/-- Translation of one instruction, before appending the translated continuation. -/
def instruction (function : Mach.Function) (source : Mach.Instruction)
    (axIsParent : Bool) : Option Code :=
  match source with
  | .Mgetstack offset type target => loadIndirect .RSP offset type target
  | .Msetstack source offset type => storeIndirect source .RSP offset type
  | .Mgetparam offset type target => do
      let body ← loadIndirect .RAX offset type target
      if axIsParent then return body
      else return (← loadIndirect .RSP function.fn_link_ofs .Tlong .AX) ++ body
  | .Mop op args target => operation op args target
  | .Mload chunk address args target => load chunk address args target
  | .Mstore chunk address args source => store chunk address args source
  | .Mcall signature (.inl register) => do return [.Pcall_r (← iregOf register) signature]
  | .Mcall signature (.inr name) => some [.Pcall_s name signature]
  | .Mtailcall signature (.inl register) => do
      return [.Pfreeframe function.fn_stacksize function.fn_retaddr_ofs function.fn_link_ofs,
        .Pjmp_r (← iregOf register) signature]
  | .Mtailcall signature (.inr name) =>
      some [.Pfreeframe function.fn_stacksize function.fn_retaddr_ofs function.fn_link_ofs,
        .Pjmp_s name signature]
  | .Mbuiltin function args result =>
      some [.Pbuiltin function (args.map builtinArg) (builtinRes result)]
  | .Mlabel label => some [.Plabel label]
  | .Mgoto label => some [.Pjmp_l label]
  | .Mcond condition args label => conditional condition args label
  | .Mjumptable register labels => do return [.Pjmptbl (← iregOf register) labels]
  | .Mreturn =>
      some [.Pfreeframe function.fn_stacksize function.fn_retaddr_ofs function.fn_link_ofs, .Pret]

/-- Whether AX still contains the parent frame pointer after this instruction. -/
def axIsParentAfter (before : Bool) : Mach.Instruction → Bool
  | .Msetstack _ _ _ => before
  | .Mgetparam _ _ target => decide (target ≠ .AX)
  | _ => false

/-- Translates a Mach instruction list, as Asmgen's `transl_code`. The Boolean records whether
`RAX` holds the parent frame pointer. -/
def code (function : Mach.Function) : Mach.Code → Bool → Option Code
  | [], _ => some []
  | head :: tail, axIsParent => do
      let continuation ← code function tail (axIsParentAfter axIsParent head)
      let emitted ← instruction function head axIsParent
      return emitted ++ continuation

/-- Function prologue and code-size check, with offsets in formal instructions. -/
def translateFunction (function : Mach.Function) : Option Function := do
  let body ← code function function.fn_code true
  let result := Instruction.Pallocframe
    function.fn_stacksize function.fn_retaddr_ofs function.fn_link_ofs :: body
  if (result.length : Int) ≤ Integers.Ptrofs.max_unsigned then
    return ⟨function.fn_sig, result⟩
  else none

end Quadrature.Asm.Generation
