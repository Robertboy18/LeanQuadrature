import Quadrature.Compiler.Asm.Operations

/-!
# Instruction execution for the imported assembly

Execution of single instructions, after `exec_instr` in `x86/Asm.v`, for the fragment
used by the ten programs. Read `execInstr` first: the successor state of one non-builtin
instruction, or `none` for instructions outside the fragment or failed memory accesses.
Builtins are handled by the `Step.builtin` rule, as in CompCert. The model includes
concrete frame allocation, saving and loading the stack pointer and return address,
memory permissions, condition flags, and instruction positions.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Asm

open CC

/-- Sets `PC` to the position after `label` in `function`, keeping the current code block. -/
def gotoLabel (function : Function) (label : Label) (registers : Regset) (memory : Mem) :
    Option State := do
  let position ← labelPos label 0 function.fn_code
  match registers .PC with
  | .Vptr block _ =>
      pure ⟨registers.set .PC (.Vptr block (Integers.Ptrofs.repr position)), memory⟩
  | _ => none

/-- Loads `chunk` at `address` into `target`, advances `PC`, and undefines the flags. -/
def execLoad (ge : Genv) (chunk : Chunk) (memory : Mem) (address : AddrMode)
    (registers : Regset) (target : PReg) : Option State := do
  let value ← Mem.loadv chunk memory (evalAddrMode ge address registers)
  pure ⟨nextInstrNf (registers.set target value), memory⟩

/-- Stores `source` as `chunk` at `address`, undefines `destroyed` and the flags, and
advances `PC`. -/
def execStore (ge : Genv) (chunk : Chunk) (memory : Mem) (address : AddrMode)
    (registers : Regset) (source : PReg) (destroyed : List PReg) : Option State := do
  let memory' ← Mem.storev chunk memory (evalAddrMode ge address registers) (registers source)
  pure ⟨nextInstrNf (registers.undefRegs destroyed), memory'⟩

/-- Executes one non-builtin instruction of `function` in the fragment the ten programs use,
`none` outside the fragment or on a failed memory access. -/
def execInstr (ge : Genv) (function : Function) (instruction : Instruction)
    (registers : Regset) (memory : Mem) : Option State :=
  match instruction with
  | .Pmov_rr target source =>
      some ⟨nextInstr (registers.set (.IR target) (registers (.IR source))), memory⟩
  | .Pmovl_ri target value =>
      some ⟨nextInstrNf (registers.set (.IR target) (.Vint value)), memory⟩
  | .Pmovq_rm target address => execLoad ge .Mint64 memory address registers (.IR target)
  | .Pmovsd_ff target source =>
      some ⟨nextInstr (registers.set (.FR target) (registers (.FR source))), memory⟩
  | .Pmovsd_fi target value =>
      some ⟨nextInstr (registers.set (.FR target) (.Vfloat value)), memory⟩
  | .Pmovsd_fm target address => execLoad ge .Mfloat64 memory address registers (.FR target)
  | .Pmovsd_mf address source => execStore ge .Mfloat64 memory address registers (.FR source) []
  | .Pmovsl_rr target source =>
      some ⟨nextInstr (registers.set (.IR target) (Val.longofint (registers (.IR source)))),
        memory⟩
  | .Pleal target address =>
      some ⟨nextInstr (registers.set (.IR target) (evalAddrMode32 ge address registers)), memory⟩
  | .Pleaq target address =>
      some ⟨nextInstr (registers.set (.IR target) (evalAddrMode64 ge address registers)), memory⟩
  | .Pimull_rr target source =>
      some ⟨nextInstrNf (registers.set (.IR target)
        (Val.mul (registers (.IR target)) (registers (.IR source)))), memory⟩
  | .Pcltd =>
      some ⟨nextInstrNf (registers.set (.IR .RDX)
        (Val.shr (registers (.IR .RAX)) (.Vint (Integers.Int.repr 31)))), memory⟩
  | .Pidivl source => do
      match registers (.IR .RDX), registers (.IR .RAX), registers (.IR source) with
      | .Vint hi, .Vint lo, .Vint denominator =>
          let (quotient, remainder) ← divmods32 hi lo denominator
          pure ⟨nextInstrNf
            ((registers.set (.IR .RAX) (.Vint quotient)).set (.IR .RDX) (.Vint remainder)),
            memory⟩
      | _, _, _ => none
  | .Pxorl_r target =>
      some ⟨nextInstrNf (registers.set (.IR target) Val.Vzero), memory⟩
  | .Psarl_ri target amount =>
      some ⟨nextInstrNf
        (registers.set (.IR target) (Val.shr (registers (.IR target)) (.Vint amount))), memory⟩
  | .Pcmpl_rr left right =>
      some ⟨nextInstr (compareInts (registers (.IR left)) (registers (.IR right))
        registers memory), memory⟩
  | .Pcmpl_ri left right =>
      some ⟨nextInstr (compareInts (registers (.IR left)) (.Vint right) registers memory), memory⟩
  | .Ptestl_rr left right =>
      some ⟨nextInstr (compareInts (Val.and (registers (.IR left)) (registers (.IR right)))
        Val.Vzero registers memory), memory⟩
  | .Pcmov condition target source =>
      let value := match evalTestCond condition registers with
        | some true => registers (.IR source)
        | some false => registers (.IR target)
        | none => .Vundef
      some ⟨nextInstr (registers.set (.IR target) value), memory⟩
  | .Paddd_ff target source =>
      some ⟨nextInstr (registers.set (.FR target)
        (Val.addf (registers (.FR target)) (registers (.FR source)))), memory⟩
  | .Psubd_ff target source =>
      some ⟨nextInstr (registers.set (.FR target)
        (Val.subf (registers (.FR target)) (registers (.FR source)))), memory⟩
  | .Pmuld_ff target source =>
      some ⟨nextInstr (registers.set (.FR target)
        (Val.mulf (registers (.FR target)) (registers (.FR source)))), memory⟩
  | .Pdivd_ff target source =>
      some ⟨nextInstr (registers.set (.FR target)
        (Val.divf (registers (.FR target)) (registers (.FR source)))), memory⟩
  | .Pxorpd_f target =>
      some ⟨nextInstrNf (registers.set (.FR target) (.Vfloat Floats.Float.zero)), memory⟩
  | .Pjmp_l label => gotoLabel function label registers memory
  | .Pjcc condition label =>
      match evalTestCond condition registers with
      | some true => gotoLabel function label registers memory
      | some false => some ⟨nextInstr registers, memory⟩
      | none => none
  | .Pcall_s name _ =>
      some ⟨(registers.set .RA (Val.offsetPtr (registers .PC) Integers.Ptrofs.one)).set .PC
        (CC.Genv.symbolAddress ge name Integers.Ptrofs.zero), memory⟩
  | .Pcall_r target _ =>
      some ⟨(registers.set .RA (Val.offsetPtr (registers .PC) Integers.Ptrofs.one)).set .PC
        (registers (.IR target)), memory⟩
  | .Pret => some ⟨registers.set .PC (registers .RA), memory⟩
  | .Pmov_rm_a target address =>
      execLoad ge (if Archi.ptr64 then .Many64 else .Many32) memory address registers (.IR target)
  | .Pmov_mr_a address source =>
      execStore ge (if Archi.ptr64 then .Many64 else .Many32) memory address
        registers (.IR source) []
  | .Plabel _ => some ⟨nextInstr registers, memory⟩
  | .Pallocframe size returnOffset linkOffset => do
      let (allocated, block) := Mem.alloc memory 0 size
      let stack := Val.Vptr block Integers.Ptrofs.zero
      let linked ← Mem.storev Mptr allocated (Val.offsetPtr stack linkOffset)
        (registers (.IR .RSP))
      let saved ← Mem.storev Mptr linked (Val.offsetPtr stack returnOffset) (registers .RA)
      pure ⟨nextInstr ((registers.set (.IR .RAX) (registers (.IR .RSP))).set (.IR .RSP) stack),
        saved⟩
  | .Pfreeframe size returnOffset linkOffset => do
      let returnAddress ← Mem.loadv Mptr memory
        (Val.offsetPtr (registers (.IR .RSP)) returnOffset)
      let stack ← Mem.loadv Mptr memory (Val.offsetPtr (registers (.IR .RSP)) linkOffset)
      match registers (.IR .RSP) with
      | .Vptr block _ =>
          let freed ← Mem.free memory block 0 size
          pure ⟨nextInstr ((registers.set (.IR .RSP) stack).set .RA returnAddress), freed⟩
      | _ => none
  | _ => none

/-- The instructions with an execution rule, plus `Pbuiltin`, which `Step.builtin` handles. -/
def Instruction.supported : Instruction → Bool
  | .Pmov_rr _ _ | .Pmovl_ri _ _ | .Pmovq_rm _ _ | .Pmovsd_ff _ _ | .Pmovsd_fi _ _
  | .Pmovsd_fm _ _ | .Pmovsd_mf _ _ | .Pmovsl_rr _ _ | .Pleal _ _ | .Pleaq _ _
  | .Pimull_rr _ _ | .Pcltd | .Pidivl _ | .Pxorl_r _ | .Psarl_ri _ _
  | .Pcmpl_rr _ _ | .Pcmpl_ri _ _ | .Ptestl_rr _ _ | .Pcmov _ _ _
  | .Paddd_ff _ _ | .Psubd_ff _ _ | .Pmuld_ff _ _ | .Pdivd_ff _ _ | .Pxorpd_f _
  | .Pjmp_l _ | .Pjcc _ _ | .Pcall_s _ _ | .Pcall_r _ _ | .Pret
  | .Pmov_rm_a _ _ | .Pmov_mr_a _ _ | .Plabel _ | .Pallocframe _ _ _
  | .Pfreeframe _ _ _ | .Pbuiltin _ _ _ => true
  | _ => false

end Quadrature.Asm
