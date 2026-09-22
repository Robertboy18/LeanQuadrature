import Quadrature.Compiler.Asm.Syntax
import Quadrature.Compiler.LTL.Locations

/-!
# Assembly registers and memory states

Register sets and states for x86-64 assembly, after `x86/Asm.v`. Read `State` first: a
register map over `PReg` and a memory. The map includes the program counter, the
return-address pseudo-register `RA`, the stack pointer, floating-point registers, and
condition flags. Frames live in ordinary memory, and no hidden stack restores registers.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Asm

open CC

/-- The processor register assigned to each Mach register by CompCert's `x86/Asmgen.v`. -/
def pregOf : LTL.MachineReg → PReg
  | .AX => .IR .RAX
  | .BX => .IR .RBX
  | .CX => .IR .RCX
  | .DX => .IR .RDX
  | .SI => .IR .RSI
  | .DI => .IR .RDI
  | .BP => .IR .RBP
  | .R8 => .IR .R8
  | .R9 => .IR .R9
  | .R10 => .IR .R10
  | .R11 => .IR .R11
  | .R12 => .IR .R12
  | .R13 => .IR .R13
  | .R14 => .IR .R14
  | .R15 => .IR .R15
  | .X0 => .FR .XMM0
  | .X1 => .FR .XMM1
  | .X2 => .FR .XMM2
  | .X3 => .FR .XMM3
  | .X4 => .FR .XMM4
  | .X5 => .FR .XMM5
  | .X6 => .FR .XMM6
  | .X7 => .FR .XMM7
  | .X8 => .FR .XMM8
  | .X9 => .FR .XMM9
  | .X10 => .FR .XMM10
  | .X11 => .FR .XMM11
  | .X12 => .FR .XMM12
  | .X13 => .FR .XMM13
  | .X14 => .FR .XMM14
  | .X15 => .FR .XMM15
  | .FP0 => .ST0

/-- Processor registers map to values. -/
abbrev Regset := PReg → Val

/-- The register set with every register `Vundef`. -/
def Regset.empty : Regset := fun _ => .Vundef

/-- Updates one register. -/
def Regset.set (registers : Regset) (register : PReg) (value : Val) : Regset :=
  fun other => if register = other then value else registers other

/-- Sets each listed register to `Vundef`. -/
def Regset.undefRegs (registers : Regset) : List PReg → Regset
  | [] => registers
  | register :: rest => (registers.set register .Vundef).undefRegs rest

/-- Writes a builtin result, splitting a long into high and low words when required. -/
def Regset.setResult (registers : Regset) (result : BuiltinRes) (value : Val) : Regset :=
  match result with
  | .BR register => registers.set register value
  | .BR_none => registers
  | .BR_splitlong hi lo =>
      (registers.setResult hi (Val.hiword value)).setResult lo (Val.loword value)

/-- ELF64 preserves the stack pointer and the six callee-save integer registers. -/
def preservedByExternal : PReg → Bool
  | .IR .RSP | .IR .RBX | .IR .RBP | .IR .R12 | .IR .R13 | .IR .R14 | .IR .R15 => true
  | _ => false

/-- Sets every register not preserved across external calls to `Vundef`. -/
def Regset.undefCallerSave (registers : Regset) : Regset :=
  fun register => if preservedByExternal register then registers register else .Vundef

/-- Reading the register just written returns the written value. -/
@[simp]
theorem set_same (registers : Regset) (register : PReg) (value : Val) :
    registers.set register value register = value := by
  simp [Regset.set]

/-- Writing `register` leaves a different register `other` unchanged, given `hne`. -/
theorem set_other (registers : Regset) (register other : PReg) (value : Val)
    (hne : register ≠ other) : registers.set register value other = registers other := by
  simp [Regset.set, hne]

/-- An assembly state: the register map and memory. Control lives in `PC`, so there is no
separate frame list. -/
structure State where
  registers : Regset
  memory : Mem

/-- The instruction at an integer position, `none` for negative positions or past the end. -/
def findInstr (position : Int) : Code → Option Instruction
  | [] => none
  | instruction :: rest =>
      if position = 0 then some instruction else findInstr (position - 1) rest

/-- A jump resumes immediately after the first matching label. -/
def labelPos (label : Label) (position : Int) : Code → Option Int
  | [] => none
  | instruction :: rest =>
      if instruction = .Plabel label then some (position + 1)
      else labelPos label (position + 1) rest

/-- Advances `PC` by one instruction. -/
def nextInstr (registers : Regset) : Regset :=
  registers.set .PC (Val.offsetPtr (registers .PC) Integers.Ptrofs.one)

/-- Undefined flags follow the compiler's pseudo-instruction convention. -/
def nextInstrNf (registers : Regset) : Regset :=
  nextInstr (registers.undefRegs [.CR .ZF, .CR .CF, .CR .PF, .CR .SF, .CR .OF])

end Quadrature.Asm
