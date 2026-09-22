import Quadrature.Compiler.CminorSel.Operations

/-!
# Machine registers and abstract stack locations

Locations and location maps after `backend/Locations.v`, `backend/LTL.v`, and the
x86-64 ELF calling conventions in `x86/Machregs.v` and `x86/Conventions1.v`.
`Location` is a machine register or an abstract stack slot, and `Locset` maps locations
to values. Stack offsets are measured in four-byte units, and `Locset.set` makes every
overlapping slot undefined on a write. Stack writes also normalize the value to the
slot's memory chunk.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.LTL

open CC

/-- x86-64 machine registers: 15 integer registers, 16 SSE registers `X0` to `X15`, and the x87
top of stack `FP0`. -/
inductive MachineReg where
  | AX | BX | CX | DX | SI | DI | BP | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15
  | X0 | X1 | X2 | X3 | X4 | X5 | X6 | X7 | X8 | X9 | X10 | X11 | X12 | X13 | X14 | X15
  | FP0
  deriving DecidableEq

/-- Stack slot kinds: local slots, incoming arguments, and outgoing arguments. -/
inductive Slot where
  | Local | Incoming | Outgoing
  deriving DecidableEq

/-- A machine register, or an abstract stack slot with its kind, offset, and type. -/
inductive Location where
  | R (register : MachineReg)
  | S (slot : Slot) (offset : Int) (type : ATyp)
  deriving DecidableEq

/-- Slot sizes are in four-byte units, not bytes. -/
def slotSize : ATyp → Int
  | .Tint | .Tsingle | .Tany32 => 1
  | .Tlong | .Tfloat | .Tany64 => 2

/-- `Location.disjoint l l'` holds when writing `l` cannot affect `l'`: distinct registers, slots of
different kinds, or slots whose extents do not overlap. -/
def Location.disjoint : Location → Location → Bool
  | .R left, .R right => left != right
  | .S left a ta, .S right b tb =>
      left != right || decide (a + slotSize ta ≤ b) || decide (b + slotSize tb ≤ a)
  | _, _ => true

/-- Location maps: total functions from locations to values. -/
abbrev Locset := Location → Val

/-- The location map holding `Vundef` everywhere. -/
def Locset.empty : Locset := fun _ => .Vundef

/-- `Locset.get ls l` reads the location `l`. -/
def Locset.get (locations : Locset) (location : Location) : Val := locations location

/-- `Locset.reg ls r` reads the machine register `r`. -/
def Locset.reg (locations : Locset) (register : MachineReg) : Val :=
  locations (.R register)

/-- `Locset.values ls rs` reads the registers `rs` in order. -/
def Locset.values (locations : Locset) (registers : List MachineReg) : List Val :=
  registers.map locations.reg

/-- `Locset.set ls l v` writes `v` to `l`, normalizing a slot write to the slot's chunk, and sets
every other location overlapping `l` to `Vundef`. Disjoint locations keep their values. -/
def Locset.set (locations : Locset) (location : Location) (value : Val) : Locset :=
  fun other =>
    if location = other then
      match location with
      | .R _ => value
      | .S _ _ type => Val.loadResult (Chunk.ofTyp type) value
    else if location.disjoint other then locations other else .Vundef

/-- `Locset.undefRegs ls rs` sets each register in `rs` to `Vundef`. -/
def Locset.undefRegs (locations : Locset) : List MachineReg → Locset
  | [] => locations
  | register :: registers => (locations.undefRegs registers).set (.R register) .Vundef

/-- Builtin results over machine registers: a register, no result, or a split 64-bit pair. -/
inductive BuiltinRes where
  | BR (register : MachineReg)
  | BR_none
  | BR_splitlong (hi lo : BuiltinRes)
  deriving DecidableEq

/-- `Locset.setResult ls res v` writes `v` to the result register, or its high and low words to
the registers of a split pair. -/
def Locset.setResult (locations : Locset) (result : BuiltinRes) (value : Val) : Locset :=
  match result with
  | .BR register => locations.set (.R register) value
  | .BR_none => locations
  | .BR_splitlong hi lo =>
      (locations.setResult hi (Val.hiword value)).setResult lo (Val.loword value)

/-- `isCalleeSave r` holds for the ELF64 callee-save registers `BX`, `BP`, and `R12` to `R15`. -/
def isCalleeSave : MachineReg → Bool
  | .BX | .BP | .R12 | .R13 | .R14 | .R15 => true
  | _ => false

/-- `callRegs caller` is the callee's view at entry: registers pass through, the caller's outgoing
slots become the callee's incoming slots, and all other slots are undefined. -/
def callRegs (caller : Locset) : Locset
  | .R register => caller (.R register)
  | .S .Incoming offset type => caller (.S .Outgoing offset type)
  | .S .Local _ _ | .S .Outgoing _ _ => .Vundef

/-- `returnRegs caller callee` is the caller's view after return: callee-save registers and local
and incoming slots come from `caller`, other registers from `callee`, and outgoing slots are
undefined. -/
def returnRegs (caller callee : Locset) : Locset
  | .R register => if isCalleeSave register then caller (.R register) else callee (.R register)
  | .S .Outgoing _ _ => .Vundef
  | .S slot offset type => caller (.S slot offset type)

/-- `undefCallerSaveRegs ls` sets every caller-save register and every outgoing slot to `Vundef`,
as an external call may clobber them. -/
def undefCallerSaveRegs (locations : Locset) : Locset
  | .R register => if isCalleeSave register then locations (.R register) else .Vundef
  | .S .Outgoing _ _ => .Vundef
  | .S slot offset type => locations (.S slot offset type)

/-- `argumentLocations tys i f off` assigns ELF64 argument locations to the types `tys`, given the
integer and floating registers already used and the next outgoing slot offset. -/
def argumentLocations : List ATyp → Nat → Nat → Int → List Location
  | [], _, _, _ => []
  | type :: types, integer, floating, offset =>
      match type with
      | .Tint | .Tlong | .Tany32 | .Tany64 =>
          match ([.DI, .SI, .DX, .CX, .R8, .R9] : List MachineReg)[integer]? with
          | some register =>
              .R register :: argumentLocations types (integer + 1) floating offset
          | none => .S .Outgoing offset type ::
              argumentLocations types integer floating (offset + 2)
      | .Tfloat | .Tsingle =>
          match ([.X0, .X1, .X2, .X3, .X4, .X5, .X6, .X7] : List MachineReg)[floating]? with
          | some register =>
              .R register :: argumentLocations types integer (floating + 1) offset
          | none => .S .Outgoing offset type ::
              argumentLocations types integer floating (offset + 2)

/-- `locArguments sig` lists the ELF64 argument locations of a signature: `DI`, `SI`, `DX`, `CX`,
`R8`, `R9` and `X0` to `X7` first, then outgoing stack slots. -/
def locArguments (signature : Signature) : List Location :=
  argumentLocations (signature.sig_args.map XType.proj) 0 0 0

/-- `locResult sig` is the ELF64 result register: `X0` for floating-point results and `AX`
otherwise. -/
def locResult (signature : Signature) : MachineReg :=
  match signature.sig_res.proj with
  | .Tfloat | .Tsingle => .X0
  | _ => .AX

/-- `registerByName s` maps an assembler register name from an inline-assembly clobber list to a
machine register. -/
def registerByName : String → Option MachineReg
  | "RAX" | "EAX" => some .AX
  | "RBX" | "EBX" => some .BX
  | "RCX" | "ECX" => some .CX
  | "RDX" | "EDX" => some .DX
  | "RSI" | "ESI" => some .SI
  | "RDI" | "EDI" => some .DI
  | "RBP" | "EBP" => some .BP
  | "R8" => some .R8
  | "R9" => some .R9
  | "R10" => some .R10
  | "R11" => some .R11
  | "R12" => some .R12
  | "R13" => some .R13
  | "R14" => some .R14
  | "R15" => some .R15
  | "XMM0" => some .X0
  | "XMM1" => some .X1
  | "XMM2" => some .X2
  | "XMM3" => some .X3
  | "XMM4" => some .X4
  | "XMM5" => some .X5
  | "XMM6" => some .X6
  | "XMM7" => some .X7
  | "XMM8" => some .X8
  | "XMM9" => some .X9
  | "XMM10" => some .X10
  | "XMM11" => some .X11
  | "XMM12" => some .X12
  | "XMM13" => some .X13
  | "XMM14" => some .X14
  | "XMM15" => some .X15
  | "ST0" => some .FP0
  | _ => none

/-- `destroyedByBuiltin ef` lists the registers a builtin clobbers on x86-64, after
`destroyed_by_builtin`. -/
def destroyedByBuiltin : ExtFun → List MachineReg
  | .EF_memcpy size _ => if size ≤ 32 then [.CX, .X7] else [.CX, .SI, .DI]
  | .EF_builtin name _ =>
      if name = "__builtin_va_start" then [.AX]
      else if name = "__builtin_write16_reversed" || name = "__builtin_write32_reversed" then
        [.CX, .DX]
      else []
  | .EF_inline_asm _ _ clobbers => clobbers.filterMap registerByName
  | _ => []

/-- `destroyedByGetstack slot` lists the registers clobbered when reading a slot: `AX` for incoming
slots. -/
def destroyedByGetstack : Slot → List MachineReg
  | .Incoming => [.AX]
  | _ => []

/-- `destroyedBySetstack ty` lists the registers clobbered when writing a slot: `FP0` for
floating-point types. -/
def destroyedBySetstack : ATyp → List MachineReg
  | .Tfloat | .Tsingle => [.FP0]
  | _ => []

/-- Writing a register and reading it back yields the written value. -/
@[simp]
theorem set_register_same (locations : Locset) (register : MachineReg) (value : Val) :
    (locations.set (.R register) value).reg register = value := by
  simp [Locset.set, Locset.reg]

/-- Writing a slot and reading it back yields the value normalized to the slot's chunk. -/
@[simp]
theorem set_slot_same (locations : Locset) (slot : Slot) (offset : Int) (type : ATyp)
    (value : Val) :
    (locations.set (.S slot offset type) value) (.S slot offset type) =
      Val.loadResult (Chunk.ofTyp type) value := by
  simp [Locset.set]

/-- Writing a location leaves every disjoint location unchanged. -/
theorem set_disjoint (locations : Locset) (location other : Location) (value : Val)
    (hne : location ≠ other) (hdisjoint : location.disjoint other = true) :
    locations.set location value other = locations other := by
  simp [Locset.set, hne, hdisjoint]

/-- Writing a location makes every distinct overlapping location `Vundef`. -/
theorem set_overlap (locations : Locset) (location other : Location) (value : Val)
    (hne : location ≠ other) (hoverlap : location.disjoint other = false) :
    locations.set location value other = .Vundef := by
  simp [Locset.set, hne, hoverlap]

end Quadrature.LTL
