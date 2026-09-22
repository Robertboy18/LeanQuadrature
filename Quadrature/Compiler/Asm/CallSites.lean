import Quadrature.Compiler.Asm.Imported
import Quadrature.Compiler.Asm.State
import Quadrature.Compiler.Mach.ImportedReturnAddresses

/-!
# Calls and saved return addresses in the imported assembly

Syntactic checks relating the Mach return-address table to the imported assembly of the
ten programs. Read `ReturnSiteMatches` first: a table row names the same caller in both
programs. The assembly instruction just before its offset is the call matching the Mach
call just before its continuation. `Imported.all_assembly_calls_recorded` shows the
table lists every assembly call site. The table is related to the Lean Asmgen
translation's return addresses in `Asm/GeneratedReturnAddresses.lean`.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Asm

open CC

/-- A Mach call and an assembly call agree: same signature, and the same symbol or the
register image under `pregOf`. -/
def MatchingCall : Mach.Instruction → Instruction → Prop
  | .Mcall sourceSig (.inr sourceName), .Pcall_s targetName targetSig =>
      sourceSig = targetSig ∧ sourceName = targetName
  | .Mcall sourceSig (.inl sourceReg), .Pcall_r targetReg targetSig =>
      sourceSig = targetSig ∧ pregOf sourceReg = .IR targetReg
  | _, _ => False

/-- Decidable by comparing signatures and names or registers. -/
instance (source : Mach.Instruction) (target : Instruction) :
    Decidable (MatchingCall source target) := by
  unfold MatchingCall
  split <;> infer_instance

/-- A row identifies the same caller and a matching call immediately before each continuation.
The target offset lies within the code and is representable without pointer wraparound. -/
def ReturnSiteMatches (source : Mach.Program) (target : Program) (row : Mach.AddressRow) : Prop :=
  match source.prog_defs[row.globalIndex]?, target.prog_defs[row.globalIndex]? with
  | some (sourceName, .Gfun (.Internal sourceFunction)),
      some (targetName, .Gfun (.Internal targetFunction)) =>
      sourceName = targetName ∧ sourceFunction.fn_sig = targetFunction.fn_sig ∧
      0 < row.skip ∧ 0 < row.offset ∧
      row.offset < targetFunction.fn_code.length ∧ row.offset < 2 ^ 64 ∧
      match sourceFunction.fn_code[row.skip - 1]?,
          targetFunction.fn_code[(row.offset - 1).toNat]? with
      | some sourceCall, some targetCall => MatchingCall sourceCall targetCall
      | _, _ => False
  | _, _ => False

/-- Decidable by indexing both programs and comparing the two call instructions. -/
instance (source : Mach.Program) (target : Program) (row : Mach.AddressRow) :
    Decidable (ReturnSiteMatches source target row) := by
  unfold ReturnSiteMatches
  split
  · split <;> infer_instance
  · infer_instance

/-- All static assembly call sites, as global indices and offsets after their calls. -/
def callReturnSites (program : Program) : List (Nat × Int) :=
  program.prog_defs.zipIdx.flatMap fun (definition, globalIndex) =>
    match definition.2 with
    | .Gfun (.Internal function) =>
        function.fn_code.zipIdx.filterMap fun (instruction, position) =>
          match instruction with
          | .Pcall_s _ _ | .Pcall_r _ _ => some (globalIndex, ((position + 1 : Nat) : Int))
          | _ => none
    | _ => []

namespace Imported

-- Kernel evaluation of `ReturnSiteMatches` on the sixteen rows against each imported program.
set_option maxRecDepth 100000 in
/-- For n = 1..10, every table row matches a call site of the imported assembly, by kernel
evaluation. -/
theorem return_sites_match (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    ∀ row ∈ Mach.ImportedAddresses.rows,
      ReturnSiteMatches (Mach.Imported.program n) (program n) row := by
  interval_cases n <;> decide +kernel

-- Kernel evaluation collecting every call site of each imported assembly program.
set_option maxRecDepth 100000 in
/-- For n = 1..10, the assembly call sites are exactly the table rows, in order, by kernel
evaluation. -/
theorem all_assembly_calls_recorded (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    callReturnSites (program n) =
      Mach.ImportedAddresses.rows.map (fun row => (row.globalIndex, row.offset)) := by
  interval_cases n <;> decide +kernel

end Imported

end Quadrature.Asm
