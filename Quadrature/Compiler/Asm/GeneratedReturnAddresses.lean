import Mathlib.Data.List.Forall2
import Quadrature.Compiler.Asm.CallSites
import Quadrature.Compiler.Asm.Generation

/-!
# Generated continuations at the imported return addresses

The Lean Asmgen translation's return-address oracle and its relation to the Mach table.
Read `returnAddress` first: `returnAddress f k ofs` holds when the Lean Asmgen translation
of `f` succeeds and dropping `ofs` instructions from it is exactly the translation of `k`.
`Imported.program_translation` shows the translation of each imported Mach program is the
imported assembly program. `Imported.table_valid` shows every table entry satisfies
`returnAddress`. `Imported.table_address_iff` shows the table and the translation agree at
every static call of the ten programs, including calls in unused library functions.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Asm.Generation

open CC

/-- A Mach global and an assembly global correspond: internal functions by
`translateFunction`, external functions and variables by equality. -/
def DefinitionTranslation : GlobDef Mach.Fundef Unit → GlobDef Fundef Unit → Prop
  | .Gfun (.Internal source), .Gfun (.Internal target) =>
      translateFunction source = some target
  | .Gfun (.External source), .Gfun (.External target) => source = target
  | .Gvar source, .Gvar target =>
      source.gvar_info = target.gvar_info ∧ source.gvar_init = target.gvar_init ∧
      source.gvar_readonly = target.gvar_readonly ∧ source.gvar_volatile = target.gvar_volatile
  | _, _ => False

/-- Decidable by running the translation and comparing. -/
instance (source : GlobDef Mach.Fundef Unit) (target : GlobDef Fundef Unit) :
    Decidable (DefinitionTranslation source target) := by
  unfold DefinitionTranslation
  split <;> infer_instance

/-- Exact function translation, with global names, data, public symbols, and entry preserved. -/
def ProgramTranslation (source : Mach.Program) (target : Program) : Prop :=
  source.prog_public = target.prog_public ∧ source.prog_main = target.prog_main ∧
    List.Forall₂ (fun s t => s.1 = t.1 ∧ DefinitionTranslation s.2 t.2)
      source.prog_defs target.prog_defs

/-- Decidable definition by definition. -/
instance (source : Mach.Program) (target : Program) :
    Decidable (ProgramTranslation source target) := by
  unfold ProgramTranslation
  infer_instance

/-- The upper bound excludes offsets past the end, even when the continuation is empty. -/
def CodeTail (offset : Integers.Ptrofs) (body tail : Code) : Prop :=
  offset.toNat ≤ body.length ∧ body.drop offset.toNat = tail

/-- Decidable by dropping `offset` instructions and comparing. -/
instance (offset : Integers.Ptrofs) (body tail : Code) :
    Decidable (CodeTail offset body tail) := inferInstanceAs
  (Decidable (offset.toNat ≤ body.length ∧ body.drop offset.toNat = tail))

/-- `returnAddress f k ofs` holds when the translations of `f` and `k` both succeed and `ofs`
selects the translation of `k` as the tail of the translated body. -/
def returnAddress (function : Mach.Function) (continuation : Mach.Code)
    (offset : Integers.Ptrofs) : Prop :=
  match translateFunction function, code function continuation false with
  | some target, some tail => CodeTail offset target.fn_code tail
  | _, _ => False

/-- Decidable by running both translations. -/
instance (function : Mach.Function) (continuation : Mach.Code) (offset : Integers.Ptrofs) :
    Decidable (returnAddress function continuation offset) := by
  unfold returnAddress
  split <;> infer_instance

/-- Two offsets `h` and `hother` selecting the same tail of `body` are equal. -/
theorem code_tail_unique {body tail : Code} {offset other : Integers.Ptrofs}
    (h : CodeTail offset body tail) (hother : CodeTail other body tail) : offset = other := by
  have hlength := congrArg List.length h.2
  have hotherlength := congrArg List.length hother.2
  simp only [List.length_drop] at hlength hotherlength
  apply BitVec.eq_of_toNat_eq
  have := h.1
  have := hother.1
  omega

/-- A function and continuation have at most one return address under the translation. -/
theorem return_address_unique {function : Mach.Function} {continuation : Mach.Code}
    {offset other : Integers.Ptrofs}
    (h : returnAddress function continuation offset)
    (hother : returnAddress function continuation other) : offset = other := by
  unfold returnAddress at h hother
  split at h
  · next target tail hf hc =>
      simp only [hf, hc] at hother
      exact code_tail_unique h hother
  · contradiction

/-- A return address `h` selects the translated continuation `hc` as a tail of the translated
body `hf`. -/
theorem return_address_tail {function : Mach.Function} {continuation : Mach.Code}
    {offset : Integers.Ptrofs} {target : Function} {tail : Code}
    (h : returnAddress function continuation offset)
    (hf : translateFunction function = some target)
    (hc : code function continuation false = some tail) :
    CodeTail offset target.fn_code tail := by
  simpa only [returnAddress, hf, hc] using h

/-- Continuations immediately following static Mach calls. -/
def callContinuations : Mach.Code → List Mach.Code
  | [] => []
  | .Mcall _ _ :: tail => tail :: callContinuations tail
  | _ :: tail => callContinuations tail

/-- Whether the table has an entry for every continuation following a static call in every
internal function of `program`. -/
def callsCovered (entries : List Mach.AddressEntry) (program : Mach.Program) : Bool :=
  program.prog_defs.all fun definition =>
    match definition.2 with
    | .Gfun (.Internal function) =>
        (callContinuations function.fn_code).all fun continuation =>
          (Mach.lookupAddress entries function continuation).isSome
    | _ => true

/-- Under `hcovered`, the continuation `hc` of a call in the internal function `hf` has a table
offset. -/
theorem covered_call_has_address {entries : List Mach.AddressEntry} {program : Mach.Program}
    (hcovered : callsCovered entries program = true)
    {name : Ident} {function : Mach.Function} {continuation : Mach.Code}
    (hf : (name, .Gfun (.Internal function)) ∈ program.prog_defs)
    (hc : continuation ∈ callContinuations function.fn_code) :
    ∃ offset, Mach.lookupAddress entries function continuation = some offset := by
  have hfunction := List.all_eq_true.mp hcovered _ hf
  have hcall := List.all_eq_true.mp hfunction _ hc
  exact Option.isSome_iff_exists.mp hcall

namespace Imported

-- Kernel evaluation of `DefinitionTranslation` on the 72 globals shared by all ten programs.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem shared_definitions_translation :
    List.Forall₂ (fun s t => s.1 = t.1 ∧ DefinitionTranslation s.2 t.2)
      ((Mach.Imported.program 0).prog_defs.take 72)
      ((Asm.Imported.program 0).prog_defs.take 72) := by
  decide +kernel

private theorem mach_definitions (n : Nat) :
    (Mach.Imported.program n).prog_defs =
      (Mach.Imported.program 0).prog_defs.take 72 ++ [Mach.Imported.mainDefinition n] := rfl

private theorem asm_definitions (n : Nat) :
    (Asm.Imported.program n).prog_defs =
      (Asm.Imported.program 0).prog_defs.take 72 ++ [Asm.Imported.mainDefinition n] := rfl

-- Kernel evaluation of `DefinitionTranslation` on each program's main definition.
set_option maxRecDepth 100000 in
private theorem main_definition_translation (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    (Mach.Imported.mainDefinition n).1 = (Asm.Imported.mainDefinition n).1 ∧
      DefinitionTranslation (Mach.Imported.mainDefinition n).2
        (Asm.Imported.mainDefinition n).2 := by
  interval_cases n <;> decide +kernel

/-- Every global agrees, including all complete generated function bodies. -/
theorem program_translation (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    ProgramTranslation (Mach.Imported.program n) (Asm.Imported.program n) := by
  refine ⟨rfl, rfl, ?_⟩
  rw [mach_definitions, asm_definitions]
  exact List.rel_append shared_definitions_translation
    (.cons (main_definition_translation n hlo hhi) .nil)

-- Kernel evaluation of `returnAddress` on each of the sixteen entries of each program's table.
set_option maxRecDepth 100000 in
/-- For n = 1..10, every entry of the imported table is a return address of the Lean Asmgen
translation, by kernel evaluation. -/
theorem table_valid (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    ∀ entry ∈ Mach.ImportedAddresses.table n,
      returnAddress entry.function entry.continuation entry.offset := by
  interval_cases n <;> decide +kernel

-- Kernel evaluation of `callsCovered` on each program and its table.
set_option maxRecDepth 100000 in
/-- For n = 1..10, the imported table covers every static call of the n-node program, by kernel
evaluation. -/
theorem all_calls_covered (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    callsCovered (Mach.ImportedAddresses.table n) (Mach.Imported.program n) = true := by
  interval_cases n <;> decide +kernel

/-- For n = 1..10, every table offset `h` is a return address of the translation. -/
theorem table_address_sound (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10)
    {function : Mach.Function} {continuation : Mach.Code} {offset : Integers.Ptrofs}
    (h : Mach.ImportedAddresses.relation n function continuation offset) :
    returnAddress function continuation offset :=
  table_valid n hlo hhi ⟨function, continuation, offset⟩ h

/-- For n = 1..10, at every static call of the n-node program (`hf`, `hc`) the table and the
translation accept the same offsets. -/
theorem table_address_iff (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10)
    {name : Ident} {function : Mach.Function} {continuation : Mach.Code}
    (hf : (name, .Gfun (.Internal function)) ∈ (Mach.Imported.program n).prog_defs)
    (hc : continuation ∈ callContinuations function.fn_code) (offset : Integers.Ptrofs) :
    Mach.ImportedAddresses.relation n function continuation offset ↔
      returnAddress function continuation offset := by
  refine ⟨table_address_sound n hlo hhi, fun h => ?_⟩
  obtain ⟨known, hknown⟩ := covered_call_has_address (all_calls_covered n hlo hhi) hf hc
  have htable := (Mach.ImportedAddresses.predict_iff n hlo hhi).mp hknown
  have heq := return_address_unique (table_address_sound n hlo hhi htable) h
  simpa only [heq] using htable

end Imported

end Quadrature.Asm.Generation
