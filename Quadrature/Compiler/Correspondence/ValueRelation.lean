import Quadrature.Compiler.Cminor.Semantics
import Quadrature.Compiler.Correspondence.MemoryRelation

/-!
# Values under block renaming

The value relation used to compare Clight and Cminor executions of the ten programs. Read
`ValuesAgree` first: numeric values are preserved exactly, a mapped pointer changes only its
block, and `Vundef` corresponds only to `Vundef`. The lemmas preserve argument types, 64-bit
address arithmetic, float addition and multiplication, and unsigned 64-bit comparison.
Pointer subtraction and comparison need an injective block map, and comparison also uses
`BlocksAgree` for pointer validity, including one-past-the-end pointers.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Compiler

open CC

/-- Two mapped source blocks cannot share a target block. Unmapped blocks are unrestricted. -/
def BlockMap.Injective (mapping : BlockMap) : Prop :=
  ∀ ⦃b₁ b₂ b'⦄, mapping b₁ = some b' → mapping b₂ = some b' → b₁ = b₂

/-- Under an injective map `hinj`, mapped blocks `hb` and `hc` are equal exactly when their
images are. -/
theorem BlockMap.Injective.eq_iff {mapping : BlockMap} (hinj : mapping.Injective)
    {b c b' c' : Block} (hb : mapping b = some b') (hc : mapping c = some c') :
    b = c ↔ b' = c' := by
  constructor
  · rintro rfl
    exact Option.some.inj (hb.symm.trans hc)
  · rintro rfl
    exact hinj hb hc

/-- Preserve numeric values and pointer offsets, renaming only mapped blocks. -/
inductive ValuesAgree (mapping : BlockMap) : Val → Val → Prop where
  | undef : ValuesAgree mapping .Vundef .Vundef
  | int (n : Integers.Int) : ValuesAgree mapping (.Vint n) (.Vint n)
  | long (n : Integers.Int64) : ValuesAgree mapping (.Vlong n) (.Vlong n)
  | float (f : Floats.Float) : ValuesAgree mapping (.Vfloat f) (.Vfloat f)
  | single (f : Floats.Float32) : ValuesAgree mapping (.Vsingle f) (.Vsingle f)
  | ptr {b b' : Block} (ofs : Integers.Ptrofs) :
      mapping b = some b' → ValuesAgree mapping (.Vptr b ofs) (.Vptr b' ofs)

namespace ValuesAgree

variable {mapping : BlockMap} {source target left right left' right' : Val}

/-- A source value has at most one related target value. -/
theorem functional (h : ValuesAgree mapping source target)
    (h' : ValuesAgree mapping source right') : target = right' := by
  cases h <;> cases h' <;> simp_all

/-- Related values have the same machine types. -/
theorem has_type (h : ValuesAgree mapping source target) (ty : ATyp) :
    Val.hasType source ty = Val.hasType target ty := by
  cases h <;> cases ty <;> rfl

/-- Related values satisfy the same argument types. -/
theorem has_arg_type (h : ValuesAgree mapping source target) (ty : XType) :
    Cminor.HasArgType source ty ↔ Cminor.HasArgType target ty := by
  cases h <;> cases ty <;> rfl

/-- Pointwise related lists satisfy the same argument type lists. -/
theorem has_arg_types {sources targets : List Val}
    (h : List.Forall₂ (ValuesAgree mapping) sources targets) (types : List XType) :
    Cminor.HasArgTypes sources types ↔ Cminor.HasArgTypes targets types := by
  induction h generalizing types with
  | nil => rfl
  | cons hv hvs ih =>
    cases types with
    | nil => simp [Cminor.HasArgTypes]
    | cons ty types =>
      simpa only [Cminor.HasArgTypes, List.forall₂_cons] using
        and_congr (hv.has_arg_type ty) (ih types)

/-- Offsetting related values by the same amount keeps them related. -/
theorem offset_ptr (h : ValuesAgree mapping source target) (ofs : Integers.Ptrofs) :
    ValuesAgree mapping (Val.offsetPtr source ofs) (Val.offsetPtr target ofs) := by
  cases h <;> constructor
  assumption

/-- 64-bit addition of related operands gives related results. -/
theorem addl (hl : ValuesAgree mapping left left') (hr : ValuesAgree mapping right right') :
    ValuesAgree mapping (Val.addl left right) (Val.addl left' right') := by
  cases hl <;> cases hr <;>
    simp only [Val.addl, Archi.ptr64, ite_true] <;> constructor <;> assumption

/-- 64-bit subtraction of related operands gives related results under an injective map `hinj`. -/
theorem subl (hinj : mapping.Injective)
    (hl : ValuesAgree mapping left left') (hr : ValuesAgree mapping right right') :
    ValuesAgree mapping (Val.subl left right) (Val.subl left' right') := by
  cases hl <;> cases hr <;>
    simp only [Val.subl, Archi.ptr64, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
  all_goals first | exact .undef | exact .long _ | exact .ptr _ (by assumption) | skip
  rename_i b b' ofs hb c c' delta hc
  by_cases hbc : b = c
  · simp only [hbc, (hinj.eq_iff hb hc).mp hbc, ite_true]
    exact .long _
  · have hbc' : b' ≠ c' := fun heq => hbc ((hinj.eq_iff hb hc).mpr heq)
    simp only [hbc, hbc', ite_false]
    exact .undef

/-- All comparison outcomes agree, including failures for invalid pointers. -/
theorem cmplu_bool {sourceMemory targetMemory : Mem}
    (hm : BlocksAgree mapping sourceMemory targetMemory) (hinj : mapping.Injective)
    (hl : ValuesAgree mapping left left') (hr : ValuesAgree mapping right right')
    (comparison : Comparison) :
    Val.cmplu_bool (Mem.validPointer sourceMemory) comparison left right =
      Val.cmplu_bool (Mem.validPointer targetMemory) comparison left' right' := by
  cases hl <;> cases hr <;> try rfl
  all_goals simp only [Val.cmplu_bool, Val.weakValidPtr]
  case long.ptr n b b' ofs hb =>
    simp only [hm.valid_pointer hb]
    rfl
  case ptr.long b b' ofs hb n =>
    simp only [hm.valid_pointer hb]
    rfl
  case ptr.ptr b b' ofs hb c c' delta hc =>
    simp only [hm.valid_pointer hb, hm.valid_pointer hc, hinj.eq_iff hb hc]
    rfl

/-- Float addition of related operands gives related results. -/
theorem addf (hl : ValuesAgree mapping left left') (hr : ValuesAgree mapping right right') :
    ValuesAgree mapping (Val.addf left right) (Val.addf left' right') := by
  cases hl <;> cases hr <;> constructor

/-- Float multiplication of related operands gives related results. -/
theorem mulf (hl : ValuesAgree mapping left left') (hr : ValuesAgree mapping right right') :
    ValuesAgree mapping (Val.mulf left right) (Val.mulf left' right') := by
  cases hl <;> cases hr <;> constructor

/-- Related addresses give equal loads, including unsuccessful loads and non-pointer inputs. -/
theorem loadv {sourceMemory targetMemory : Mem}
    (hm : BlocksAgree mapping sourceMemory targetMemory)
    (h : ValuesAgree mapping source target) (chunk : Chunk) :
    Mem.loadv chunk sourceMemory source = Mem.loadv chunk targetMemory target := by
  cases h with
  | ptr ofs hb => exact hm.load hb chunk (Integers.Ptrofs.unsigned ofs)
  | _ => rfl

end ValuesAgree

end Quadrature.Compiler
