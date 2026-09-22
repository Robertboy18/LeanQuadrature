import Quadrature.CSource.Semantics.Syntax

/-!
# Reads in the C expression semantics

`DerefLoc` adapts `Csem.deref_loc` of CompCert (revision recorded in
`Quadrature.Clight.Source`), keeping the volatile case with its observable
trace. `derefLoc_iff` relates the nonvolatile cases to CLean's Clight
`DerefLoc`. Clight represents volatile accesses by separate builtin
statements, so only nonvolatile types are bridged.
-/

namespace Quadrature.CSource.C

open CC

/-- `DerefLoc ge ty m b ofs bf trace v`: reading a value of type `ty` from block `b` at offset
`ofs` (bitfield designation `bf`) in memory `m` yields `v` with trace `trace`. By-value types
load a chunk (volatile ones through `VolatileLoad`, with a trace), by-reference and by-copy types
yield the address, and bitfields use `LoadBitfield`. -/
inductive DerefLoc (ge : ExpressionEnv) (ty : Ty) (m : Mem) (b : Block)
    (ofs : Integers.Ptrofs) : Bitfield → Trace → Val → Prop where
  | value (chunk v) :
      accessMode ty = .By_value chunk →
      typeIsVolatile ty = false →
      Mem.loadv chunk m (.Vptr b ofs) = some v →
      DerefLoc ge ty m b ofs .Full E0 v
  | volatile (chunk trace v) :
      accessMode ty = .By_value chunk →
      typeIsVolatile ty = true →
      VolatileLoad ge.symbols chunk m b ofs trace v →
      DerefLoc ge ty m b ofs .Full trace v
  | reference :
      accessMode ty = .By_reference →
      DerefLoc ge ty m b ofs .Full E0 (.Vptr b ofs)
  | copy :
      accessMode ty = .By_copy →
      DerefLoc ge ty m b ofs .Full E0 (.Vptr b ofs)
  | bitfield (sz sg pos width v) :
      Cop.LoadBitfield ty sz sg pos width m (.Vptr b ofs) v →
      DerefLoc ge ty m b ofs (.Bits sz sg pos width) E0 v

/-- For a nonvolatile type, the C read relation holds exactly when the trace is empty and CLean's
Clight `DerefLoc` holds. -/
theorem derefLoc_iff {ge : ExpressionEnv} {ty : Ty} {m : Mem} {b : Block}
    {ofs : Integers.Ptrofs} {bf : Bitfield} {trace : Trace} {v : Val}
    (hv : typeIsVolatile ty = false) :
    DerefLoc ge ty m b ofs bf trace v ↔
      trace = E0 ∧ CC.DerefLoc ty m b ofs bf v := by
  constructor
  · intro h
    cases h with
    | value chunk v ha _ hl => exact ⟨rfl, .value chunk v ha hl⟩
    | volatile chunk trace v _ ht _ => simp [hv] at ht
    | reference ha => exact ⟨rfl, .reference ha⟩
    | copy ha => exact ⟨rfl, .copy ha⟩
    | bitfield sz sg pos width v hl => exact ⟨rfl, .bitfield sz sg pos width v hl⟩
  · rintro ⟨rfl, h⟩
    cases h with
    | value chunk v ha hl => exact .value chunk v ha hv hl
    | reference ha => exact .reference ha
    | copy ha => exact .copy ha
    | bitfield sz sg pos width v hl => exact .bitfield sz sg pos width v hl

/-- A Clight read of a nonvolatile type is a silent C read. -/
theorem derefLoc_of_clight {ge : ExpressionEnv} {ty : Ty} {m : Mem} {b : Block}
    {ofs : Integers.Ptrofs} {bf : Bitfield} {v : Val}
    (hv : typeIsVolatile ty = false) (h : CC.DerefLoc ty m b ofs bf v) :
    DerefLoc ge ty m b ofs bf E0 v :=
  (derefLoc_iff hv).mpr ⟨rfl, h⟩

end Quadrature.CSource.C
