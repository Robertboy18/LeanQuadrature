import Quadrature.Compiler.Mach.Execution

/-!
# Finite return-address tables

A return-address oracle given by a table of (function, continuation, offset) rows. Read
`tableAddress` first, membership in the table. `lookupAddress` is the executable lookup,
comparing the whole function and continuation, and `consistentAddresses` makes lookup
complete for membership. The table used by the ten programs is related to the Lean
Asmgen translation's return addresses in `Asm/GeneratedReturnAddresses.lean`.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Mach

open CC

/-- A table entry: a function, its continuation after a call, and the return-address offset. -/
structure AddressEntry where
  function : Function
  continuation : Code
  offset : Integers.Ptrofs
  deriving DecidableEq

/-- A generated row: a zero-based global index, the number `skip` of Mach instructions before
the continuation, and the offset. -/
structure AddressRow where
  globalIndex : Nat
  skip : Nat
  offset : Int
  deriving DecidableEq

/-- The entry a row denotes in `program`: the internal function at `globalIndex`, its code
after `skip` instructions, and the offset. A row naming any other global gives no entry. -/
def entriesForRow (program : Program) (row : AddressRow) : List AddressEntry :=
  match program.prog_defs[row.globalIndex]? with
  | some (_, .Gfun (.Internal function)) =>
      [⟨function, function.fn_code.drop row.skip, Integers.Ptrofs.repr row.offset⟩]
  | _ => []

/-- The entries of all `rows` in `program`. -/
def addressTable (program : Program) (rows : List AddressRow) : List AddressEntry :=
  rows.flatMap (entriesForRow program)

/-- Finds the offset of the first entry whose function and continuation both match. -/
def lookupAddress : List AddressEntry → ReturnAddressExecutor
  | [], _, _ => none
  | entry :: rest, function, code =>
      if function = entry.function ∧ code = entry.continuation then some entry.offset
      else lookupAddress rest function code

/-- The oracle accepting exactly the offsets recorded in `entries`. -/
def tableAddress (entries : List AddressEntry) : ReturnAddress :=
  fun function code offset => ⟨function, code, offset⟩ ∈ entries

/-- Every offset found by `lookupAddress entries` is a member of `entries`. -/
theorem lookup_address_sound (entries : List AddressEntry) :
    ReturnAddressExecutorSound (lookupAddress entries) (tableAddress entries) := by
  intro function code offset h
  induction entries with
  | nil => cases h
  | cons entry rest ih =>
      simp only [lookupAddress] at h
      split at h
      · next heq =>
          obtain ⟨hf, hc⟩ := heq
          cases entry
          simp only at hf hc h
          cases hf
          cases hc
          cases h
          exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

/-- Every entry agrees with lookup, including entries shadowed by an earlier equal key. -/
def consistentAddresses (entries : List AddressEntry) : Bool :=
  entries.all fun entry =>
    decide (lookupAddress entries entry.function entry.continuation = some entry.offset)

/-- Under `hconsistent`, every member offset `h` is the one found by `lookupAddress`. -/
theorem lookup_address_complete {entries : List AddressEntry}
    (hconsistent : consistentAddresses entries = true)
    {function : Function} {code : Code} {offset : Integers.Ptrofs}
    (h : tableAddress entries function code offset) :
    lookupAddress entries function code = some offset := by
  have hall := List.all_eq_true.mp hconsistent
  exact of_decide_eq_true (hall ⟨function, code, offset⟩ h)

/-- Under `hconsistent`, lookup and membership agree. -/
theorem lookup_address_iff {entries : List AddressEntry}
    (hconsistent : consistentAddresses entries = true)
    {function : Function} {code : Code} {offset : Integers.Ptrofs} :
    lookupAddress entries function code = some offset ↔
      tableAddress entries function code offset :=
  ⟨lookup_address_sound entries function code offset,
    lookup_address_complete hconsistent⟩

/-- Under `hconsistent`, a function and continuation have at most one offset in the table. -/
theorem table_address_unique {entries : List AddressEntry}
    (hconsistent : consistentAddresses entries = true)
    {function : Function} {code : Code} {offset other : Integers.Ptrofs}
    (h : tableAddress entries function code offset)
    (hother : tableAddress entries function code other) : offset = other :=
  Option.some.inj ((lookup_address_complete hconsistent h).symm.trans
    (lookup_address_complete hconsistent hother))

end Quadrature.Mach
