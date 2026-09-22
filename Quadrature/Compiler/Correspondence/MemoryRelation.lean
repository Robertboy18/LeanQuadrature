import CCLib.MemoryLemmas

/-!
# Agreement of memory blocks across the compiler boundary

The memory relation used to compare Clight and Cminor executions of the ten programs. Read
`BlocksAgree` first: mapped blocks are allocated on both sides and have identical byte
contents and permissions. The relation preserves loads and survives allocation, freeing,
and stores outside the mapped blocks. It compares contents byte for byte, which suits the
numeric tables the programs read.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Compiler

open CC

/-- A partial correspondence between source and target block identifiers. -/
abbrev BlockMap := Block → Option Block

/-- Mapped blocks are allocated and have identical byte contents and permissions. -/
structure BlocksAgree (mapping : BlockMap) (source target : Mem) : Prop where
  source_valid : ∀ {b b'}, mapping b = some b' → b < source.nextblock
  target_valid : ∀ {b b'}, mapping b = some b' → b' < target.nextblock
  contents : ∀ {b b'}, mapping b = some b' →
    PMap.get b source.contents = PMap.get b' target.contents
  access : ∀ {b b'}, mapping b = some b' →
    PMap.get b source.access = PMap.get b' target.access

namespace BlocksAgree

variable {mapping : BlockMap} {source target : Mem} {b b' : Block}

/-- Permissions agree at every offset of a mapped block `hb`. -/
theorem perm (h : BlocksAgree mapping source target) (hb : mapping b = some b')
    (ofs : Z) (k : PermKind) (p : Permission) :
    Mem.perm source b ofs k p = Mem.perm target b' ofs k p := by
  simp only [Mem.perm, h.access hb]

/-- Range permissions agree on a mapped block `hb`. -/
theorem range_perm (h : BlocksAgree mapping source target) (hb : mapping b = some b')
    (lo hi : _root_.Int) (k : PermKind) (p : Permission) :
    Mem.rangePerm source b lo hi k p = Mem.rangePerm target b' lo hi k p := by
  cases ht : Mem.rangePerm target b' lo hi k p
  · cases hs : Mem.rangePerm source b lo hi k p
    · rfl
    · have htrue := Mem.rangePerm_intro target b' lo hi k p (fun ofs hlo hhi => by
        rw [← h.perm hb]
        exact Mem.rangePerm_perm source b lo hi k p hs ofs hlo hhi)
      simp [ht] at htrue
  · exact Mem.rangePerm_intro source b lo hi k p (fun ofs hlo hhi => by
      rw [h.perm hb]
      exact Mem.rangePerm_perm target b' lo hi k p ht ofs hlo hhi)

/-- Access validity agrees on a mapped block `hb`. -/
theorem valid_access (h : BlocksAgree mapping source target) (hb : mapping b = some b')
    (chunk : Chunk) (ofs : Z) (p : Permission) :
    Mem.validAccess source chunk b ofs p = Mem.validAccess target chunk b' ofs p := by
  simp only [Mem.validAccess, h.range_perm hb]

/-- Loads agree at any offset, including unsuccessful and misaligned loads. -/
theorem load (h : BlocksAgree mapping source target) (hb : mapping b = some b')
    (chunk : Chunk) (ofs : Z) :
    Mem.load chunk source b ofs = Mem.load chunk target b' ofs := by
  simp only [Mem.load, h.valid_access hb, h.contents hb]

/-- Byte loads agree on a mapped block `hb`. -/
theorem loadbytes (h : BlocksAgree mapping source target) (hb : mapping b = some b')
    (ofs n : Z) :
    Mem.loadbytes source b ofs n = Mem.loadbytes target b' ofs n := by
  simp only [Mem.loadbytes, h.range_perm hb, h.contents hb]

/-- Pointer validity agrees on a mapped block `hb`. -/
theorem valid_pointer (h : BlocksAgree mapping source target) (hb : mapping b = some b')
    (ofs : Z) :
    Mem.validPointer source b ofs = Mem.validPointer target b' ofs := by
  exact h.perm hb ofs .Cur .Nonempty

/-- Weak pointer validity, allowing one past the end, agrees on a mapped block `hb`. -/
theorem weak_valid_pointer (h : BlocksAgree mapping source target)
    (hb : mapping b = some b') (ofs : Z) :
    Mem.weakValidPointer source b ofs = Mem.weakValidPointer target b' ofs := by
  simp only [Mem.weakValidPointer, h.valid_pointer hb]

/-- A mapped target block `hb` is already allocated, so it differs from the next block. -/
theorem target_ne_nextblock (h : BlocksAgree mapping source target)
    (hb : mapping b = some b') : b' ≠ target.nextblock := by
  intro heq
  have hv := h.target_valid hb
  rw [heq, Positive.lt_iff] at hv
  exact Nat.lt_irrefl _ hv

/-- A fresh target allocation cannot overwrite any mapped block. -/
theorem alloc_target (h : BlocksAgree mapping source target) (lo hi : Z) :
    BlocksAgree mapping source (Mem.alloc target lo hi).1 where
  source_valid := h.source_valid
  target_valid hb := by
    have hv := h.target_valid hb
    simp only [Mem.alloc_nextblock, Positive.lt_iff, Positive.toNat_succ] at *
    omega
  contents hb := by
    rw [Mem.alloc_contents, PMap.gso _ _ _ _ (h.target_ne_nextblock hb).symm]
    exact h.contents hb
  access hb := by
    rw [Mem.alloc_access, PMap.gso _ _ _ _ (h.target_ne_nextblock hb).symm]
    exact h.access hb

/-- Freeing a block outside the correspondence preserves every mapped block. -/
theorem unchecked_free_target (h : BlocksAgree mapping source target)
    (freed : Block) (lo hi : Z) (hunmapped : ∀ b, mapping b ≠ some freed) :
    BlocksAgree mapping source (Mem.uncheckedFree target freed lo hi) where
  source_valid := h.source_valid
  target_valid := h.target_valid
  contents := h.contents
  access {b b'} hb := by
    have hne : freed ≠ b' := by
      intro heq
      exact hunmapped b (heq.symm ▸ hb)
    simp only [Mem.uncheckedFree, PMap.gso _ _ _ _ hne]
    exact h.access hb

/-- Freeing an unmapped target block (`hfree`, `hunmapped`) preserves the relation. -/
theorem free_target (h : BlocksAgree mapping source target)
    {freed : Block} {lo hi : Z} {target' : Mem}
    (hfree : Mem.free target freed lo hi = some target')
    (hunmapped : ∀ b, mapping b ≠ some freed) :
    BlocksAgree mapping source target' := by
  rw [Mem.free_result hfree]
  exact h.unchecked_free_target freed lo hi hunmapped

/-- In particular, a frame allocated after the relation was established is unmapped. -/
theorem alloc_free_target (h : BlocksAgree mapping source target)
    (lo hi : Z) {target' : Mem}
    (hfree : Mem.free (Mem.alloc target lo hi).1 target.nextblock lo hi = some target') :
    BlocksAgree mapping source target' :=
  (h.alloc_target lo hi).free_target hfree
    (fun _ hb => h.target_ne_nextblock hb rfl)

/-- A fresh frame can be freed in full, including a frame of size zero. -/
theorem alloc_free_target_exists (h : BlocksAgree mapping source target)
    (lo hi : _root_.Int) :
    ∃ target', Mem.free (Mem.alloc target lo hi).1 target.nextblock lo hi = some target' ∧
      BlocksAgree mapping source target' ∧ target'.nextblock = target.nextblock.succ := by
  have hfree := Mem.free_isSome (Mem.rangePerm_intro (Mem.alloc target lo hi).1
    target.nextblock lo hi .Cur .Freeable (fun ofs hlo hhi =>
      Mem.perm_alloc_same target lo hi ofs .Cur hlo hhi))
  exact ⟨_, hfree, h.alloc_free_target lo hi hfree, rfl⟩

/-- A store `hstore` to an unmapped target block preserves the relation. -/
theorem store_target (h : BlocksAgree mapping source target)
    {chunk : Chunk} {stored : Block} {ofs : Z} {value : Val} {target' : Mem}
    (hstore : Mem.store chunk target stored ofs value = some target')
    (hunmapped : ∀ b, mapping b ≠ some stored) :
    BlocksAgree mapping source target' where
  source_valid := h.source_valid
  target_valid hb := by rw [Mem.store_nextblock hstore]; exact h.target_valid hb
  contents {b b'} hb := by
    have hne : stored ≠ b' := by
      intro heq
      exact hunmapped b (heq.symm ▸ hb)
    rw [Mem.store_contents hstore, PMap.gso _ _ _ _ hne]
    exact h.contents hb
  access hb := by rw [Mem.store_access hstore]; exact h.access hb

/-- A byte store `hstore` to an unmapped target block preserves the relation. -/
theorem storebytes_target (h : BlocksAgree mapping source target)
    {stored : Block} {ofs : Z} {bytes : List MemVal} {target' : Mem}
    (hstore : Mem.storebytes target stored ofs bytes = some target')
    (hunmapped : ∀ b, mapping b ≠ some stored) :
    BlocksAgree mapping source target' where
  source_valid := h.source_valid
  target_valid hb := by rw [Mem.storebytes_nextblock hstore]; exact h.target_valid hb
  contents {b b'} hb := by
    have hne : stored ≠ b' := by
      intro heq
      exact hunmapped b (heq.symm ▸ hb)
    rw [Mem.storebytes_contents hstore, PMap.gso _ _ _ _ hne]
    exact h.contents hb
  access hb := by rw [Mem.storebytes_access hstore]; exact h.access hb

end BlocksAgree

end Quadrature.Compiler
