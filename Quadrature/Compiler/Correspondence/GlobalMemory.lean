import Quadrature.Clight.Main
import Quadrature.Compiler.Cminor.StoredPrograms
import Quadrature.Compiler.Correspondence.GlobalInitialization
import Quadrature.Compiler.Correspondence.MemoryRelation

/-!
# Initialized globals in the Clight and Cminor applications

Relates the initial memories of the Clight and Cminor programs by `BlocksAgree`. The Lean
Clight application has nine globals, and the imported Cminor program has 73, including
compiler builtins and unused library globals. Read `globalBlockMap` first, which pairs the
nine source globals with their target blocks, and `globalIdentMap`, the finite renaming
between the two identifier encodings. `initialized_globals_agree` checks both initial
memories and their mapped contents and permissions by kernel evaluation.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Compiler

open CC

/-- Every source global, paired with its block in declaration order. -/
def sharedGlobals : List (Ident × Block) :=
  [(Binary64.ClightSource._gauss_pts, Positive.ofNat 1),
   (Binary64.ClightSource._gauss_wts, Positive.ofNat 2),
   (Binary64.ClightSource._gauss_point, Positive.ofNat 3),
   (Binary64.ClightSource._gauss_weight, Positive.ofNat 4),
   (Binary64.ClightSource._integrate, Positive.ofNat 5),
   (Binary64.ClightSource._testfun, Positive.ofNat 6),
   (Binary64.ClightSource._integrate_testfun, Positive.ofNat 7),
   (Binary64.ClightSource._cos, Positive.ofNat 8),
   (Binary64.Clight.Application.mainIdent, Positive.ofNat 9)]

/-- The correspondence includes every declaration in the source application. -/
theorem shared_globals_complete (n : Nat) :
    (Binary64.Clight.Application.program n).prog_defs.map Prod.fst =
      sharedGlobals.map Prod.fst := rfl

/-- Map the tables, accessors, integrator, callbacks, and entry point by global position. -/
def globalBlockMap (b : Block) : Option Block :=
  if b = Positive.ofNat 1 then some (Positive.ofNat 60) else
  if b = Positive.ofNat 2 then some (Positive.ofNat 62) else
  if b = Positive.ofNat 3 then some (Positive.ofNat 61) else
  if b = Positive.ofNat 4 then some (Positive.ofNat 63) else
  if b = Positive.ofNat 5 then some (Positive.ofNat 70) else
  if b = Positive.ofNat 6 then some (Positive.ofNat 71) else
  if b = Positive.ofNat 7 then some (Positive.ofNat 72) else
  if b = Positive.ofNat 8 then some (Positive.ofNat 69) else
  if b = Positive.ofNat 9 then some (Positive.ofNat 73) else none

/-- Pairs each source identifier with the numeric identifier the target import uses for it. -/
def globalIdentMap (id : Ident) : Option Ident :=
  if id = Binary64.ClightSource._gauss_pts then some Cminor.Imported.global59.1 else
  if id = Binary64.ClightSource._gauss_wts then some Cminor.Imported.global61.1 else
  if id = Binary64.ClightSource._gauss_point then some Cminor.Imported.global60.1 else
  if id = Binary64.ClightSource._gauss_weight then some Cminor.Imported.global62.1 else
  if id = Binary64.ClightSource._integrate then some Cminor.Imported.global69.1 else
  if id = Binary64.ClightSource._testfun then some Cminor.Imported.global70.1 else
  if id = Binary64.ClightSource._integrate_testfun then some Cminor.Imported.global71.1 else
  if id = Binary64.ClightSource._cos then some Cminor.Imported.global68.1 else
  if id = Binary64.Clight.Application.mainIdent then some (Cminor.Imported.mainDefinition 0).1
  else none

/-- Even `cos` has different numeric identifiers in the two representations. -/
theorem cosine_identifiers_differ :
    Binary64.ClightSource._cos ≠ Cminor.Imported.global68.1 := by
  decide +kernel

/-- A mapped pair `h` is one of the nine listed block pairs. -/
theorem global_block_map_cases {b b' : Block} (h : globalBlockMap b = some b') :
    (b = Positive.ofNat 1 ∧ b' = Positive.ofNat 60) ∨
    (b = Positive.ofNat 2 ∧ b' = Positive.ofNat 62) ∨
    (b = Positive.ofNat 3 ∧ b' = Positive.ofNat 61) ∨
    (b = Positive.ofNat 4 ∧ b' = Positive.ofNat 63) ∨
    (b = Positive.ofNat 5 ∧ b' = Positive.ofNat 70) ∨
    (b = Positive.ofNat 6 ∧ b' = Positive.ofNat 71) ∨
    (b = Positive.ofNat 7 ∧ b' = Positive.ofNat 72) ∨
    (b = Positive.ofNat 8 ∧ b' = Positive.ofNat 69) ∨
    (b = Positive.ofNat 9 ∧ b' = Positive.ofNat 73) := by
  unfold globalBlockMap at h
  split_ifs at h <;> simp_all

/-- Distinct source globals remain distinct in the target. -/
theorem global_block_map_injective {b₁ b₂ b' : Block}
    (h₁ : globalBlockMap b₁ = some b') (h₂ : globalBlockMap b₂ = some b') : b₁ = b₂ := by
  rcases global_block_map_cases h₁ with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    rcases global_block_map_cases h₂ with h | h | h | h | h | h | h | h | h
    all_goals
      simp only [Positive.ofNat, Positive.ofNatAux] at h ⊢
      rcases h with ⟨rfl, h⟩
      first | rfl | contradiction

/-- The initial memory of the imported Cminor programs, taken from `Imported.program 0`. -/
def cminorEntryMemory : Mem := (Cminor.Imported.program 0).initMem.getD Mem.empty

private def cminorGlobalPrefix : List (Ident × GlobDef Cminor.Fundef Unit) :=
  (Cminor.Imported.program 0).prog_defs.take 72

private theorem cminor_global_definitions (n : Nat) :
    (Cminor.Imported.program n).prog_defs =
      cminorGlobalPrefix ++ [Cminor.Imported.mainDefinition n] := rfl

/-- All imported Cminor programs have the same symbol table. -/
theorem cminor_global_symbols_independent (n : Nat) :
    (Cminor.Imported.program n).globalenv.genv_symb =
      (Cminor.Imported.program 0).globalenv.genv_symb := by
  unfold Cminor.Program.globalenv
  rw [cminor_global_definitions n, cminor_global_definitions 0]
  exact add_globals_last_symbols _ cminorGlobalPrefix (Positive.ofNat 22880918) _ _

/-- Renamed symbols resolve to the corresponding blocks for every source declaration. -/
theorem shared_global_symbols (n : Nat) {id : Ident} {b : Block}
    (h : (id, b) ∈ sharedGlobals) :
    Genv.findSymbol (Binary64.Clight.Application.program n).globalenv.genv_genv id = some b ∧
    (globalIdentMap id).bind (Genv.findSymbol (Cminor.Imported.program n).globalenv) =
      globalBlockMap b := by
  simp only [sharedGlobals, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h
  all_goals
    cases h
    constructor
    · rfl
    · unfold Genv.findSymbol
      rw [cminor_global_symbols_independent]
      decide +kernel

/-- Every imported Cminor program has the initial memory of `Imported.program 0`, because the
programs differ only in the body of `main`. -/
theorem cminor_init_mem_independent (n : Nat) :
    (Cminor.Imported.program n).initMem = (Cminor.Imported.program 0).initMem := by
  unfold Cminor.Program.initMem
  rw [alloc_globals_symbols_congr (source := (Cminor.Imported.program n).globalenv)
    (target := (Cminor.Imported.program 0).globalenv) (cminor_global_symbols_independent n)]
  rw [cminor_global_definitions n, cminor_global_definitions 0,
    alloc_globals_append, alloc_globals_append]
  apply congrArg (fun continuation =>
    (Genv.allocGlobals (Cminor.Imported.program 0).globalenv Mem.empty cminorGlobalPrefix).bind
      continuation)
  funext memory
  rfl

/-- Initialization of `Imported.program 0` succeeds, extracted from the checked execution of the
one-node program. -/
theorem cminor_program_initializes : (Cminor.Imported.program 0).initMem.isSome = true := by
  have h := Cminor.StoredPrograms.execution_checked 1 (by decide) (by decide)
  simp only [Cminor.executeProgram, Cminor.initialState, bind,
    Option.bind_eq_some_iff] at h
  obtain ⟨_, ⟨memory, hmemory, _⟩, _⟩ := h
  rw [cminor_init_mem_independent] at hmemory
  rw [hmemory]
  rfl

/-- Every imported Cminor program initializes to `cminorEntryMemory`. -/
theorem cminor_program_initialized (n : Nat) :
    (Cminor.Imported.program n).initMem = some cminorEntryMemory := by
  rw [cminor_init_mem_independent]
  have h := cminor_program_initializes
  unfold cminorEntryMemory
  cases hm : (Cminor.Imported.program 0).initMem <;> simp_all

-- Kernel evaluation of the Cminor initial memory's block count.
set_option maxRecDepth 100000 in
/-- The Cminor initial memory has 73 allocated blocks, by kernel evaluation. -/
theorem cminor_entry_nextblock : cminorEntryMemory.nextblock = Positive.ofNat 74 := by
  decide +kernel

-- Kernel evaluation of the Clight initial memory's block count.
set_option maxRecDepth 20000 in
/-- The Clight initial memory has nine allocated blocks, by kernel evaluation. -/
theorem clight_entry_nextblock :
    Binary64.Clight.Application.entryMemory.nextblock = Positive.ofNat 10 := by
  decide +kernel

-- Kernel evaluation comparing contents and permissions of the nine mapped blocks in both memories.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
private theorem mapped_initial_blocks {b b' : Block} (hb : globalBlockMap b = some b') :
    b < Binary64.Clight.Application.entryMemory.nextblock ∧
    b' < cminorEntryMemory.nextblock ∧
    PMap.get b Binary64.Clight.Application.entryMemory.contents =
      PMap.get b' cminorEntryMemory.contents ∧
    PMap.get b Binary64.Clight.Application.entryMemory.access =
      PMap.get b' cminorEntryMemory.access := by
  rcases global_block_map_cases hb with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    rw [clight_entry_nextblock, cminor_entry_nextblock]
    exact ⟨by decide, by decide, rfl, rfl⟩

/-- The nine source globals have equal contents and permissions in the two initial memories. -/
theorem initialized_globals_agree :
    BlocksAgree globalBlockMap Binary64.Clight.Application.entryMemory cminorEntryMemory where
  source_valid hb := (mapped_initial_blocks hb).1
  target_valid hb := (mapped_initial_blocks hb).2.1
  contents hb := (mapped_initial_blocks hb).2.2.1
  access hb := (mapped_initial_blocks hb).2.2.2

/-- The initial memories used in the relation are produced by both programs themselves. -/
theorem programs_initialize_related (n : Nat) :
    (Binary64.Clight.Application.program n).initMem =
        some Binary64.Clight.Application.entryMemory ∧
    (Cminor.Imported.program n).initMem = some cminorEntryMemory ∧
    BlocksAgree globalBlockMap Binary64.Clight.Application.entryMemory cminorEntryMemory :=
  ⟨Binary64.Clight.Application.program_initialized n, cminor_program_initialized n,
    initialized_globals_agree⟩

/-- Loads from mapped global blocks `hb` agree in the two initial memories. -/
theorem initialized_loads_agree {b b' : Block} (hb : globalBlockMap b = some b')
    (chunk : Chunk) (ofs : Z) :
    Mem.load chunk Binary64.Clight.Application.entryMemory b ofs =
      Mem.load chunk cminorEntryMemory b' ofs :=
  initialized_globals_agree.load hb chunk ofs

end Quadrature.Compiler
