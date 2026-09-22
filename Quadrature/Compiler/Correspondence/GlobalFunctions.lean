import Quadrature.Compiler.Correspondence.GlobalMemory
import Quadrature.Compiler.Correspondence.ValueRelation

/-!
# Global addresses and function lookup across Clight and Cminor

Relates function lookup in the Clight and Cminor programs under `globalBlockMap` and
`globalIdentMap`. Read `global_callee_signatures` first: values related by `ValuesAgree`
resolve to functions with the same signature, or both fail to resolve, covering table
addresses, non-pointer values, and nonzero offsets. `shared_global_addresses` shows the
two symbol environments produce related pointers after renaming.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Compiler

open CC

/-- Lower the Clight argument and return types to the signature used by Cminor. -/
def clightSignature : FunDef → Signature
  | .Internal f => signatureOfType (typeOfParams f.fn_params) f.fn_return f.fn_callconv
  | .External _ args result cc => signatureOfType args result cc

/-- Changing the final function body preserves lookup signatures at every block. -/
theorem add_globals_last_function_signature {F V : Type} (signature : F → Signature)
    (ge : Genv F V) (globals : List (Ident × GlobDef F V)) (id : Ident)
    (first last : F) (hsig : signature first = signature last) (b : Block) :
    (Genv.findFunctPtr (Genv.addGlobals ge (globals ++ [(id, .Gfun first)])) b).map
        signature =
      (Genv.findFunctPtr (Genv.addGlobals ge (globals ++ [(id, .Gfun last)])) b).map
        signature := by
  simp only [Genv.addGlobals, List.foldl_append, List.foldl_cons, List.foldl_nil]
  by_cases hb : (globals.foldl Genv.addGlobal ge).genv_next = b
  · subst b
    simp only [Genv.findFunctPtr, Genv.findDef, Genv.addGlobal, PTree.gss,
      Option.map_some, hsig]
  · simp only [Genv.findFunctPtr, Genv.findDef, Genv.addGlobal, PTree.gso _ _ _ _ hb]

/-- Function signatures at every block are the same in all Clight application programs, which
differ only in the body of `main`. -/
theorem clight_function_signatures_independent (n : Nat) (b : Block) :
    (Genv.findFunctPtr (Binary64.Clight.Application.program n).globalenv.genv_genv b).map
        clightSignature =
      (Genv.findFunctPtr (Binary64.Clight.Application.program 0).globalenv.genv_genv b).map
        clightSignature :=
  add_globals_last_function_signature clightSignature (Genv.emptyGenv [])
    Binary64.Clight.polynomialLibrary.prog_defs Binary64.Clight.Application.mainIdent
    (.Internal (Binary64.Clight.Application.mainFunction n))
    (.Internal (Binary64.Clight.Application.mainFunction 0)) rfl b

private def mainTarget (n : Nat) : Cminor.Fundef :=
  match h : (Cminor.Imported.mainDefinition n).2 with
  | .Gfun f => f
  | .Gvar _ => False.elim (by cases h)

private theorem target_definitions (n : Nat) :
    (Cminor.Imported.program n).prog_defs =
      (Cminor.Imported.program 0).prog_defs.take 72 ++
        [((Cminor.Imported.mainDefinition n).1, .Gfun (mainTarget n))] := rfl

/-- Function signatures at every block are the same in all imported Cminor programs, which
differ only in the body of `main`. -/
theorem cminor_function_signatures_independent (n : Nat) (b : Block) :
    (Genv.findFunctPtr (Cminor.Imported.program n).globalenv b).map
        Cminor.Fundef.signature =
      (Genv.findFunctPtr (Cminor.Imported.program 0).globalenv b).map
        Cminor.Fundef.signature := by
  unfold Cminor.Program.globalenv
  conv_lhs => rw [target_definitions n]
  conv_rhs => rw [target_definitions 0]
  exact add_globals_last_function_signature Cminor.Fundef.signature
    (Genv.emptyGenv (Cminor.Imported.program 0).prog_public)
    ((Cminor.Imported.program 0).prog_defs.take 72) (Positive.ofNat 22880918)
    (mainTarget n) (mainTarget 0) rfl b

-- Kernel evaluation of function lookup at the nine mapped block pairs.
set_option maxRecDepth 100000 in
/-- All mapped blocks agree on whether they contain a function and on its signature. -/
theorem global_function_signatures (n : Nat) {b b' : Block}
    (hb : globalBlockMap b = some b') :
    (Genv.findFunctPtr (Binary64.Clight.Application.program n).globalenv.genv_genv b).map
        clightSignature =
      (Genv.findFunctPtr (Cminor.Imported.program n).globalenv b').map
        Cminor.Fundef.signature := by
  rw [clight_function_signatures_independent, cminor_function_signatures_independent]
  rcases global_block_map_cases hb with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals decide +kernel

/-- Renamed callee values preserve successful lookup and its signature, as well as failure. -/
theorem global_callee_signatures (n : Nat) {source target : Val}
    (hv : ValuesAgree globalBlockMap source target) :
    (Genv.findFunct (Binary64.Clight.Application.program n).globalenv.genv_genv source).map
        clightSignature =
      (Genv.findFunct (Cminor.Imported.program n).globalenv target).map
        Cminor.Fundef.signature := by
  cases hv with
  | ptr ofs hb =>
    cases hoff : Integers.Ptrofs.eq ofs Integers.Ptrofs.zero <;>
      simp only [Genv.findFunct, hoff, Bool.false_eq_true, ite_false, ite_true]
    · rfl
    · exact global_function_signatures n hb
  | _ => rfl

/-- A source callee has a target definition with the required calling signature. -/
theorem global_callee_exists (n : Nat) {source target : Val} {fd : FunDef}
    (hv : ValuesAgree globalBlockMap source target)
    (hf : Genv.findFunct (Binary64.Clight.Application.program n).globalenv.genv_genv source =
      some fd) :
    ∃ fd', Genv.findFunct (Cminor.Imported.program n).globalenv target = some fd' ∧
      fd'.signature = clightSignature fd := by
  have h := global_callee_signatures n hv
  rw [hf, Option.map_some] at h
  exact Option.map_eq_some_iff.mp h.symm

/-- Every source global block `h` is mapped by `globalBlockMap`. -/
theorem shared_global_block_mapped {id : Ident} {b : Block}
    (h : (id, b) ∈ sharedGlobals) : ∃ b', globalBlockMap b = some b' := by
  simp only [sharedGlobals, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h
  all_goals cases h; exact ⟨_, rfl⟩

/-- The two symbol environments produce related pointers for every source global `h` after
identifier renaming. -/
theorem shared_global_addresses (n : Nat) {id : Ident} {b : Block}
    (h : (id, b) ∈ sharedGlobals) (ofs : Integers.Ptrofs) :
    ∃ id', globalIdentMap id = some id' ∧ ValuesAgree globalBlockMap
      (Genv.symbolAddress (Binary64.Clight.Application.program n).globalenv.genv_genv id ofs)
      (Genv.symbolAddress (Cminor.Imported.program n).globalenv id' ofs) := by
  obtain ⟨b', hb⟩ := shared_global_block_mapped h
  obtain ⟨hsource, htarget⟩ := shared_global_symbols n h
  rw [hb] at htarget
  obtain ⟨id', hid, htarget⟩ := Option.bind_eq_some_iff.mp htarget
  refine ⟨id', hid, ?_⟩
  simp only [Genv.symbolAddress, hsource, htarget]
  exact .ptr ofs hb

/-- Related addresses `hv` load equal values from the two initial memories. -/
theorem initialized_pointer_loads {source target : Val}
    (hv : ValuesAgree globalBlockMap source target) (chunk : Chunk) :
    Mem.loadv chunk Binary64.Clight.Application.entryMemory source =
      Mem.loadv chunk cminorEntryMemory target :=
  hv.loadv initialized_globals_agree chunk

end Quadrature.Compiler
