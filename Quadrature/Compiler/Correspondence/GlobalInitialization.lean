import CCLib.Globalenvs

/-!
# Global initialization and function-body changes

Lemmas showing that global initialization depends only on symbol addresses and variable
initializers, so changing a function body leaves initial memory unchanged. Read
`alloc_globals_symbols_congr` first: two environments with the same symbol table allocate
the same globals identically. `GlobalMemory` uses these to relate the ten Cminor programs,
which differ only in the body of `main`, without evaluating the initializers' byte stores.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Compiler

open CC

variable {F V : Type} {source target : Genv F V}

/-- Changing the last definition's body cannot change any symbol address. -/
theorem add_globals_last_symbols (ge : Genv F V)
    (globals : List (Ident × GlobDef F V)) (id : Ident) (firstDef lastDef : GlobDef F V) :
    (Genv.addGlobals ge (globals ++ [(id, firstDef)])).genv_symb =
      (Genv.addGlobals ge (globals ++ [(id, lastDef)])).genv_symb := by
  simp only [Genv.addGlobals, List.foldl_append, List.foldl_cons, List.foldl_nil,
    Genv.addGlobal]

/-- Storing one initializer depends only on the symbol table `hs`. -/
theorem store_init_data_symbols_congr (hs : source.genv_symb = target.genv_symb)
    (m : Mem) (b : Block) (ofs : Z) (data : InitData) :
    Genv.storeInitData source m b ofs data = Genv.storeInitData target m b ofs data := by
  cases data <;> first | rfl | simp only [Genv.storeInitData, Genv.findSymbol, hs]

/-- Storing an initializer list depends only on the symbol table `hs`. -/
theorem store_init_data_list_symbols_congr (hs : source.genv_symb = target.genv_symb)
    (m : Mem) (b : Block) (ofs : Z) (data : List InitData) :
    Genv.storeInitDataList source m b ofs data =
      Genv.storeInitDataList target m b ofs data := by
  induction data generalizing m ofs with
  | nil => rfl
  | cons item rest ih =>
      simp only [Genv.storeInitDataList, store_init_data_symbols_congr hs]
      cases Genv.storeInitData target m b ofs item with
      | none => rfl
      | some m' => exact ih m' (ofs + item.size)

/-- Allocating one global depends only on the symbol table `hs`. -/
theorem alloc_global_symbols_congr (hs : source.genv_symb = target.genv_symb)
    (m : Mem) (global : Ident × GlobDef F V) :
    Genv.allocGlobal source m global = Genv.allocGlobal target m global := by
  rcases global with ⟨id, definition⟩
  cases definition with
  | Gfun => rfl
  | Gvar gv =>
      simp only [Genv.allocGlobal, store_init_data_list_symbols_congr hs]

/-- Allocating a list of globals depends only on the symbol table `hs`. -/
theorem alloc_globals_symbols_congr (hs : source.genv_symb = target.genv_symb)
    (m : Mem) (globals : List (Ident × GlobDef F V)) :
    Genv.allocGlobals source m globals = Genv.allocGlobals target m globals := by
  induction globals generalizing m with
  | nil => rfl
  | cons global rest ih =>
      simp only [Genv.allocGlobals, alloc_global_symbols_congr hs]
      cases Genv.allocGlobal target m global with
      | none => rfl
      | some m' => exact ih m'

/-- Allocating a concatenated list allocates the first part, then the second. -/
theorem alloc_globals_append (ge : Genv F V) (m : Mem)
    (firstGlobals lastGlobals : List (Ident × GlobDef F V)) :
    Genv.allocGlobals ge m (firstGlobals ++ lastGlobals) =
      (Genv.allocGlobals ge m firstGlobals).bind
        (fun m' => Genv.allocGlobals ge m' lastGlobals) := by
  induction firstGlobals generalizing m with
  | nil => rfl
  | cons global rest ih =>
      simp only [List.cons_append, Genv.allocGlobals]
      cases Genv.allocGlobal ge m global with
      | none => rfl
      | some m' => exact ih m'

end Quadrature.Compiler
