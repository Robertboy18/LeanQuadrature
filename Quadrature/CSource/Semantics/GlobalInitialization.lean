import Quadrature.CSource.Semantics.Strategy

/-!
# Initializing a C library

A `Library` holds typed C global definitions, exported names and composite
types. `Library.globalEnv` installs the definitions in declaration order, and
`Library.initMem` allocates their storage and writes their initializers using
CLean's memory operations. There is no entry-point requirement: the quadrature
source is a library whose functions are called after initialization.
-/

namespace Quadrature.CSource.C

open CC

/-- Typed C globals with the names exported by a library and its composite environment. -/
structure Library where
  definitions : List (Ident × GlobDef FunDef Ty)
  publicNames : List Ident
  composites : CompositeEnv

/-- Assign blocks to the library's globals in declaration order. -/
def Library.globalEnv (library : Library) : GlobalEnv :=
  ⟨Genv.addGlobals (Genv.emptyGenv library.publicNames) library.definitions, library.composites⟩

/-- Allocate the globals, write their initializers and establish their final permissions. -/
def Library.initMem (library : Library) : Option Mem :=
  Genv.allocGlobals library.globalEnv.globals Mem.empty library.definitions

/-- Initialize the library, resolve an entry symbol to its actual function definition, and
execute that function with the supplied arguments. The returned memory and trace are explicit. -/
def Library.InitializedCall [ExternalCalls] (library : Library) (entry : Ident)
    (arguments : List Val) (trace : Trace) (final : Mem) (value : Val) : Prop :=
  ∃ initial block function,
    library.initMem = some initial ∧
    Genv.findSymbol library.globalEnv.globals entry = some block ∧
    Genv.findFunct library.globalEnv.globals (.Vptr block Integers.Ptrofs.zero) = some function ∧
    EvalFuncall library.globalEnv initial function arguments trace final value

end Quadrature.CSource.C
