import Quadrature.CSource.Frontend.Refinement
import Quadrature.CSource.Semantics.GlobalInitialization

/-!
# Preservation after initialization and function lookup

`InitializedRefinement` resolves the same exported function in the C library
and its normalized Clight program, starting from their actual initializers.
`InitializedRefinement.outcomes_iff` then compares calls by exported name;
the caller need not supply a function body, table memory or symbol map.
-/

namespace Quadrature.CSource

open CC

variable [ExternalCalls]

/-- An observable result of initializing a C library and calling an exported function.
The execution permits every operand evaluation order in the C small-step semantics. -/
def C.Library.InitializedOutcome (library : C.Library) (name : Ident)
    (args : List Val) (trace : Trace) (value : Val) : Prop :=
  ∃ memory block function final,
    library.initMem = some memory ∧
    Genv.findSymbol library.globalEnv.globals name = some block ∧
    Genv.findFunct library.globalEnv.globals (.Vptr block Integers.Ptrofs.zero) = some function ∧
    C.SmallStep.CallOutcome library.globalEnv memory function args trace value final

/-- An observable result of initializing a Clight program and calling an exported function. -/
def ClightOutcome (program : CC.Program) (name : Ident)
    (args : List Val) (trace : Trace) (value : Val) : Prop :=
  ∃ memory block function final,
    program.initMem = some memory ∧
    Genv.findSymbol program.globalenv.genv_genv name = some block ∧
    Genv.findFunct program.globalenv.genv_genv (.Vptr block Integers.Ptrofs.zero) = some function ∧
    Star (Step2 program.globalenv) (.Callstate function args .Kstop memory)
      trace (.Returnstate value .Kstop final)

/-- Once initialization and lookup succeed, a named C outcome is precisely a call outcome. -/
theorem C.Library.initialized_outcome_iff {library : C.Library} {name : Ident}
    {memory : Mem} {block : Block} {function : C.FunDef}
    (hinit : library.initMem = some memory)
    (hsymbol : Genv.findSymbol library.globalEnv.globals name = some block)
    (hfunction : Genv.findFunct library.globalEnv.globals
      (.Vptr block Integers.Ptrofs.zero) = some function)
    (args : List Val) (trace : Trace) (value : Val) :
    library.InitializedOutcome name args trace value ↔
      ∃ final,
        C.SmallStep.CallOutcome library.globalEnv memory function args trace value final := by
  simp only [InitializedOutcome, hinit, Option.some.injEq, exists_and_left, exists_eq_left',
    hsymbol, hfunction]

/-- Once initialization and lookup succeed, a named Clight outcome is precisely a call trace. -/
theorem clight_outcome_iff {program : CC.Program} {name : Ident}
    {memory : Mem} {block : Block} {function : CC.FunDef}
    (hinit : program.initMem = some memory)
    (hsymbol : Genv.findSymbol program.globalenv.genv_genv name = some block)
    (hfunction : Genv.findFunct program.globalenv.genv_genv
      (.Vptr block Integers.Ptrofs.zero) = some function)
    (args : List Val) (trace : Trace) (value : Val) :
    ClightOutcome program name args trace value ↔
      ∃ final, Star (Step2 program.globalenv) (.Callstate function args .Kstop memory)
        trace (.Returnstate value .Kstop final) := by
  simp only [ClightOutcome, hinit, Option.some.injEq, exists_and_left, exists_eq_left',
    hsymbol, hfunction]

/-- Both initializers succeed with the same memory, and both symbol maps select functions
whose calls satisfy behavioral preservation. -/
def InitializedRefinement (library : C.Library) (program : CC.Program)
    (name : Ident) (args : List Val) (result : Val) : Prop :=
  ∃ memory block sourceFunction targetFunction,
    library.initMem = some memory ∧
    program.initMem = some memory ∧
    Genv.findSymbol library.globalEnv.globals name = some block ∧
    Genv.findSymbol program.globalenv.genv_genv name = some block ∧
    Genv.findFunct library.globalEnv.globals (.Vptr block Integers.Ptrofs.zero) =
      some sourceFunction ∧
    Genv.findFunct program.globalenv.genv_genv (.Vptr block Integers.Ptrofs.zero) =
      some targetFunction ∧
    CallRefinement library.globalEnv program memory sourceFunction targetFunction args result

/-- The initialized C function really returns, and its value and trace are uniquely specified. -/
theorem InitializedRefinement.source_outcome_iff {library : C.Library} {program : CC.Program}
    {name : Ident} {args : List Val} {result : Val}
    (h : InitializedRefinement library program name args result) (trace : Trace) (value : Val) :
    library.InitializedOutcome name args trace value ↔ trace = E0 ∧ value = result := by
  obtain ⟨memory, block, sourceFunction, targetFunction,
    hsourceInit, _, hsourceSymbol, _, hsourceFunction, _, hcall⟩ := h
  exact (C.Library.initialized_outcome_iff hsourceInit hsourceSymbol hsourceFunction
    args trace value).trans (hcall.source_correct.outcome_iff trace value)

/-- The initialized Clight function has the same unique value and trace as the C function. -/
theorem InitializedRefinement.target_outcome_iff {library : C.Library} {program : CC.Program}
    {name : Ident} {args : List Val} {result : Val}
    (h : InitializedRefinement library program name args result) (trace : Trace) (value : Val) :
    ClightOutcome program name args trace value ↔ trace = E0 ∧ value = result := by
  obtain ⟨memory, block, sourceFunction, targetFunction,
    _, htargetInit, _, htargetSymbol, _, htargetFunction, hcall⟩ := h
  exact (clight_outcome_iff htargetInit htargetSymbol htargetFunction
    args trace value).trans (hcall.target_outcome_iff trace value)

/-- Initialization and lookup preserve and reflect every returned value and trace. -/
theorem InitializedRefinement.outcomes_iff {library : C.Library} {program : CC.Program}
    {name : Ident} {args : List Val} {result : Val}
    (h : InitializedRefinement library program name args result) (trace : Trace) (value : Val) :
    library.InitializedOutcome name args trace value ↔
      ClightOutcome program name args trace value :=
  (h.source_outcome_iff trace value).trans (h.target_outcome_iff trace value).symm

end Quadrature.CSource
