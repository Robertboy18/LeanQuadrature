import CCLib.ClightExecSound
import CCLib.Determinism

/-!
# Finite executions of Clight library calls

This file fixes the vocabulary used by every `Quadrature.Clight*` file and proves
the two generic lemmas behind their total-correctness packages.

Vocabulary. A *silent step* is a `CC.Step2` transition with the empty trace
`CC.E0`, and `CC.StarE0 R a b` is a finite run of silent `R`-steps from `a` to
`b`. `Callstate fd args k m` is CLean's state on entry to a function body,
`Returnstate v k m` its state after a return, and `Kstop` the empty
continuation, so `Returnstate v Kstop m` is a finished call. A *trace* is the
list of observable events emitted along a run. An *external-call contract* is
an explicit hypothesis on what an external function does, replacing CLean's
axioms about external functions. A *library context* (`LibraryContext` in
`Quadrature.Clight.Library`) packages the symbols, accessor bodies, table loads
and callback that a caller must provide. A *table cell* (`TableCells` in
`Quadrature.Clight.Loop`) says that for the j-th pair `(w, x)` of `terms` the
weights table holds `w` and the nodes table holds `x` at byte offset
`8 * tableOffset n (i + j)`, where `tableOffset n i = n(n-1)/2 + i`. Pairs are
(weight, node). `runCall` below is a fuel-bounded interpreter that drives
CLean's `doStep` with empty traces until `Returnstate v Kstop m`, and
`runCall_sound` turns a successful run into a `StarE0` execution.

The *total-correctness package* for a call is the six theorems named
`_prefix`, `_return_state`, `_return_eq`, `_return_memory`, `_progress` and
`_not_infinite`. Together they say every reachable state can finish, every
finished run returns the stated value and memory, and no run is infinite. Their
generic halves are `silent_execution_prefix` and `silent_execution_not_infinite`.
-/

namespace Quadrature.Binary64.Clight

/-- Two silent runs, from `a` to `b` and from `b` to `c`, compose into one from `a` to `c`. -/
theorem starE0_trans {R : CC.State → CC.Trace → CC.State → Prop} {a b c : CC.State}
    (h : CC.StarE0 R a b) (h' : CC.StarE0 R b c) : CC.StarE0 R a c := by
  induction h with
  | refl => exact h'
  | step x y _ hxy _ ih => exact .step x y c hxy (ih h')

/-- In the empty local environment `CC.emptyEnv`, a by-reference global `Evar id ty` evaluates to
`Vptr b 0` when `findSymbol` maps `id` to `b`. The empty environment guarantees that no local
variable shadows the global. -/
theorem global_reference (ge : CC.CGenv) (le : CC.TempEnv) (m : CC.Mem)
    (id : CC.Ident) (ty : CC.Ty) (b : CC.Block)
    (hty : CC.accessMode ty = .By_reference)
    (hsym : CC.Genv.findSymbol ge.genv_genv id = some b) :
    CC.doEvalExpr ge CC.emptyEnv le m (.Evar id ty) =
      some (.Vptr b CC.Integers.Ptrofs.zero) := by
  simp only [CC.doEvalExpr, CC.lvalOfVar, CC.emptyEnv, CC.PTree.gempty, hsym,
    CC.doDerefLoc, hty]

/-- An `Scall` statement steps silently into `Callstate fd vargs (Kcall ...)` once the callee
expression, the arguments and the function lookup are supplied. The callee and arguments come
from the executable evaluators, so a call whose target is fixed by a hypothesis can be stepped. -/
theorem call_step [CC.ExternalCalls]
    {ge : CC.CGenv} {fn : CC.Function} {optid : Option CC.Ident} {a : CC.Expr}
    {al : List CC.Expr} {k : CC.Cont} {e : CC.Env} {le : CC.TempEnv} {m : CC.Mem}
    {tyargs : List CC.Ty} {tyres : CC.Ty} {cconv : CC.CallConv} {vf : CC.Val}
    {vargs : List CC.Val} {fd : CC.FunDef}
    (hclass : CC.Cop.classifyFun (CC.typeof a) = .f tyargs tyres cconv)
    (hfn : CC.doEvalExpr ge e le m a = some vf)
    (hargs : CC.doEvalExprlist ge e le m al tyargs = some vargs)
    (hfind : CC.Genv.findFunct ge.genv_genv vf = some fd)
    (htype : CC.typeOfFundef fd = .Tfunction tyargs tyres cconv) :
    CC.Step2 ge (.State fn (.Scall optid a al) k e le m) CC.E0
      (.Callstate fd vargs (.Kcall optid fn e le k) m) :=
  CC.Step.call _ _ _ _ _ _ _ _ _ _ _ _ _ _ hclass
    (CC.doEvalExpr_sound _ _ _ _ _ _ hfn)
    (CC.doEvalExprlist_sound _ _ _ _ _ _ _ hargs) hfind htype

/-- `Sset id (Ederef a tdouble)` steps silently to `Sskip` with `id ↦ Vfloat v` when `a` evaluates
to `Vptr b ofs` and memory holds `v` there. Address evaluation and the load are separate
hypotheses so that a table-load assumption can be plugged in directly. -/
theorem set_float_load [CC.ExternalCalls]
    {ge : CC.CGenv} {fn : CC.Function} {id : CC.Ident} {a : CC.Expr} {k : CC.Cont}
    {e : CC.Env} {le : CC.TempEnv} {m : CC.Mem} {b : CC.Block}
    {ofs : CC.Integers.Ptrofs} {v : CC.Floats.Float}
    (haddr : CC.doEvalExpr ge e le m a = some (.Vptr b ofs))
    (hload : CC.Mem.load .Mfloat64 m b ofs.unsigned = some (.Vfloat v)) :
    CC.Step2 ge (.State fn (.Sset id (.Ederef a CC.tdouble)) k e le m) CC.E0
      (.State fn .Sskip k e (le.set id (.Vfloat v)) m) := by
  apply CC.Step.set
  apply CC.EvalExpr.Elvalue
  · exact CC.EvalLvalue.Ederef _ _ _ _ (CC.doEvalExpr_sound _ _ _ _ _ _ haddr)
  · exact CC.DerefLoc.value _ _ rfl hload

/-- A finished call `Returnstate value Kstop memory` has no successor under `Step2`. -/
theorem return_stop_no_step [CC.ExternalCalls] (ge : CC.CGenv)
    (value : CC.Val) (memory : CC.Mem) (trace : CC.Trace) (state : CC.State) :
    ¬ CC.Step2 ge (.Returnstate value .Kstop memory) trace state := by
  intro h
  cases h

/-- `callCont k = k` when `k` is already a call continuation (`Kstop` or `Kcall`). -/
theorem callCont_eq_self {k : CC.Cont} (h : CC.isCallCont k = true) :
    CC.callCont k = k := by
  cases k <;> simp_all [CC.isCallCont, CC.callCont]

/-- Fuel-bounded interpreter: `runCall ge fuel state` drives CLean's `doStep` from `state`,
requiring every step's trace to be empty, and returns `(v, m)` on reaching
`Returnstate v Kstop m`. It runs any state, library calls as well as `main` in
`Quadrature.Clight.Main`. A `none` result means exhausted fuel, a stuck state or a non-silent
step. -/
def runCall (ge : CC.CGenv) : Nat → CC.State → Option (CC.Val × CC.Mem)
  | 0, _ => none
  | fuel + 1, state =>
    match state with
    | .Returnstate value .Kstop memory => some (value, memory)
    | _ => do
      let (trace, next) ← CC.doStep ge state
      if trace = CC.E0 then runCall ge fuel next else none

/-- A successful `runCall` yields a `StarE0` execution from `state` to
`Returnstate value Kstop memory`, by soundness of `doStep`. -/
theorem runCall_sound [CC.ExternalCalls] (ge : CC.CGenv) (fuel : Nat)
    (state : CC.State) (value : CC.Val) (memory : CC.Mem)
    (h : runCall ge fuel state = some (value, memory)) :
    CC.StarE0 (CC.Step2 ge) state (.Returnstate value .Kstop memory) := by
  induction fuel generalizing state with
  | zero => simp [runCall] at h
  | succ fuel ih =>
    unfold runCall at h
    split at h
    · cases Option.some.inj h
      exact .refl _
    · cases hstep : CC.doStep ge state with
      | none => simp [hstep] at h
      | some result =>
        obtain ⟨trace, next⟩ := result
        rw [hstep] at h
        change (if trace = CC.E0 then runCall ge fuel next else none) =
          some (value, memory) at h
        split at h
        · rename_i htrace
          subst trace
          exact .step _ _ _ (CC.doStep_sound ge state CC.E0 next hstep) (ih next h)
        · simp at h

/-- The return value of `runCall`, with the final memory dropped so that a kernel computation
need not compare memories. -/
def runCallValue (ge : CC.CGenv) (fuel : Nat) (state : CC.State) : Option CC.Val :=
  (runCall ge fuel state).map Prod.fst

/-- A successful `runCallValue` yields a `StarE0` execution from `state` to
`Returnstate value Kstop m` for some memory `m`. -/
theorem runCallValue_sound [CC.ExternalCalls] (ge : CC.CGenv) (fuel : Nat)
    (state : CC.State) (value : CC.Val)
    (h : runCallValue ge fuel state = some value) :
    ∃ memory, CC.StarE0 (CC.Step2 ge) state (.Returnstate value .Kstop memory) := by
  cases hrun : runCall ge fuel state with
  | none => simp [runCallValue, hrun] at h
  | some result =>
    obtain ⟨returned, memory⟩ := result
    simp only [runCallValue, hrun, Option.map_some, Option.some.injEq] at h
    subst returned
    exact ⟨memory, runCall_sound ge fuel state value memory hrun⟩

/-- A trace matching the empty trace under `CC.MatchTraces` is empty. -/
theorem matchTraces_empty {ge : CC.Senv} {trace : CC.Trace}
    (h : CC.MatchTraces ge CC.E0 trace) : trace = CC.E0 := by
  cases h
  rfl

/-- Given a silent run from `start` to a stuck state `finish` and deterministic external calls,
every run from `start` is silent and can be extended to `finish`. This is the `_prefix` half of
the total-correctness package. -/
theorem silent_execution_prefix [calls : CC.ExternalCalls]
    [CC.ExternalCallsDeterministic calls] (program : CC.Program)
    {start finish : CC.State}
    (hrun : CC.StarE0 (CC.Step2 program.globalenv) start finish)
    (hstop : ∀ trace state, ¬ CC.Step2 program.globalenv finish trace state) :
    ∀ {trace state}, CC.Star (CC.Step2 program.globalenv) start trace state →
      trace = CC.E0 ∧ CC.StarE0 (CC.Step2 program.globalenv) state finish := by
  induction hrun with
  | refl state =>
    intro trace reached hprefix
    cases hprefix with
    | refl => exact ⟨rfl, .refl _⟩
    | step _ trace next _ _ _ hstep _ _ => exact (hstop trace next hstep).elim
  | step start next finish hstep hrest ih =>
    intro trace reached hprefix
    cases hprefix with
    | refl => exact ⟨rfl, .step _ _ _ hstep hrest⟩
    | step _ firstTrace otherNext restTrace _ _ hfirst htail htrace =>
      have hdet := CC.step_determ (CC.entryDeterm_functionEntry2 program.globalenv)
        (CC.program_symbolsInjective program) hstep hfirst
      have hfirstTrace : firstTrace = CC.E0 := matchTraces_empty hdet.1
      have hnext := hdet.2 hfirstTrace.symm
      subst otherNext
      obtain ⟨htailTrace, hremaining⟩ := ih hstop htail
      exact ⟨by simpa [hfirstTrace, htailTrace, CC.Eapp, CC.E0] using htrace,
        hremaining⟩

/-- Under the hypotheses of `silent_execution_prefix`, no infinite sequence of steps starts at
`start`. This is the `_not_infinite` half of the total-correctness package. -/
theorem silent_execution_not_infinite [calls : CC.ExternalCalls]
    [CC.ExternalCallsDeterministic calls] (program : CC.Program)
    {start finish : CC.State}
    (hrun : CC.StarE0 (CC.Step2 program.globalenv) start finish)
    (hstop : ∀ trace state, ¬ CC.Step2 program.globalenv finish trace state) :
    ∀ (states : Nat → CC.State) (traces : Nat → CC.Trace), states 0 = start →
      (∀ n, CC.Step2 program.globalenv (states n) (traces n) (states (n + 1))) →
      False := by
  induction hrun with
  | refl state =>
    intro states traces hstart hsteps
    have hfirst := hsteps 0
    rw [hstart] at hfirst
    exact hstop _ _ hfirst
  | step start next finish hstep _ ih =>
    intro states traces hstart hsteps
    have hfirst := hsteps 0
    rw [hstart] at hfirst
    have hdet := CC.step_determ (CC.entryDeterm_functionEntry2 program.globalenv)
      (CC.program_symbolsInjective program) hstep hfirst
    have htrace : traces 0 = CC.E0 := matchTraces_empty hdet.1
    have hnext := hdet.2 htrace.symm
    exact ih hstop (fun n => states (n + 1)) (fun n => traces (n + 1))
      hnext.symm (fun n => hsteps (n + 1))

end Quadrature.Binary64.Clight
