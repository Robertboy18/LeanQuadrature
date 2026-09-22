import Quadrature.Clight.Observation
import Quadrature.Clight.StoredAccuracy

/-!
# An initialized quadrature application with an observable result

`main` is written directly in Clight (not parsed from C). It calls the imported
integrator with the original callback and a stored order `n`, reports the
result through CompCert's annotation builtin, which places the value in the
trace as `quadrature-result`, and returns integer zero. There is no printf.
The caller follows the companion Rocq proofs in `compcert/PolynomialRules.v`,
which verify the same application over CompCert's Clight semantics in Rocq.
`program n` appends `main` to `polynomialLibrary`. The theorems prove global
initialization, the whole-program execution with its one-event trace, the
total-correctness package for runs from the initial state (vocabulary: see
`Quadrature.Clight.Execution` and `Quadrature.Clight.Observation`), and the
integral bound on the observed value.
-/

namespace Quadrature.Binary64.Clight.Application

open FloatLib.Floats.Formats.BinaryInterchange
open ClightSource

/-- The identifier of `main`. -/
def mainIdent : CC.Ident := CC.identOfString "main"
/-- The temporary of `main` that receives the integrator's result. -/
def resultTemp : CC.Ident := CC.Positive.ofNat 1000

/-- The trace of one `quadrature-result` annotation carrying `value`, the event the companion
Rocq proofs observe as well. -/
def resultTrace (value : Value) : CC.Trace :=
  [.Event_annot "quadrature-result" [.EVfloat value]]

private def observation : CC.Stmt :=
  .Sbuiltin none (.EF_annot (CC.Positive.ofNat 1) "quadrature-result" [.Tfloat]) [CC.tdouble]
    [.Etempvar resultTemp CC.tdouble]

private def exitStatement : CC.Stmt :=
  .Sreturn (some (.Econst_int CC.Integers.Int.zero CC.tint))

private def suffix : CC.Stmt := .Ssequence observation exitStatement

private def callbackType : CC.Ty :=
  .Tfunction [CC.tdouble] CC.tdouble CC.cc_default

/-- The Clight `main` for the stored order `n`: `resultTemp = integrate(&testfun, n)`, then the
`quadrature-result` annotation of `resultTemp`, then `return 0`. -/
def mainFunction (n : Nat) : CC.Function where
  fn_return := CC.tint
  fn_callconv := CC.cc_default
  fn_params := []
  fn_vars := []
  fn_temps := [(resultTemp, CC.tdouble)]
  fn_body :=
    .Ssequence
      (.Scall (some resultTemp)
        (.Evar _integrate
          (.Tfunction [CC.tptr callbackType, CC.tint] CC.tdouble CC.cc_default))
        [.Eaddrof (.Evar _testfun callbackType) (CC.tptr callbackType),
         .Econst_int (CC.Integers.Int.repr n) CC.tint])
      suffix

/-- `polynomialLibrary` with `mainFunction n` appended as ninth definition and made the public
entry point. -/
def program (n : Nat) : CC.Program :=
  CC.mkprogram []
    (polynomialLibrary.prog_defs ++ [(mainIdent, .Gfun (.Internal (mainFunction n)))])
    [mainIdent] mainIdent

/-- The initialized global memory of `program n`, computed at `n = 0`. Every order has the same
global layout, since only the body of `main` depends on `n`. -/
def entryMemory : CC.Mem := (program 0).initMem.getD CC.Mem.empty

-- Compute the global initialization of the nine definitions, including the 110 table words.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- Global initialization of `program 0` succeeds, by kernel evaluation. -/
theorem program_initializes : (program 0).initMem.isSome = true := by
  decide +kernel

-- The initializers do not mention `n`, so the goal is `program_initializes` up to `change`.
set_option maxRecDepth 20000 in
/-- Every `program n` initializes to `entryMemory`. -/
theorem program_initialized (n : Nat) : (program n).initMem = some entryMemory := by
  change (program 0).initMem = some entryMemory
  have h := program_initializes
  unfold entryMemory
  cases hm : (program 0).initMem <;> simp_all

/-- The state entering `main` from `entryMemory` under the empty continuation, CLean's initial
state of `program n` (see `initial_state`). -/
def initialState (n : Nat) : CC.State :=
  .Callstate (.Internal (mainFunction n)) [] .Kstop entryMemory

/-- `initialState n` is CLean's `InitialState` of `program n`: `main` resolves to block 9 and the
memory is the initialized memory. -/
theorem initial_state (n : Nat) : CC.InitialState (program n) (initialState n) :=
  .intro (CC.Positive.ofNat 9) _ _ (program_initialized n) (by rfl) (by rfl) rfl

-- Read the 110 table cells from the initialized memory, for each `n ≤ 10`.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
/-- For `n ≤ 10`, `entryMemory` holds the cells of `storedTerms n` in the node block 1 and the
weight block 2 at their C offsets. -/
theorem table_cells (n : Nat) (hn : n ≤ 10) :
    TableCells entryMemory (CC.Positive.ofNat 1) (CC.Positive.ofNat 2)
      n 0 (storedTerms n) := by
  interval_cases n <;>
    dsimp [storedTerms, ClightTableData.weightBits, ClightTableData.nodeBits,
      List.zip, List.drop, List.take, List.map, TableCells] <;>
    (repeat' constructor)

/-- `program n` with `entryMemory` satisfies `StoredLibraryContext` for `storedTerms n`, with the
tables at blocks 1 and 2 and the accessors at blocks 3 and 4. -/
def libraryContext (n : Nat) (hn : n ≤ 10) :
    StoredLibraryContext (program n).globalenv entryMemory (storedTerms n) where
  nodes := CC.Positive.ofNat 1
  weights := CC.Positive.ofNat 2
  point := CC.Positive.ofNat 3
  weight := CC.Positive.ofNat 4
  nodes_symbol := by rfl
  weights_symbol := by rfl
  point_symbol := by rfl
  weight_symbol := by rfl
  point_function := by rfl
  weight_function := by rfl
  count_bound := by rw [stored_terms_length n hn]; exact hn
  cells := by rw [stored_terms_length n hn]; exact table_cells n hn

/-- In `program n`, the original callback with the internal polynomial at `cos` (block 8)
satisfies `LibraryCallbackContract` with `f = testfun Polynomial.cosine`. -/
theorem callback_contract [CC.ExternalCalls] (n : Nat) :
    LibraryCallbackContract (program n).globalenv entryMemory
      (.Vptr testfunBlock CC.Integers.Ptrofs.zero) (.Internal f_testfun)
      (testfun Polynomial.cosine) :=
  polynomial_callback_contract_in_context _ _ _ (CC.Positive.ofNat 8)
    (by rfl) (by rfl) (by rfl)

private def entryTemps : CC.TempEnv := CC.createUndefTemps [(resultTemp, CC.tdouble)]

private def continuation (n : Nat) : CC.Cont :=
  .Kcall (some resultTemp) (mainFunction n) CC.emptyEnv entryTemps (.Kseq suffix .Kstop)

private def observationState (n : Nat) (value : Value) : CC.State :=
  .State (mainFunction n) observation (.Kseq exitStatement .Kstop) CC.emptyEnv
    (entryTemps.set resultTemp (.Vfloat value)) entryMemory

private theorem caller_entry [CC.ExternalCalls] (n : Nat) :
    CC.StarE0 (CC.Step2 (program n).globalenv) (initialState n)
      (storedLibraryCall (.Vptr testfunBlock CC.Integers.Ptrofs.zero)
        n (continuation n) entryMemory) := by
  refine .step _ _ _ (CC.doStep_sound _ _ _ _ (by rfl)) ?_
  refine .step _ _ _ (CC.doStep_sound _ _ _ _ (by rfl)) ?_
  exact .step _ _ _ (CC.doStep_sound _ _ _ _ (by rfl)) (.refl _)

private theorem caller_resume [CC.ExternalCalls] (n : Nat) (value : Value) :
    CC.StarE0 (CC.Step2 (program n).globalenv)
      (.Returnstate (.Vfloat value) (continuation n) entryMemory)
      (observationState n value) := by
  refine .step _ _ _ (CC.doStep_sound _ _ _ _ (by rfl)) ?_
  refine .step _ _ _ (CC.doStep_sound _ _ _ _ (by rfl)) ?_
  exact .step _ _ _ (CC.doStep_sound _ _ _ _ (by rfl)) (.refl _)

/-- For `n ≤ 10`, `initialState n` runs silently to the state about to execute the annotation,
with `resultTemp ↦ Vfloat (StoredPolynomial.result n)` and memory `entryMemory`. -/
theorem before_observation [CC.ExternalCalls] (n : Nat) (hn : n ≤ 10) :
    CC.StarE0 (CC.Step2 (program n).globalenv) (initialState n)
      (observationState n (StoredPolynomial.result n)) := by
  apply starE0_trans (caller_entry n)
  have h := stored_library_execution _ entryMemory (storedTerms n) (libraryContext n hn)
    (.Internal f_testfun) (testfun Polynomial.cosine)
    (.Vptr testfunBlock CC.Integers.Ptrofs.zero) (callback_contract n) (continuation n)
  rw [stored_terms_length n hn] at h
  exact starE0_trans h (caller_resume n (StoredPolynomial.result n))

private theorem observe_and_exit [CC.ExternalCalls] (n : Nat) (value : Value) :
    CC.Star (CC.Step2 (program n).globalenv) (observationState n value)
      (resultTrace value)
      (.Returnstate (.Vint CC.Integers.Int.zero) .Kstop entryMemory) := by
  refine .step _ (resultTrace value)
    (.State (mainFunction n) .Sskip (.Kseq exitStatement .Kstop) CC.emptyEnv
      (entryTemps.set resultTemp (.Vfloat value)) entryMemory)
    CC.E0 _ _ ?_ ?_ (by simp [CC.Eapp, CC.E0])
  · apply CC.Step.builtin (vargs := [.Vfloat value])
    · exact CC.doEvalExprlist_sound _ _ _ _ _ _ _ (by rfl)
    · exact CC.ExtcallAnnotSem.intro _ _ _ _
        (.evl_match_cons _ _ _ _ _ _ (.ev_match_float value) .evl_match_nil)
  · apply CC.star_of_starE0
    refine .step _ _ _ (CC.doStep_sound _ _ _ _ (by rfl)) ?_
    exact .step _ _ _ (CC.doStep_sound _ _ _ _ (by rfl)) (.refl _)

/-- For `n ≤ 10`, `initialState n` runs to `Returnstate (Vint 0) Kstop entryMemory` with trace
`resultTrace (StoredPolynomial.result n)`: the imported loop, the annotation and the exit. -/
theorem execution [CC.ExternalCalls] (n : Nat) (hn : n ≤ 10) :
    CC.Star (CC.Step2 (program n).globalenv) (initialState n)
      (resultTrace (StoredPolynomial.result n))
      (.Returnstate (.Vint CC.Integers.Int.zero) .Kstop entryMemory) := by
  exact star_trans (CC.star_of_starE0 (before_observation n hn))
    (observe_and_exit n (StoredPolynomial.result n))

/-- For `1 ≤ n ≤ 10`, some value is observed by a run of `program n` from its initial state to a
zero exit, and that value is finite and within `StoredPolynomial.errorBound n` of the integral. -/
theorem execution_accuracy [CC.ExternalCalls] (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    ∃ value : Value,
      CC.InitialState (program n) (initialState n) ∧
      CC.Star (CC.Step2 (program n).globalenv) (initialState n) (resultTrace value)
        (.Returnstate (.Vint CC.Integers.Int.zero) .Kstop entryMemory) ∧
      Model.isFinite value = true ∧
      |Model.toReal value - ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤
        StoredPolynomial.errorBound n :=
  ⟨StoredPolynomial.result n, initial_state n, execution n hhi,
    StoredPolynomial.integral_accuracy n hlo hhi⟩

/-- Total-correctness package: every run of `program n` from an initial state can be extended to
the zero exit, and its trace so far is a prefix of `resultTrace (StoredPolynomial.result n)`. -/
theorem execution_prefix [calls : CC.ExternalCalls] [CC.ExternalCallsDeterministic calls]
    (n : Nat) (hn : n ≤ 10) (start reached : CC.State) (trace : CC.Trace)
    (hinit : CC.InitialState (program n) start)
    (h : CC.Star (CC.Step2 (program n).globalenv) start trace reached) :
    ∃ remaining, CC.Eapp trace remaining = resultTrace (StoredPolynomial.result n) ∧
      CC.Star (CC.Step2 (program n).globalenv) reached remaining
        (.Returnstate (.Vint CC.Integers.Int.zero) .Kstop entryMemory) := by
  have hstart := CC.initialState_determ hinit (initial_state n)
  subst start
  exact annotation_execution_prefix (program n) (execution n hn)
    (annotation_trace_singleton _ _) (return_stop_no_step _ _ _) h

/-- Total-correctness package: every state reachable from an initial state is the zero exit or
has a successor. -/
theorem progress [calls : CC.ExternalCalls] [CC.ExternalCallsDeterministic calls]
    (n : Nat) (hn : n ≤ 10) (start reached : CC.State) (trace : CC.Trace)
    (hinit : CC.InitialState (program n) start)
    (h : CC.Star (CC.Step2 (program n).globalenv) start trace reached) :
    reached = .Returnstate (.Vint CC.Integers.Int.zero) .Kstop entryMemory ∨
      ∃ nextTrace next, CC.Step2 (program n).globalenv reached nextTrace next := by
  obtain ⟨remaining, _, hrest⟩ := execution_prefix n hn start reached trace hinit h
  cases hrest with
  | refl => exact Or.inl rfl
  | step _ first next _ _ _ hstep _ _ => exact Or.inr ⟨first, next, hstep⟩

/-- Total-correctness package: no infinite sequence of steps starts at an initial state of
`program n`. -/
theorem not_infinite [calls : CC.ExternalCalls] [CC.ExternalCallsDeterministic calls]
    (n : Nat) (hn : n ≤ 10) (states : Nat → CC.State) (traces : Nat → CC.Trace)
    (hinit : CC.InitialState (program n) (states 0))
    (hsteps : ∀ i, CC.Step2 (program n).globalenv (states i) (traces i) (states (i + 1))) :
    False :=
  annotation_execution_not_infinite (program n) (execution n hn)
    (annotation_trace_singleton _ _) (return_stop_no_step _ _ _) states traces
    (CC.initialState_determ hinit (initial_state n)) hsteps

/-- Total-correctness package: every finished run from an initial state has trace
`resultTrace (StoredPolynomial.result n)`, returns `Vint 0` and leaves memory `entryMemory`. -/
theorem return_specification [calls : CC.ExternalCalls]
    [CC.ExternalCallsDeterministic calls] (n : Nat) (hn : n ≤ 10)
    (start : CC.State) (trace : CC.Trace) (value : CC.Val) (memory : CC.Mem)
    (hinit : CC.InitialState (program n) start)
    (h : CC.Star (CC.Step2 (program n).globalenv) start trace
      (.Returnstate value .Kstop memory)) :
    trace = resultTrace (StoredPolynomial.result n) ∧
      value = .Vint CC.Integers.Int.zero ∧ memory = entryMemory := by
  have hstart := CC.initialState_determ hinit (initial_state n)
  subst start
  have heq := annotation_execution_unique (program n) (execution n hn)
    (annotation_trace_singleton _ _) (return_stop_no_step _ _ _) h
    (return_stop_no_step _ _ _)
  exact ⟨heq.1, (CC.State.Returnstate.inj heq.2).1,
    (CC.State.Returnstate.inj heq.2).2.2⟩

/-- For `1 ≤ n ≤ 10`, every run of `program n` from an initial state to a CLean `FinalState`
exits with status zero. Its trace is one annotation of a finite value within
`StoredPolynomial.errorBound n` of ∫₋₁¹ ½(1−x)cos x dx. -/
theorem final_accuracy [calls : CC.ExternalCalls] [CC.ExternalCallsDeterministic calls]
    (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10)
    (start finish : CC.State) (trace : CC.Trace) (status : CC.Integers.Int)
    (hinit : CC.InitialState (program n) start)
    (h : CC.Star (CC.Step2 (program n).globalenv) start trace finish)
    (hfinal : CC.FinalState finish status) :
    status = CC.Integers.Int.zero ∧
      ∃ value : Value, trace = resultTrace value ∧
        Model.isFinite value = true ∧
        |Model.toReal value - ∫ x in (-1 : ℝ)..1, Example.integrand x| ≤
          StoredPolynomial.errorBound n := by
  cases hfinal with
  | intro status memory =>
    have hspec := return_specification n hhi start trace (.Vint status) memory hinit h
    exact ⟨CC.Val.Vint.inj hspec.2.1, StoredPolynomial.result n, hspec.1,
      StoredPolynomial.integral_accuracy n hlo hhi⟩

end Quadrature.Binary64.Clight.Application
