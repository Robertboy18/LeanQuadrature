import Quadrature.Compiler.Cminor.Annotations
import Quadrature.Compiler.Execution.Run
import Quadrature.Compiler.Mach.Semantics

/-!
# A checked Mach executor

An executable checker for the rules of `Quadrature.Compiler.Mach.Semantics`. Read `executeStep`
first: it takes a return-address predictor and an external executor, checks the saved
stack pointer and return address before freeing a frame, and computes the successor
state. `execute_step_sound` shows that every successful step is a `Step` derivation for
any oracle the predictor is sound for.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Mach

open CC

/-- Executable external calls, the contract shared by every stage. -/
abbrev ExternalExecutor := Cminor.ExternalExecutor
/-- The external executor that emits numeric annotations and delegates other calls to CLean. -/
abbrev annotatedExternalCall := Cminor.annotatedExternalCall
/-- An executable return-address predictor, computing the offset for a function and
continuation. -/
abbrev ReturnAddressExecutor := Function → Code → Option Integers.Ptrofs

/-- The internal function stored at `block`, `none` for external functions or unmapped blocks. -/
def findInternal (ge : Genv) (block : Block) : Option Function :=
  match CC.Genv.findFunctPtr ge block with
  | some (.Internal function) => some function
  | _ => none

/-- `findInternal` succeeds exactly when the block holds an internal function. -/
theorem find_internal_iff {ge : Genv} {block : Block} {function : Function} :
    findInternal ge block = some function ↔
      CC.Genv.findFunctPtr ge block = some (.Internal function) := by
  unfold findInternal
  cases h : CC.Genv.findFunctPtr ge block with
  | none => simp
  | some fd => cases fd <;> simp

/-- Check both saved pointers and free the entire allocated block. -/
def releaseFrame (frames : List Stackframe) (function : Function) (stack : Val)
    (memory : Mem) : Option Mem :=
  if loadStack memory stack Tptr function.fn_link_ofs = some (parentStack frames) then
    if loadStack memory stack Tptr function.fn_retaddr_ofs =
        some (parentReturnAddress frames) then
      match stack with
      | .Vptr block _ => Mem.free memory block 0 function.fn_stacksize
      | _ => none
    else none
  else none

/-- `releaseFrame` succeeds exactly when the stack is a pointer, both saved values match the
parent frame, and the free succeeds. -/
theorem release_frame_iff {frames : List Stackframe} {function : Function} {stack : Val}
    {memory memory' : Mem} :
    releaseFrame frames function stack memory = some memory' ↔
      ∃ block offset, stack = .Vptr block offset ∧
        loadStack memory stack Tptr function.fn_link_ofs = some (parentStack frames) ∧
        loadStack memory stack Tptr function.fn_retaddr_ofs =
          some (parentReturnAddress frames) ∧
        Mem.free memory block 0 function.fn_stacksize = some memory' := by
  unfold releaseFrame
  split
  · next hlink =>
      split
      · next hreturn =>
          cases stack <;> simp_all
      · next hreturn =>
          constructor
          · intro h
            cases h
          · rintro ⟨_, _, _, _, h, _⟩
            exact False.elim (hreturn h)
  · next hlink =>
      constructor
      · intro h
        cases h
      · rintro ⟨_, _, _, h, _, _⟩
        exact False.elim (hlink h)

/-- Computes one Mach transition, using `predict` for return addresses and `external` for
builtins and external functions. Returns `none` when a lookup, memory access, or
saved-pointer check fails. -/
def executeStep (predict : ReturnAddressExecutor) (external : ExternalExecutor) (ge : Genv) :
    State → Option (Trace × State)
  | .Running s fb sp (instruction :: bb) rs m =>
      match instruction with
      | .Mop op args result => do
          let value ← evalOperation ge sp op (rs.values args)
          pure (E0, .Running s fb sp bb ((rs.undefRegs (destroyedByOp op)).set result value) m)
      | .Mload chunk address args result => do
          let pointer ← evalAddressing ge sp address (rs.values args)
          let value ← Mem.loadv chunk m pointer
          pure (E0, .Running s fb sp bb (rs.set result value) m)
      | .Mgetstack offset type result => do
          let value ← loadStack m sp type offset
          pure (E0, .Running s fb sp bb (rs.set result value) m)
      | .Msetstack source offset type => do
          let m' ← storeStack m sp type offset (rs source)
          pure (E0, .Running s fb sp bb (rs.undefRegs (destroyedBySetstack type)) m')
      | .Mgetparam offset type result => do
          let f ← findInternal ge fb
          if loadStack m sp Tptr f.fn_link_ofs = some (parentStack s) then
            let value ← loadStack m (parentStack s) type offset
            pure (E0, .Running s fb sp bb ((rs.set .AX .Vundef).set result value) m)
          else none
      | .Mstore chunk address args source => do
          let pointer ← evalAddressing ge sp address (rs.values args)
          let m' ← Mem.storev chunk m pointer (rs source)
          pure (E0, .Running s fb sp bb rs m')
      | .Mcall _ target => do
          let called ← findFunctionPtr ge target rs
          let f ← findInternal ge fb
          let offset ← predict f bb
          pure (E0, .Callstate (⟨fb, sp, .Vptr fb offset, bb⟩ :: s) called rs m)
      | .Mtailcall _ target => do
          let called ← findFunctionPtr ge target rs
          let f ← findInternal ge fb
          let m' ← releaseFrame s f sp m
          pure (E0, .Callstate s called rs m')
      | .Mbuiltin ef args result => do
          let values ← evalBuiltinArgs ge sp rs m args
          let (trace, value, m') ← external ef values m
          pure (trace, .Running s fb sp bb
            ((rs.undefRegs (destroyedByBuiltin ef)).setResult result value) m')
      | .Mlabel _ => some (E0, .Running s fb sp bb rs m)
      | .Mgoto label => do
          let f ← findInternal ge fb
          let target ← findLabel label f.fn_code
          pure (E0, .Running s fb sp target rs m)
      | .Mcond condition args label => do
          let result ← evalCondition condition (rs.values args)
          if result then
            let f ← findInternal ge fb
            let target ← findLabel label f.fn_code
            pure (E0, .Running s fb sp target rs m)
          else pure (E0, .Running s fb sp bb rs m)
      | .Mjumptable arg table =>
          match rs arg with
          | .Vint index => do
              let label ← table[(Integers.Int.unsigned index).toNat]?
              let f ← findInternal ge fb
              let target ← findLabel label f.fn_code
              pure (E0, .Running s fb sp target (rs.undefRegs [.AX, .DX]) m)
          | _ => none
      | .Mreturn => do
          let f ← findInternal ge fb
          let m' ← releaseFrame s f sp m
          pure (E0, .Returnstate s rs m')
  | .Running _ _ _ [] _ _ => none
  | .Callstate s fb rs m => do
      let fd ← CC.Genv.findFunctPtr ge fb
      match fd with
      | .Internal f =>
          let (m₁, block) := Mem.alloc m 0 f.fn_stacksize
          let sp := Val.Vptr block Integers.Ptrofs.zero
          let m₂ ← storeStack m₁ sp Tptr f.fn_link_ofs (parentStack s)
          let m₃ ← storeStack m₂ sp Tptr f.fn_retaddr_ofs (parentReturnAddress s)
          pure (E0, .Running s fb sp f.fn_code (rs.undefRegs [.AX, .FP0]) m₃)
      | .External ef =>
          let args ← externalArgs rs m (parentStack s) ef.sig
          let (trace, value, m') ← external ef args m
          pure (trace, .Returnstate s (rs.undefCallerSave.set (locResult ef.sig) value) m')
  | .Returnstate (frame :: s) rs m =>
      some (E0, .Running s frame.caller frame.stack frame.continuation rs m)
  | .Returnstate [] _ _ => none

/-- Runs exactly `fuel` transitions from a state, concatenating their traces. -/
def executeSteps (predict : ReturnAddressExecutor) (external : ExternalExecutor) (ge : Genv) :
    Nat → State → Option (Trace × State) :=
  Execution.run (executeStep predict external ge)

/-- The stage-specific executor implements the shared finite runner. -/
theorem execute_steps_eq_run (predict : ReturnAddressExecutor) (external : ExternalExecutor)
    (ge : Genv) (fuel : Nat) (state : State) :
    executeSteps predict external ge fuel state =
      Execution.run (executeStep predict external ge) fuel state :=
  rfl

/-- Every offset computed by `predict` is permitted by the oracle `relation`. -/
def ReturnAddressExecutorSound (predict : ReturnAddressExecutor) (relation : ReturnAddress) :
    Prop :=
  ∀ function code offset, predict function code = some offset → relation function code offset

variable [ExternalCalls]

/-- Every result accepted by `external` is permitted by the external-call relation over `ge`. -/
def ExternalExecutorSound (external : ExternalExecutor) (ge : Genv) : Prop :=
  Execution.ExternalExecutorSound external ge.toSenv

variable {predict : ReturnAddressExecutor} {returnAddress : ReturnAddress}
  {external : ExternalExecutor} {ge : Genv}

/-- A successful `executeStep` under a sound predictor `hreturn` and a sound external executor
`hexternal` is a `Step`. -/
theorem execute_step_sound (hreturn : ReturnAddressExecutorSound predict returnAddress)
    (hexternal : ExternalExecutorSound external ge) {start finish : State} {trace : Trace}
    (h : executeStep predict external ge start = some (trace, finish)) :
    Step returnAddress ge start trace finish := by
  cases start with
  | Running s fb sp instructions rs m =>
      cases instructions with
      | nil => cases h
      | cons instruction bb =>
          cases instruction with
          | Mop op args result =>
              simp only [executeStep, bind, Option.bind_eq_some_iff] at h
              obtain ⟨value, hvalue, h⟩ := h
              cases h
              exact .operation _ _ _ _ _ _ _ _ _ _ hvalue
          | Mload chunk address args result =>
              simp only [executeStep, bind, Option.bind_eq_some_iff] at h
              obtain ⟨pointer, hp, value, hv, h⟩ := h
              cases h
              exact .load _ _ _ _ _ _ _ _ _ _ _ _ hp hv
          | Mgetstack offset type result =>
              simp only [executeStep, bind, Option.bind_eq_some_iff] at h
              obtain ⟨value, hv, h⟩ := h
              cases h
              exact .getstack _ _ _ _ _ _ _ _ _ _ hv
          | Msetstack source offset type =>
              simp only [executeStep, bind, Option.bind_eq_some_iff] at h
              obtain ⟨m', hm, h⟩ := h
              cases h
              exact .setstack _ _ _ _ _ _ _ _ _ _ hm
          | Mgetparam offset type result =>
              simp only [executeStep, bind, Option.bind_eq_some_iff] at h
              obtain ⟨f, hf, h⟩ := h
              split at h
              · next hlink =>
                  simp only [Option.bind_eq_some_iff] at h
                  obtain ⟨value, hv, h⟩ := h
                  cases h
                  exact .getparam _ _ _ _ _ _ _ _ _ _ _
                    (find_internal_iff.mp hf) hlink hv
              · cases h
          | Mstore chunk address args source =>
              simp only [executeStep, bind, Option.bind_eq_some_iff] at h
              obtain ⟨pointer, hp, m', hm, h⟩ := h
              cases h
              exact .store _ _ _ _ _ _ _ _ _ _ _ _ hp hm
          | Mcall signature target =>
              simp only [executeStep, bind, Option.bind_eq_some_iff] at h
              obtain ⟨called, hcalled, f, hf, offset, hoffset, h⟩ := h
              cases h
              exact .call _ _ _ _ _ _ _ _ _ _ _ hcalled
                (find_internal_iff.mp hf) (hreturn _ _ _ hoffset)
          | Mtailcall signature target =>
              simp only [executeStep, bind, Option.bind_eq_some_iff] at h
              obtain ⟨called, hcalled, f, hf, m', hm, h⟩ := h
              cases h
              obtain ⟨block, soff, rfl, hlink, hra, hfree⟩ := release_frame_iff.mp hm
              exact .tailcall _ _ _ _ _ _ _ _ _ _ _ _ hcalled
                (find_internal_iff.mp hf) hlink hra hfree
          | Mbuiltin ef args result =>
              simp only [executeStep, bind, Option.bind_eq_some_iff] at h
              obtain ⟨values, hv, ⟨emitted, value, m'⟩, hext, h⟩ := h
              cases h
              exact .builtin _ _ _ _ _ _ _ _ _ _ _ _ _ (eval_builtin_args_sound hv)
                (hexternal _ _ _ _ _ _ hext)
          | Mlabel label =>
              cases h
              exact .label _ _ _ _ _ _ _
          | Mgoto label =>
              simp only [executeStep, bind, Option.bind_eq_some_iff] at h
              obtain ⟨f, hf, target, htarget, h⟩ := h
              cases h
              exact .goto _ _ _ _ _ _ _ _ _ (find_internal_iff.mp hf) htarget
          | Mcond condition args label =>
              simp only [executeStep, bind, Option.bind_eq_some_iff] at h
              obtain ⟨result, hb, h⟩ := h
              cases result with
              | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte] at h
                  cases h
                  exact .condition_false _ _ _ _ _ _ _ _ _ hb
              | true =>
                  simp only [↓reduceIte, Option.bind_eq_some_iff] at h
                  obtain ⟨f, hf, target, htarget, h⟩ := h
                  cases h
                  exact .condition_true _ _ _ _ _ _ _ _ _ _ _
                    hb (find_internal_iff.mp hf) htarget
          | Mjumptable arg table =>
              simp only [executeStep] at h
              cases harg : rs arg <;> simp only [harg] at h <;> try cases h
              simp only [bind, Option.bind_eq_some_iff] at h
              obtain ⟨label, hn, f, hf, target, htarget, h⟩ := h
              cases h
              exact .jumpTable _ _ _ _ _ _ _ _ _ _ _ _
                harg hn (find_internal_iff.mp hf) htarget
          | Mreturn =>
              simp only [executeStep, bind, Option.bind_eq_some_iff] at h
              obtain ⟨f, hf, m', hm, h⟩ := h
              cases h
              obtain ⟨block, soff, rfl, hlink, hra, hfree⟩ := release_frame_iff.mp hm
              exact .returnValue _ _ _ _ _ _ _ _ _
                (find_internal_iff.mp hf) hlink hra hfree
  | Callstate s fb rs m =>
      simp only [executeStep, bind, Option.bind_eq_some_iff] at h
      obtain ⟨fd, hfd, h⟩ := h
      cases fd with
      | Internal f =>
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨m₂, hlink, m₃, hra, h⟩ := h
          cases h
          exact .internal_function _ _ _ _ _ _ _ _ _ hfd rfl hlink hra
      | External ef =>
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨args, hargs, ⟨emitted, value, m'⟩, hext, h⟩ := h
          cases h
          exact .external_function _ _ _ _ _ _ _ _ _ hfd
            (external_args_iff.mpr hargs) (hexternal _ _ _ _ _ _ hext)
  | Returnstate s rs m =>
      cases s <;> cases h
      exact .return_to_caller _ _ _ _

/-- A successful `executeSteps` run under a sound predictor `hreturn` and a sound external
executor `hexternal` is a `Steps` derivation with the same trace. -/
theorem execute_steps_sound (hreturn : ReturnAddressExecutorSound predict returnAddress)
    (hexternal : ExternalExecutorSound external ge)
    {fuel : Nat} {start finish : State} {trace : Trace}
    (h : executeSteps predict external ge fuel start = some (trace, finish)) :
    Steps returnAddress ge start trace finish := by
  rw [execute_steps_eq_run] at h
  exact Execution.run_sound (execute_step_sound hreturn hexternal) Steps.refl Steps.cons h

/-- The numeric-annotation executor is sound in every global environment. -/
theorem annotated_external_executor_sound :
    ExternalExecutorSound annotatedExternalCall ge :=
  Cminor.annotated_external_call_sound

end Quadrature.Mach
