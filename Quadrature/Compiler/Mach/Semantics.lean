import Quadrature.Compiler.Cminor.Semantics
import Quadrature.Compiler.Mach.Arguments

/-!
# Mach transition rules

Small-step rules for Mach, after `backend/Mach.v` on x86-64 ELF. Read `Step` first, one
transition under a return-address oracle and a global environment, emitting a trace.
Calls store a return address in the semantic call frame. Function entry allocates the
frame and writes the caller's stack pointer and return address. Return and tail call
check both saved values before freeing the frame.

`Step` takes `returnAddress : Function → Code → Ptrofs → Prop`, CompCert's
`return_address_offset` oracle for the assembly offset following a call. Two instances
are used: table membership `ImportedAddresses.relation` (file
`Mach/ImportedReturnAddresses.lean`) and the Lean Asmgen translation
`Asm.Generation.returnAddress`. The two are related in `Asm/GeneratedReturnAddresses.lean`.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Mach

open CC

/-- One Mach transition under the return-address oracle `returnAddress` and global environment
`ge`, emitting a trace. Each constructor mirrors one rule of `backend/Mach.v`. The `call`
rule consults the oracle for the saved return address, and builtins and external functions
step by the external-call relation `externalCall`. -/
inductive Step [ExternalCalls] (returnAddress : ReturnAddress) (ge : Genv) :
    State → Trace → State → Prop where
  | operation (s f sp rs m op args result bb value) :
      evalOperation ge sp op (rs.values args) = some value →
      Step returnAddress ge (.Running s f sp (.Mop op args result :: bb) rs m)
        E0 (.Running s f sp bb ((rs.undefRegs (destroyedByOp op)).set result value) m)
  | load (s f sp rs m chunk address args result bb pointer value) :
      evalAddressing ge sp address (rs.values args) = some pointer →
      Mem.loadv chunk m pointer = some value →
      Step returnAddress ge (.Running s f sp (.Mload chunk address args result :: bb) rs m)
        E0 (.Running s f sp bb (rs.set result value) m)
  | getstack (s f sp rs m offset type result bb value) :
      loadStack m sp type offset = some value →
      Step returnAddress ge (.Running s f sp (.Mgetstack offset type result :: bb) rs m)
        E0 (.Running s f sp bb (rs.set result value) m)
  | setstack (s f sp rs m source offset type bb m') :
      storeStack m sp type offset (rs source) = some m' →
      Step returnAddress ge (.Running s f sp (.Msetstack source offset type :: bb) rs m)
        E0 (.Running s f sp bb (rs.undefRegs (destroyedBySetstack type)) m')
  | getparam (s fb f sp rs m offset type result bb value) :
      CC.Genv.findFunctPtr ge fb = some (.Internal f) →
      loadStack m sp Tptr f.fn_link_ofs = some (parentStack s) →
      loadStack m (parentStack s) type offset = some value →
      Step returnAddress ge (.Running s fb sp (.Mgetparam offset type result :: bb) rs m)
        E0 (.Running s fb sp bb ((rs.set .AX .Vundef).set result value) m)
  | store (s f sp rs m chunk address args source bb pointer m') :
      evalAddressing ge sp address (rs.values args) = some pointer →
      Mem.storev chunk m pointer (rs source) = some m' →
      Step returnAddress ge (.Running s f sp (.Mstore chunk address args source :: bb) rs m)
        E0 (.Running s f sp bb rs m')
  | call (s fb f sp rs m signature target bb called offset) :
      findFunctionPtr ge target rs = some called →
      CC.Genv.findFunctPtr ge fb = some (.Internal f) →
      returnAddress f bb offset →
      Step returnAddress ge (.Running s fb sp (.Mcall signature target :: bb) rs m)
        E0 (.Callstate (⟨fb, sp, .Vptr fb offset, bb⟩ :: s) called rs m)
  | tailcall (s fb f block soff rs m signature target bb called m') :
      findFunctionPtr ge target rs = some called →
      CC.Genv.findFunctPtr ge fb = some (.Internal f) →
      loadStack m (.Vptr block soff) Tptr f.fn_link_ofs = some (parentStack s) →
      loadStack m (.Vptr block soff) Tptr f.fn_retaddr_ofs = some (parentReturnAddress s) →
      Mem.free m block 0 f.fn_stacksize = some m' →
      Step returnAddress ge (.Running s fb (.Vptr block soff)
          (.Mtailcall signature target :: bb) rs m)
        E0 (.Callstate s called rs m')
  | builtin (s f sp rs m ef args result bb values trace value m') :
      EvalBuiltinArgs ge sp rs m args values →
      externalCall ef ge.toSenv values m trace value m' →
      Step returnAddress ge (.Running s f sp (.Mbuiltin ef args result :: bb) rs m)
        trace (.Running s f sp bb
          ((rs.undefRegs (destroyedByBuiltin ef)).setResult result value) m')
  | label (s f sp rs m label bb) :
      Step returnAddress ge (.Running s f sp (.Mlabel label :: bb) rs m)
        E0 (.Running s f sp bb rs m)
  | goto (s fb f sp rs m label bb target) :
      CC.Genv.findFunctPtr ge fb = some (.Internal f) →
      findLabel label f.fn_code = some target →
      Step returnAddress ge (.Running s fb sp (.Mgoto label :: bb) rs m)
        E0 (.Running s fb sp target rs m)
  | condition_true (s fb f sp rs m condition args label bb target) :
      evalCondition condition (rs.values args) = some true →
      CC.Genv.findFunctPtr ge fb = some (.Internal f) →
      findLabel label f.fn_code = some target →
      Step returnAddress ge (.Running s fb sp (.Mcond condition args label :: bb) rs m)
        E0 (.Running s fb sp target rs m)
  | condition_false (s fb sp rs m condition args label bb) :
      evalCondition condition (rs.values args) = some false →
      Step returnAddress ge (.Running s fb sp (.Mcond condition args label :: bb) rs m)
        E0 (.Running s fb sp bb rs m)
  | jumpTable (s fb f sp rs m arg table bb index label target) :
      rs arg = .Vint index →
      table[(Integers.Int.unsigned index).toNat]? = some label →
      CC.Genv.findFunctPtr ge fb = some (.Internal f) →
      findLabel label f.fn_code = some target →
      Step returnAddress ge (.Running s fb sp (.Mjumptable arg table :: bb) rs m)
        E0 (.Running s fb sp target (rs.undefRegs [.AX, .DX]) m)
  | returnValue (s fb f block soff rs m bb m') :
      CC.Genv.findFunctPtr ge fb = some (.Internal f) →
      loadStack m (.Vptr block soff) Tptr f.fn_link_ofs = some (parentStack s) →
      loadStack m (.Vptr block soff) Tptr f.fn_retaddr_ofs = some (parentReturnAddress s) →
      Mem.free m block 0 f.fn_stacksize = some m' →
      Step returnAddress ge (.Running s fb (.Vptr block soff) (.Mreturn :: bb) rs m)
        E0 (.Returnstate s rs m')
  | internal_function (s fb f rs m m₁ m₂ m₃ block) :
      CC.Genv.findFunctPtr ge fb = some (.Internal f) →
      Mem.alloc m 0 f.fn_stacksize = (m₁, block) →
      storeStack m₁ (.Vptr block Integers.Ptrofs.zero) Tptr f.fn_link_ofs (parentStack s) =
        some m₂ →
      storeStack m₂ (.Vptr block Integers.Ptrofs.zero) Tptr f.fn_retaddr_ofs
        (parentReturnAddress s) = some m₃ →
      Step returnAddress ge (.Callstate s fb rs m)
        E0 (.Running s fb (.Vptr block Integers.Ptrofs.zero) f.fn_code
          (rs.undefRegs [.AX, .FP0]) m₃)
  | external_function (s fb ef rs m args trace value m') :
      CC.Genv.findFunctPtr ge fb = some (.External ef) →
      ExternalArgs rs m (parentStack s) ef.sig args →
      externalCall ef ge.toSenv args m trace value m' →
      Step returnAddress ge (.Callstate s fb rs m)
        trace (.Returnstate s (rs.undefCallerSave.set (locResult ef.sig) value) m')
  | return_to_caller (frame s rs m) :
      Step returnAddress ge (.Returnstate (frame :: s) rs m)
        E0 (.Running s frame.caller frame.stack frame.continuation rs m)

/-- The initial state of `program`: a call to the block of `prog_main` with every register
`Vundef`, in the program's initial memory. -/
inductive InitialState (program : Program) : State → Prop where
  | intro (block : Block) (memory : Mem) :
      program.initMem = some memory →
      CC.Genv.findSymbol program.globalenv program.prog_main = some block →
      InitialState program (.Callstate [] block Regset.empty memory)

/-- A final state is a `Returnstate` with no frames whose `AX` holds the integer exit status. -/
inductive FinalState : State → Integers.Int → Prop where
  | intro (registers : Regset) (result : Integers.Int) (memory : Mem) :
      registers .AX = .Vint result →
      FinalState (.Returnstate [] registers memory) result

/-- Finite sequences of transitions, concatenating their traces. -/
inductive Steps [ExternalCalls] (returnAddress : ReturnAddress) (ge : Genv) :
    State → Trace → State → Prop where
  | refl (state : State) : Steps returnAddress ge state [] state
  | cons {start next finish : State} {first rest : Trace} :
      Step returnAddress ge start first next → Steps returnAddress ge next rest finish →
      Steps returnAddress ge start (first ++ rest) finish

variable [ExternalCalls] {returnAddress : ReturnAddress} {ge : Genv}

/-- A single transition `h` is a one-step sequence with the same trace. -/
theorem steps_single {start finish : State} {trace : Trace}
    (h : Step returnAddress ge start trace finish) :
    Steps returnAddress ge start trace finish := by
  simpa using Steps.cons h (.refl finish)

/-- Two sequences `hleft` and `hright` compose, concatenating their traces. -/
theorem steps_trans {start middle finish : State} {left right : Trace}
    (hleft : Steps returnAddress ge start left middle)
    (hright : Steps returnAddress ge middle right finish) :
    Steps returnAddress ge start (left ++ right) finish := by
  induction hleft with
  | refl => exact hright
  | cons h _ ih => simpa only [List.append_assoc] using Steps.cons h (ih hright)

/-- No transition leaves a final state `hfinal`. -/
theorem final_state_stuck {state next : State} {result : Integers.Int} {trace : Trace}
    (hfinal : FinalState state result) : ¬ Step returnAddress ge state trace next := by
  cases hfinal
  intro h
  cases h

end Quadrature.Mach
