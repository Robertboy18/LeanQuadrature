import Quadrature.Compiler.Cminor.Semantics
import Quadrature.Compiler.LTL.Arguments

/-!
# LTL transition rules

Small-step rules for LTL on x86-64 ELF, after `backend/LTL.v`. `Step ge s t s'` is one
transition emitting trace `t`, and `Steps` is its closure. Operations read their
operands before clobbering registers. Calls save the caller's locations, and returns
restore callee-save registers and local slots through `returnRegs`. Tail calls resolve
their target after that restoration, as in CompCert. Loads, stores, and the selected
conditions clobber no registers on this target. An empty basic block is stuck.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.LTL

open CC

/-- `Step ge s t s'` is one LTL transition from `s` to `s'` emitting trace `t`: entering a block,
running its head instruction, a function entry, an external call, or a return. -/
inductive Step [ExternalCalls] (ge : Genv) : State → Trace → State → Prop where
  | startBlock (s f sp pc rs m bb) :
      f.fn_code.get pc = some bb →
      Step ge (.Running s f sp pc rs m) E0 (.Block s f sp bb rs m)
  | operation (s f sp rs m op args result bb value) :
      evalOperation ge sp op (rs.values args) = some value →
      Step ge (.Block s f sp (.Lop op args result :: bb) rs m)
        E0 (.Block s f sp bb ((rs.undefRegs (destroyedByOp op)).set (.R result) value) m)
  | load (s f sp rs m chunk address args result bb pointer value) :
      evalAddressing ge sp address (rs.values args) = some pointer →
      Mem.loadv chunk m pointer = some value →
      Step ge (.Block s f sp (.Lload chunk address args result :: bb) rs m)
        E0 (.Block s f sp bb (rs.set (.R result) value) m)
  | getstack (s f sp rs m slot offset type result bb) :
      Step ge (.Block s f sp (.Lgetstack slot offset type result :: bb) rs m)
        E0 (.Block s f sp bb ((rs.undefRegs (destroyedByGetstack slot)).set
          (.R result) (rs (.S slot offset type))) m)
  | setstack (s f sp rs m source slot offset type bb) :
      Step ge (.Block s f sp (.Lsetstack source slot offset type :: bb) rs m)
        E0 (.Block s f sp bb ((rs.undefRegs (destroyedBySetstack type)).set
          (.S slot offset type) (rs.reg source)) m)
  | store (s f sp rs m chunk address args source bb pointer m') :
      evalAddressing ge sp address (rs.values args) = some pointer →
      Mem.storev chunk m pointer (rs.reg source) = some m' →
      Step ge (.Block s f sp (.Lstore chunk address args source :: bb) rs m)
        E0 (.Block s f sp bb rs m')
  | call (s f sp rs m signature target bb fd) :
      findFunction ge target rs = some fd →
      fd.signature = signature →
      Step ge (.Block s f sp (.Lcall signature target :: bb) rs m)
        E0 (.Callstate (⟨f, sp, rs, bb⟩ :: s) fd rs m)
  | tailcall (s f block rs m signature target bb fd m') :
      findFunction ge target (returnRegs (parentLocset s) rs) = some fd →
      fd.signature = signature →
      Mem.free m block 0 f.fn_stacksize = some m' →
      Step ge (.Block s f (.Vptr block Integers.Ptrofs.zero)
          (.Ltailcall signature target :: bb) rs m)
        E0 (.Callstate s fd (returnRegs (parentLocset s) rs) m')
  | builtin (s f sp rs m ef args result bb values trace value m') :
      EvalBuiltinArgs ge sp rs m args values →
      externalCall ef ge.toSenv values m trace value m' →
      Step ge (.Block s f sp (.Lbuiltin ef args result :: bb) rs m)
        trace (.Block s f sp bb ((rs.undefRegs (destroyedByBuiltin ef)).setResult result value) m')
  | branch (s f sp rs m next bb) :
      Step ge (.Block s f sp (.Lbranch next :: bb) rs m)
        E0 (.Running s f sp next rs m)
  | condition (s f sp rs m condition args yes no bb result) :
      evalCondition condition (rs.values args) = some result →
      Step ge (.Block s f sp (.Lcond condition args yes no :: bb) rs m)
        E0 (.Running s f sp (if result then yes else no) rs m)
  | jumpTable (s f sp rs m arg table bb index next) :
      rs.reg arg = .Vint index →
      table[(Integers.Int.unsigned index).toNat]? = some next →
      Step ge (.Block s f sp (.Ljumptable arg table :: bb) rs m)
        E0 (.Running s f sp next (rs.undefRegs [.AX, .DX]) m)
  | returnValue (s f block rs m bb m') :
      Mem.free m block 0 f.fn_stacksize = some m' →
      Step ge (.Block s f (.Vptr block Integers.Ptrofs.zero) (.Lreturn :: bb) rs m)
        E0 (.Returnstate s (returnRegs (parentLocset s) rs) m')
  | internal_function (s f rs m m' block) :
      Mem.alloc m 0 f.fn_stacksize = (m', block) →
      Step ge (.Callstate s (.Internal f) rs m)
        E0 (.Running s f (.Vptr block Integers.Ptrofs.zero) f.fn_entrypoint
          ((callRegs rs).undefRegs [.AX, .FP0]) m')
  | external_function (s ef rs m trace value m') :
      externalCall ef ge.toSenv ((locArguments ef.sig).map rs) m trace value m' →
      Step ge (.Callstate s (.External ef) rs m)
        trace (.Returnstate s ((undefCallerSaveRegs rs).set (.R (locResult ef.sig)) value) m')
  | return_to_caller (frame s rs m) :
      Step ge (.Returnstate (frame :: s) rs m)
        E0 (.Block s frame.caller frame.stack frame.continuation rs m)

/-- `InitialState program s` holds when `s` calls the entry function of `program` with every
location undefined and no frames in the memory `program.initMem`, and the entry has signature
`int main(void)`. -/
inductive InitialState (program : Program) : State → Prop where
  | intro (block : Block) (function : Fundef) (memory : Mem) :
      program.initMem = some memory →
      CC.Genv.findSymbol program.globalenv program.prog_main = some block →
      CC.Genv.findFunctPtr program.globalenv block = some function →
      function.signature = mksignature [] .Xint cc_default →
      InitialState program (.Callstate [] function Locset.empty memory)

/-- `FinalState s r` holds when `s` has returned with no frames left and register `AX` holds the
integer `r`, the exit status. -/
inductive FinalState : State → Integers.Int → Prop where
  | intro (locations : Locset) (result : Integers.Int) (memory : Mem) :
      locations.reg .AX = .Vint result →
      FinalState (.Returnstate [] locations memory) result

/-- `Steps ge s t s'` is the reflexive transitive closure of `Step`, with the emitted traces
concatenated in order. -/
inductive Steps [ExternalCalls] (ge : Genv) : State → Trace → State → Prop where
  | refl (state : State) : Steps ge state [] state
  | cons {start next finish : State} {first rest : Trace} :
      Step ge start first next → Steps ge next rest finish →
      Steps ge start (first ++ rest) finish

variable [ExternalCalls] {ge : Genv}

/-- A single `Step` is a `Steps` run with the same trace. -/
theorem steps_single {start finish : State} {trace : Trace}
    (h : Step ge start trace finish) : Steps ge start trace finish := by
  simpa using Steps.cons h (.refl finish)

/-- Two consecutive `Steps` runs compose into one run whose trace is the concatenation. -/
theorem steps_trans {start middle finish : State} {left right : Trace}
    (hleft : Steps ge start left middle) (hright : Steps ge middle right finish) :
    Steps ge start (left ++ right) finish := by
  induction hleft with
  | refl => exact hright
  | cons h _ ih => simpa only [List.append_assoc] using Steps.cons h (ih hright)

/-- If `FinalState s r` holds, no `Step` leaves `s`. -/
theorem final_state_stuck {state next : State} {result : Integers.Int} {trace : Trace}
    (hfinal : FinalState state result) : ¬ Step ge state trace next := by
  cases hfinal
  intro h
  cases h

end Quadrature.LTL
