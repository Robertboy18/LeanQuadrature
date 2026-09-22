import Quadrature.Compiler.Cminor.Semantics
import Quadrature.Compiler.Linear.Syntax

/-!
# Linear transition rules

Small-step rules for Linear, after `backend/Linear.v` on x86-64 ELF. Read `Step` first,
one transition of a Linear state under a global environment, emitting a trace. Labels
advance to the next instruction. Jumps search the whole function body and resume after
the first matching label, and a false condition falls through. Registers, abstract stack
slots, and calling conventions follow LTL. A `Running` state with no instructions left
has no rule.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Linear

open CC

/-- One Linear transition under global environment `ge`, emitting a trace. Each constructor
mirrors one rule of `backend/Linear.v`. Builtins and external functions step by the
external-call relation `externalCall`. -/
inductive Step [ExternalCalls] (ge : Genv) : State → Trace → State → Prop where
  | operation (s f sp rs m op args result bb value) :
      evalOperation ge sp op (rs.values args) = some value →
      Step ge (.Running s f sp (.Lop op args result :: bb) rs m)
        E0 (.Running s f sp bb ((rs.undefRegs (destroyedByOp op)).set (.R result) value) m)
  | load (s f sp rs m chunk address args result bb pointer value) :
      evalAddressing ge sp address (rs.values args) = some pointer →
      Mem.loadv chunk m pointer = some value →
      Step ge (.Running s f sp (.Lload chunk address args result :: bb) rs m)
        E0 (.Running s f sp bb (rs.set (.R result) value) m)
  | getstack (s f sp rs m slot offset type result bb) :
      Step ge (.Running s f sp (.Lgetstack slot offset type result :: bb) rs m)
        E0 (.Running s f sp bb ((rs.undefRegs (destroyedByGetstack slot)).set
          (.R result) (rs (.S slot offset type))) m)
  | setstack (s f sp rs m source slot offset type bb) :
      Step ge (.Running s f sp (.Lsetstack source slot offset type :: bb) rs m)
        E0 (.Running s f sp bb ((rs.undefRegs (destroyedBySetstack type)).set
          (.S slot offset type) (rs.reg source)) m)
  | store (s f sp rs m chunk address args source bb pointer m') :
      evalAddressing ge sp address (rs.values args) = some pointer →
      Mem.storev chunk m pointer (rs.reg source) = some m' →
      Step ge (.Running s f sp (.Lstore chunk address args source :: bb) rs m)
        E0 (.Running s f sp bb rs m')
  | call (s f sp rs m signature target bb fd) :
      findFunction ge target rs = some fd →
      fd.signature = signature →
      Step ge (.Running s f sp (.Lcall signature target :: bb) rs m)
        E0 (.Callstate (⟨f, sp, rs, bb⟩ :: s) fd rs m)
  | tailcall (s f block rs m signature target bb fd m') :
      findFunction ge target (returnRegs (parentLocset s) rs) = some fd →
      fd.signature = signature →
      Mem.free m block 0 f.fn_stacksize = some m' →
      Step ge (.Running s f (.Vptr block Integers.Ptrofs.zero)
          (.Ltailcall signature target :: bb) rs m)
        E0 (.Callstate s fd (returnRegs (parentLocset s) rs) m')
  | builtin (s f sp rs m ef args result bb values trace value m') :
      EvalBuiltinArgs ge sp rs m args values →
      externalCall ef ge.toSenv values m trace value m' →
      Step ge (.Running s f sp (.Lbuiltin ef args result :: bb) rs m)
        trace (.Running s f sp bb
          ((rs.undefRegs (destroyedByBuiltin ef)).setResult result value) m')
  | label (s f sp rs m label bb) :
      Step ge (.Running s f sp (.Llabel label :: bb) rs m)
        E0 (.Running s f sp bb rs m)
  | goto (s f sp rs m label bb target) :
      findLabel label f.fn_code = some target →
      Step ge (.Running s f sp (.Lgoto label :: bb) rs m)
        E0 (.Running s f sp target rs m)
  | condition_true (s f sp rs m condition args label bb target) :
      evalCondition condition (rs.values args) = some true →
      findLabel label f.fn_code = some target →
      Step ge (.Running s f sp (.Lcond condition args label :: bb) rs m)
        E0 (.Running s f sp target rs m)
  | condition_false (s f sp rs m condition args label bb) :
      evalCondition condition (rs.values args) = some false →
      Step ge (.Running s f sp (.Lcond condition args label :: bb) rs m)
        E0 (.Running s f sp bb rs m)
  | jumpTable (s f sp rs m arg table bb index label target) :
      rs.reg arg = .Vint index →
      table[(Integers.Int.unsigned index).toNat]? = some label →
      findLabel label f.fn_code = some target →
      Step ge (.Running s f sp (.Ljumptable arg table :: bb) rs m)
        E0 (.Running s f sp target (rs.undefRegs [.AX, .DX]) m)
  | returnValue (s f block rs m bb m') :
      Mem.free m block 0 f.fn_stacksize = some m' →
      Step ge (.Running s f (.Vptr block Integers.Ptrofs.zero) (.Lreturn :: bb) rs m)
        E0 (.Returnstate s (returnRegs (parentLocset s) rs) m')
  | internal_function (s f rs m m' block) :
      Mem.alloc m 0 f.fn_stacksize = (m', block) →
      Step ge (.Callstate s (.Internal f) rs m)
        E0 (.Running s f (.Vptr block Integers.Ptrofs.zero) f.fn_code
          ((callRegs rs).undefRegs [.AX, .FP0]) m')
  | external_function (s ef rs m trace value m') :
      externalCall ef ge.toSenv ((locArguments ef.sig).map rs) m trace value m' →
      Step ge (.Callstate s (.External ef) rs m)
        trace (.Returnstate s ((undefCallerSaveRegs rs).set (.R (locResult ef.sig)) value) m')
  | return_to_caller (frame s rs m) :
      Step ge (.Returnstate (frame :: s) rs m)
        E0 (.Running s frame.caller frame.stack frame.continuation rs m)

/-- The initial state of `program`: a call to the function named by `prog_main`, which must
have the signature of `int main(void)`, in the program's initial memory. -/
inductive InitialState (program : Program) : State → Prop where
  | intro (block : Block) (function : Fundef) (memory : Mem) :
      program.initMem = some memory →
      CC.Genv.findSymbol program.globalenv program.prog_main = some block →
      CC.Genv.findFunctPtr program.globalenv block = some function →
      function.signature = mksignature [] .Xint cc_default →
      InitialState program (.Callstate [] function LTL.Locset.empty memory)

/-- A final state is a `Returnstate` with no frames whose `AX` holds the integer exit status. -/
inductive FinalState : State → Integers.Int → Prop where
  | intro (locations : Locset) (result : Integers.Int) (memory : Mem) :
      locations.reg .AX = .Vint result →
      FinalState (.Returnstate [] locations memory) result

/-- Finite sequences of transitions, concatenating their traces. -/
inductive Steps [ExternalCalls] (ge : Genv) : State → Trace → State → Prop where
  | refl (state : State) : Steps ge state [] state
  | cons {start next finish : State} {first rest : Trace} :
      Step ge start first next → Steps ge next rest finish →
      Steps ge start (first ++ rest) finish

variable [ExternalCalls] {ge : Genv}

/-- A single transition `h` is a one-step sequence with the same trace. -/
theorem steps_single {start finish : State} {trace : Trace}
    (h : Step ge start trace finish) : Steps ge start trace finish := by
  simpa using Steps.cons h (.refl finish)

/-- Two sequences `hleft` and `hright` compose, concatenating their traces. -/
theorem steps_trans {start middle finish : State} {left right : Trace}
    (hleft : Steps ge start left middle) (hright : Steps ge middle right finish) :
    Steps ge start (left ++ right) finish := by
  induction hleft with
  | refl => exact hright
  | cons h _ ih => simpa only [List.append_assoc] using Steps.cons h (ih hright)

/-- No transition leaves a final state `hfinal`. -/
theorem final_state_stuck {state next : State} {result : Integers.Int} {trace : Trace}
    (hfinal : FinalState state result) : ¬ Step ge state trace next := by
  cases hfinal
  intro h
  cases h

end Quadrature.Linear
