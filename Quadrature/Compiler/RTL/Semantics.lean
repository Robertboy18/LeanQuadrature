import Quadrature.Compiler.Cminor.Semantics
import Quadrature.Compiler.RTL.Arguments

/-!
# RTL transition rules

Small-step rules for RTL, after `backend/RTL.v`. `Step ge s t s'` is one transition
emitting trace `t`, and `Steps` is its closure. Each instruction step requires the
instruction at the current CFG node. Calls save the caller's registers in a
`Stackframe`. Entry allocates a frame, and return or tail call frees it at zero offset.
All instruction forms are present, including indirect calls and builtin arguments.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.RTL

open CC

/-- Cminor's `HasArgTypes`, reused for argument typing at function entry. -/
abbrev HasArgTypes := Cminor.HasArgTypes

/-- `Step ge s t s'` is one RTL transition from `s` to `s'` emitting trace `t`: the instruction at
the current node, a function entry, an external call, or a return to the caller. -/
inductive Step [ExternalCalls] (ge : Genv) : State → Trace → State → Prop where
  | nop (s f sp pc rs m next) :
      f.fn_code.get pc = some (.Inop next) →
      Step ge (.Running s f sp pc rs m) E0 (.Running s f sp next rs m)
  | operation (s f sp pc rs m op args result next value) :
      f.fn_code.get pc = some (.Iop op args result next) →
      evalOperation ge sp op (rs.values args) = some value →
      Step ge (.Running s f sp pc rs m) E0 (.Running s f sp next (rs.set result value) m)
  | load (s f sp pc rs m chunk address args result next pointer value) :
      f.fn_code.get pc = some (.Iload chunk address args result next) →
      evalAddressing ge sp address (rs.values args) = some pointer →
      Mem.loadv chunk m pointer = some value →
      Step ge (.Running s f sp pc rs m) E0 (.Running s f sp next (rs.set result value) m)
  | store (s f sp pc rs m chunk address args source next pointer m') :
      f.fn_code.get pc = some (.Istore chunk address args source next) →
      evalAddressing ge sp address (rs.values args) = some pointer →
      Mem.storev chunk m pointer (rs.get source) = some m' →
      Step ge (.Running s f sp pc rs m) E0 (.Running s f sp next rs m')
  | call (s f sp pc rs m signature target args result next fd) :
      f.fn_code.get pc = some (.Icall signature target args result next) →
      findFunction ge target rs = some fd →
      fd.signature = signature →
      Step ge (.Running s f sp pc rs m)
        E0 (.Callstate (⟨result, f, sp, next, rs⟩ :: s) fd (rs.values args) m)
  | tailcall (s f block pc rs m signature target args fd m') :
      f.fn_code.get pc = some (.Itailcall signature target args) →
      findFunction ge target rs = some fd →
      fd.signature = signature →
      Mem.free m block 0 f.fn_stacksize = some m' →
      Step ge (.Running s f (.Vptr block Integers.Ptrofs.zero) pc rs m)
        E0 (.Callstate s fd (rs.values args) m')
  | builtin (s f sp pc rs m ef args result next values trace value m') :
      f.fn_code.get pc = some (.Ibuiltin ef args result next) →
      EvalBuiltinArgs ge sp rs m args values →
      externalCall ef ge.toSenv values m trace value m' →
      Step ge (.Running s f sp pc rs m)
        trace (.Running s f sp next (rs.setResult result value) m')
  | branch (s f sp pc rs m condition args yes no result) :
      f.fn_code.get pc = some (.Icond condition args yes no) →
      evalCondition condition (rs.values args) = some result →
      Step ge (.Running s f sp pc rs m)
        E0 (.Running s f sp (if result then yes else no) rs m)
  | jumpTable (s f sp pc rs m arg table index next) :
      f.fn_code.get pc = some (.Ijumptable arg table) →
      rs.get arg = .Vint index →
      table[(Integers.Int.unsigned index).toNat]? = some next →
      Step ge (.Running s f sp pc rs m) E0 (.Running s f sp next rs m)
  | returnValue (s f block pc rs m result m') :
      f.fn_code.get pc = some (.Ireturn result) →
      Mem.free m block 0 f.fn_stacksize = some m' →
      Step ge (.Running s f (.Vptr block Integers.Ptrofs.zero) pc rs m)
        E0 (.Returnstate s (rs.optget result) m')
  | internal_function (s f values m m' block) :
      HasArgTypes values f.fn_sig.sig_args →
      Mem.alloc m 0 f.fn_stacksize = (m', block) →
      Step ge (.Callstate s (.Internal f) values m)
        E0 (.Running s f (.Vptr block Integers.Ptrofs.zero) f.fn_entrypoint
          (initRegs values f.fn_params) m')
  | external_function (s ef values m trace value m') :
      externalCall ef ge.toSenv values m trace value m' →
      Step ge (.Callstate s (.External ef) values m) trace (.Returnstate s value m')
  | return_to_caller (frame s value m) :
      Step ge (.Returnstate (frame :: s) value m)
        E0 (.Running s frame.caller frame.stack frame.next
          (frame.registers.set frame.result value) m)

/-- `InitialState program s` holds when `s` calls the entry function of `program` with no
arguments and no frames in the memory `program.initMem`, and the entry has signature
`int main(void)`. -/
inductive InitialState (program : Program) : State → Prop where
  | intro (block : Block) (function : Fundef) (memory : Mem) :
      program.initMem = some memory →
      CC.Genv.findSymbol program.globalenv program.prog_main = some block →
      CC.Genv.findFunctPtr program.globalenv block = some function →
      function.signature = mksignature [] .Xint cc_default →
      InitialState program (.Callstate [] function [] memory)

/-- `FinalState s r` holds when `s` has returned the integer `r` with no frames left, so `r` is
the exit status. -/
inductive FinalState : State → Integers.Int → Prop where
  | intro (result : Integers.Int) (memory : Mem) :
      FinalState (.Returnstate [] (.Vint result) memory) result

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

end Quadrature.RTL
