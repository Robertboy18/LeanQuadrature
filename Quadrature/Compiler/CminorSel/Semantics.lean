import Quadrature.Compiler.Cminor.Semantics
import Quadrature.Compiler.CminorSel.Arguments

/-!
# CminorSel transition rules

Small-step rules for CminorSel, after `backend/CminorSel.v`, restricted only by the
expression and operation syntax in this development. `Step ge s t s'` is one transition
emitting trace `t`, and `Steps` is its closure. Direct and indirect calls, stores,
builtin arguments, conditional exits, tail calls, and labels each follow their upstream
rule. Function entry allocates a frame. Return and tail call require the zero-offset
stack pointer and free the frame. Argument typing reuses Cminor's `HasArgTypes`.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.CminorSel

open CC

/-- Cminor's `HasArgTypes`, reused for argument typing at function entry. -/
abbrev HasArgTypes := Cminor.HasArgTypes

/-- `Step ge s t s'` is one CminorSel transition from `s` to `s'` emitting trace `t`. Only builtins
and external functions emit events. -/
inductive Step [ExternalCalls] (ge : Genv) : State → Trace → State → Prop where
  | skip_seq (f s k sp e m) :
      Step ge (.Running f .Sskip (.Kseq s k) sp e m) E0 (.Running f s k sp e m)
  | skip_block (f k sp e m) :
      Step ge (.Running f .Sskip (.Kblock k) sp e m) E0 (.Running f .Sskip k sp e m)
  | skip_call (f k sp e m m') :
      IsCallCont k →
      Mem.free m sp 0 f.fn_stackspace = some m' →
      Step ge (.Running f .Sskip k (.Vptr sp Integers.Ptrofs.zero) e m)
        E0 (.Returnstate .Vundef k m')
  | assign (f name a k sp e m v) :
      EvalExpr ge sp e m [] a v →
      Step ge (.Running f (.Sassign name a) k sp e m)
        E0 (.Running f .Sskip k sp (e.set name v) m)
  | store (f chunk address args a k sp e m values v pointer m') :
      EvalExprList ge sp e m [] args values →
      EvalExpr ge sp e m [] a v →
      evalAddressing ge sp address values = some pointer →
      Mem.storev chunk m pointer v = some m' →
      Step ge (.Running f (.Sstore chunk address args a) k sp e m)
        E0 (.Running f .Sskip k sp e m')
  | call (f result signature a args k sp e m vf values fd) :
      EvalExprOrSymbol ge sp e m [] a vf →
      EvalExprList ge sp e m [] args values →
      CC.Genv.findFunct ge vf = some fd →
      fd.signature = signature →
      Step ge (.Running f (.Scall result signature a args) k sp e m)
        E0 (.Callstate fd values (.Kcall result f sp e k) m)
  | tailcall (f signature a args k sp e m vf values fd m') :
      EvalExprOrSymbol ge (.Vptr sp Integers.Ptrofs.zero) e m [] a vf →
      EvalExprList ge (.Vptr sp Integers.Ptrofs.zero) e m [] args values →
      CC.Genv.findFunct ge vf = some fd →
      fd.signature = signature →
      Mem.free m sp 0 f.fn_stackspace = some m' →
      Step ge (.Running f (.Stailcall signature a args) k (.Vptr sp Integers.Ptrofs.zero) e m)
        E0 (.Callstate fd values (callCont k) m')
  | builtin (f result ef args k sp e m values trace v m') :
      EvalBuiltinArgs ge sp e m args values →
      externalCall ef ge.toSenv values m trace v m' →
      Step ge (.Running f (.Sbuiltin result ef args) k sp e m)
        trace (.Running f .Sskip k sp (setBuiltinRes result v e) m')
  | seq (f first second k sp e m) :
      Step ge (.Running f (.Sseq first second) k sp e m)
        E0 (.Running f first (.Kseq second k) sp e m)
  | branch (f condition yes no k sp e m b) :
      EvalCondExpr ge sp e m [] condition b →
      Step ge (.Running f (.Sifthenelse condition yes no) k sp e m)
        E0 (.Running f (if b then yes else no) k sp e m)
  | loop (f body k sp e m) :
      Step ge (.Running f (.Sloop body) k sp e m)
        E0 (.Running f body (.Kseq (.Sloop body) k) sp e m)
  | block (f body k sp e m) :
      Step ge (.Running f (.Sblock body) k sp e m)
        E0 (.Running f body (.Kblock k) sp e m)
  | exit_seq (f depth s k sp e m) :
      Step ge (.Running f (.Sexit depth) (.Kseq s k) sp e m)
        E0 (.Running f (.Sexit depth) k sp e m)
  | exit_block_zero (f k sp e m) :
      Step ge (.Running f (.Sexit 0) (.Kblock k) sp e m)
        E0 (.Running f .Sskip k sp e m)
  | exit_block_succ (f depth k sp e m) :
      Step ge (.Running f (.Sexit (depth + 1)) (.Kblock k) sp e m)
        E0 (.Running f (.Sexit depth) k sp e m)
  | switch (f a k sp e m depth) :
      EvalExitExpr ge sp e m [] a depth →
      Step ge (.Running f (.Sswitch a) k sp e m)
        E0 (.Running f (.Sexit depth) k sp e m)
  | return_none (f k sp e m m') :
      Mem.free m sp 0 f.fn_stackspace = some m' →
      Step ge (.Running f (.Sreturn none) k (.Vptr sp Integers.Ptrofs.zero) e m)
        E0 (.Returnstate .Vundef (callCont k) m')
  | return_some (f a k sp e m v m') :
      EvalExpr ge (.Vptr sp Integers.Ptrofs.zero) e m [] a v →
      Mem.free m sp 0 f.fn_stackspace = some m' →
      Step ge (.Running f (.Sreturn (some a)) k (.Vptr sp Integers.Ptrofs.zero) e m)
        E0 (.Returnstate v (callCont k) m')
  | label (f name body k sp e m) :
      Step ge (.Running f (.Slabel name body) k sp e m) E0 (.Running f body k sp e m)
  | goto (f name k sp e m s' k') :
      findLabel name f.fn_body (callCont k) = some (s', k') →
      Step ge (.Running f (.Sgoto name) k sp e m) E0 (.Running f s' k' sp e m)
  | internal_function (f values k m m' sp e) :
      HasArgTypes values f.fn_sig.sig_args →
      Mem.alloc m 0 f.fn_stackspace = (m', sp) →
      setLocals f.fn_vars (setParams values f.fn_params) = e →
      Step ge (.Callstate (.Internal f) values k m)
        E0 (.Running f f.fn_body k (.Vptr sp Integers.Ptrofs.zero) e m')
  | external_function (ef values k m trace v m') :
      externalCall ef ge.toSenv values m trace v m' →
      Step ge (.Callstate (.External ef) values k m) trace (.Returnstate v k m')
  | return_to_caller (v result f sp e k m) :
      Step ge (.Returnstate v (.Kcall result f sp e k) m)
        E0 (.Running f .Sskip k sp (setOptvar result v e) m)

/-- `InitialState program s` holds when `s` calls the entry function of `program` with no
arguments in the memory `program.initMem`, and the entry has signature `int main(void)`. -/
inductive InitialState (program : Program) : State → Prop where
  | intro (block : Block) (function : Fundef) (memory : Mem) :
      program.initMem = some memory →
      CC.Genv.findSymbol program.globalenv program.prog_main = some block →
      CC.Genv.findFunctPtr program.globalenv block = some function →
      function.signature = mksignature [] .Xint cc_default →
      InitialState program (.Callstate function [] .Kstop memory)

/-- `FinalState s r` holds when `s` has returned the integer `r` to the `Kstop` continuation,
so `r` is the exit status. -/
inductive FinalState : State → Integers.Int → Prop where
  | intro (result : Integers.Int) (memory : Mem) :
      FinalState (.Returnstate (.Vint result) .Kstop memory) result

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

end Quadrature.CminorSel
