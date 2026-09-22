import Quadrature.CSource.Semantics.Reduction

/-!
# The C execution machine

The states, continuations and transitions follow CompCert's
`cfrontend/Csem.v`, at the revision recorded in `Quadrature.Clight.Source`.
Expression steps use every context allowed by `Reduction`; statement steps
enter and leave functions, allocate and free locals, and implement control flow.

`State.stuck` is explicit. A correctness proof must exclude reaching it as well
as exclude other states with no successor. This machine includes parenthesized
intermediate expressions, labels and jumps, which the terminating strategy
relation does not cover.
-/

namespace Quadrature.CSource.C.SmallStep

open CC

/-- What remains to execute after the current statement, expression or function call. -/
inductive Cont where
  | stop
  | discard (next : Cont)
  | seq (statement : Stmt) (next : Cont)
  | branch (yes no : Stmt) (next : Cont)
  | whileTest (test : Expr) (body : Stmt) (next : Cont)
  | whileBody (test : Expr) (body : Stmt) (next : Cont)
  | doBody (test : Expr) (body : Stmt) (next : Cont)
  | doTest (test : Expr) (body : Stmt) (next : Cont)
  | forTest (test : Expr) (incr body : Stmt) (next : Cont)
  | forBody (test : Expr) (incr body : Stmt) (next : Cont)
  | forIncr (test : Expr) (incr body : Stmt) (next : Cont)
  | switchTest (cases : LabeledStatements) (next : Cont)
  | switchBody (next : Cont)
  | result (next : Cont)
  | call (function : Function) (locals : Env) (context : Expr → Expr)
      (type : Ty) (next : Cont)

/-- Discard the current function's pending control flow on return. -/
def Cont.callCont : Cont → Cont
  | .stop => .stop
  | .discard next => next
  | .seq _ next | .branch _ _ next | .whileTest _ _ next | .whileBody _ _ next
  | .doBody _ _ next | .doTest _ _ next | .forTest _ _ _ next | .forBody _ _ _ next
  | .forIncr _ _ _ next | .switchTest _ next | .switchBody next | .result next =>
      next.callCont
  | next@(.call ..) => next

/-- A continuation at a function boundary. -/
def Cont.IsCall : Cont → Prop
  | .stop | .call .. => True
  | _ => False

/-- A C computation is executing a statement or expression, entering or returning from a
function, or has encountered undefined behavior. -/
inductive State where
  | statement (function : Function) (statement : Stmt) (next : Cont)
      (locals : Env) (memory : Mem)
  | expression (function : Function) (expression : Expr) (next : Cont)
      (locals : Env) (memory : Mem)
  | call (function : FunDef) (args : List Val) (next : Cont) (memory : Mem)
  | returned (value : Val) (next : Cont) (memory : Mem)
  | stuck

mutual
/-- Find a label and rebuild the continuation of its enclosing statements. -/
def findLabel (label : Ident) : Stmt → Cont → Option (Stmt × Cont)
  | .Ssequence first second, next =>
      (findLabel label first (.seq second next)).orElse fun _ => findLabel label second next
  | .Sifthenelse _ yes no, next =>
      (findLabel label yes next).orElse fun _ => findLabel label no next
  | .Swhile test body, next => findLabel label body (.whileBody test body next)
  | .Sdowhile test body, next => findLabel label body (.doBody test body next)
  | .Sfor initial test incr body, next =>
      (findLabel label initial (.seq (.Sfor .Sskip test incr body) next)).orElse fun _ =>
        (findLabel label body (.forBody test incr body next)).orElse fun _ =>
          findLabel label incr (.forIncr test incr body next)
  | .Sswitch _ cases, next => findLabelCases label cases (.switchBody next)
  | .Slabel name body, next =>
      if name = label then some (body, next) else findLabel label body next
  | _, _ => none

/-- Search switch cases with the continuation that implements fall-through. -/
def findLabelCases (label : Ident) : LabeledStatements → Cont → Option (Stmt × Cont)
  | .LSnil, _ => none
  | .LScons _ body rest, next =>
      (findLabel label body (.seq (seqOfLabeledStatement rest) next)).orElse fun _ =>
        findLabelCases label rest next
end

variable [ExternalCalls]

/-- Expression transitions, including a transition to `stuck` when any exposed subexpression
is unsafe. Entering a call suspends its expression context until the call returns. -/
inductive ExprStep (ge : GlobalEnv) : State → Trace → State → Prop where
  | lred (context function expr next locals memory result final) :
      Lred ge.expressionEnv locals expr memory result final →
      Context .LV .RV context →
      ExprStep ge (.expression function (context expr) next locals memory)
        E0 (.expression function (context result) next locals final)
  | rred (context function expr next locals memory trace result final) :
      Rred ge expr memory trace result final →
      Context .RV .RV context →
      ExprStep ge (.expression function (context expr) next locals memory)
        trace (.expression function (context result) next locals final)
  | call (context caller expr next locals memory function args type) :
      Callred ge expr memory function args type →
      Context .RV .RV context →
      ExprStep ge (.expression caller (context expr) next locals memory)
        E0 (.call function args (.call caller locals context type next) memory)
  | stuck (context function expr next locals memory kind) :
      Context kind .RV context →
      ¬ ImmSafe ge locals kind expr memory →
      ExprStep ge (.expression function (context expr) next locals memory) E0 .stuck

/-- Statement and function-boundary transitions. These are independent of expression order. -/
inductive StmtStep (ge : GlobalEnv) : State → Trace → State → Prop where
  | do_start (function expr next locals memory) :
      StmtStep ge (.statement function (.Sdo expr) next locals memory)
        E0 (.expression function expr (.discard next) locals memory)
  | do_finish (function value type next locals memory) :
      StmtStep ge (.expression function (.Eval value type) (.discard next) locals memory)
        E0 (.statement function .Sskip next locals memory)
  | seq (function first second next locals memory) :
      StmtStep ge (.statement function (.Ssequence first second) next locals memory)
        E0 (.statement function first (.seq second next) locals memory)
  | skip_seq (function statement next locals memory) :
      StmtStep ge (.statement function .Sskip (.seq statement next) locals memory)
        E0 (.statement function statement next locals memory)
  | continue_seq (function statement next locals memory) :
      StmtStep ge (.statement function .Scontinue (.seq statement next) locals memory)
        E0 (.statement function .Scontinue next locals memory)
  | break_seq (function statement next locals memory) :
      StmtStep ge (.statement function .Sbreak (.seq statement next) locals memory)
        E0 (.statement function .Sbreak next locals memory)
  | branch_start (function test yes no next locals memory) :
      StmtStep ge (.statement function (.Sifthenelse test yes no) next locals memory)
        E0 (.expression function test (.branch yes no next) locals memory)
  | branch_finish (function value type yes no next locals memory flag) :
      Cop.boolVal value type memory = some flag →
      StmtStep ge (.expression function (.Eval value type) (.branch yes no next) locals memory)
        E0 (.statement function (if flag then yes else no) next locals memory)
  | while_start (function test body next locals memory) :
      StmtStep ge (.statement function (.Swhile test body) next locals memory)
        E0 (.expression function test (.whileTest test body next) locals memory)
  | while_false (function value type test body next locals memory) :
      Cop.boolVal value type memory = some false →
      StmtStep ge
        (.expression function (.Eval value type) (.whileTest test body next) locals memory)
        E0 (.statement function .Sskip next locals memory)
  | while_true (function value type test body next locals memory) :
      Cop.boolVal value type memory = some true →
      StmtStep ge
        (.expression function (.Eval value type) (.whileTest test body next) locals memory)
        E0 (.statement function body (.whileBody test body next) locals memory)
  | while_repeat (function statement test body next locals memory) :
      statement = .Sskip ∨ statement = .Scontinue →
      StmtStep ge (.statement function statement (.whileBody test body next) locals memory)
        E0 (.statement function (.Swhile test body) next locals memory)
  | while_break (function test body next locals memory) :
      StmtStep ge (.statement function .Sbreak (.whileBody test body next) locals memory)
        E0 (.statement function .Sskip next locals memory)
  | do_start_body (function test body next locals memory) :
      StmtStep ge (.statement function (.Sdowhile test body) next locals memory)
        E0 (.statement function body (.doBody test body next) locals memory)
  | do_start_test (function statement test body next locals memory) :
      statement = .Sskip ∨ statement = .Scontinue →
      StmtStep ge (.statement function statement (.doBody test body next) locals memory)
        E0 (.expression function test (.doTest test body next) locals memory)
  | do_false (function value type test body next locals memory) :
      Cop.boolVal value type memory = some false →
      StmtStep ge (.expression function (.Eval value type) (.doTest test body next) locals memory)
        E0 (.statement function .Sskip next locals memory)
  | do_true (function value type test body next locals memory) :
      Cop.boolVal value type memory = some true →
      StmtStep ge (.expression function (.Eval value type) (.doTest test body next) locals memory)
        E0 (.statement function (.Sdowhile test body) next locals memory)
  | do_break (function test body next locals memory) :
      StmtStep ge (.statement function .Sbreak (.doBody test body next) locals memory)
        E0 (.statement function .Sskip next locals memory)
  | for_start (function initial test incr body next locals memory) :
      initial ≠ .Sskip →
      StmtStep ge (.statement function (.Sfor initial test incr body) next locals memory)
        E0 (.statement function initial (.seq (.Sfor .Sskip test incr body) next) locals memory)
  | for_test (function test incr body next locals memory) :
      StmtStep ge (.statement function (.Sfor .Sskip test incr body) next locals memory)
        E0 (.expression function test (.forTest test incr body next) locals memory)
  | for_false (function value type test incr body next locals memory) :
      Cop.boolVal value type memory = some false →
      StmtStep ge
        (.expression function (.Eval value type) (.forTest test incr body next) locals memory)
        E0 (.statement function .Sskip next locals memory)
  | for_true (function value type test incr body next locals memory) :
      Cop.boolVal value type memory = some true →
      StmtStep ge
        (.expression function (.Eval value type) (.forTest test incr body next) locals memory)
        E0 (.statement function body (.forBody test incr body next) locals memory)
  | for_increment (function statement test incr body next locals memory) :
      statement = .Sskip ∨ statement = .Scontinue →
      StmtStep ge (.statement function statement (.forBody test incr body next) locals memory)
        E0 (.statement function incr (.forIncr test incr body next) locals memory)
  | for_break (function test incr body next locals memory) :
      StmtStep ge (.statement function .Sbreak (.forBody test incr body next) locals memory)
        E0 (.statement function .Sskip next locals memory)
  | for_repeat (function test incr body next locals memory) :
      StmtStep ge (.statement function .Sskip (.forIncr test incr body next) locals memory)
        E0 (.statement function (.Sfor .Sskip test incr body) next locals memory)
  | return_void (function next locals memory final) :
      Mem.freeList memory (blocksOfEnv ge.composites locals) = some final →
      StmtStep ge (.statement function (.Sreturn none) next locals memory)
        E0 (.returned .Vundef next.callCont final)
  | return_start (function expr next locals memory) :
      StmtStep ge (.statement function (.Sreturn (some expr)) next locals memory)
        E0 (.expression function expr (.result next) locals memory)
  | return_finish (function value type next locals memory result final) :
      Cop.semCast value type function.fn_return memory = some result →
      Mem.freeList memory (blocksOfEnv ge.composites locals) = some final →
      StmtStep ge (.expression function (.Eval value type) (.result next) locals memory)
        E0 (.returned result next.callCont final)
  | return_skip (function next locals memory final) :
      next.IsCall →
      Mem.freeList memory (blocksOfEnv ge.composites locals) = some final →
      StmtStep ge (.statement function .Sskip next locals memory)
        E0 (.returned .Vundef next final)
  | switch_start (function expr cases next locals memory) :
      StmtStep ge (.statement function (.Sswitch expr cases) next locals memory)
        E0 (.expression function expr (.switchTest cases next) locals memory)
  | switch_finish (function type cases next locals memory value index) :
      Cop.semSwitchArg value type = some index →
      StmtStep ge (.expression function (.Eval value type) (.switchTest cases next) locals memory)
        E0 (.statement function (seqOfLabeledStatement (selectSwitch index cases))
          (.switchBody next) locals memory)
  | switch_stop (function statement next locals memory) :
      statement = .Sskip ∨ statement = .Sbreak →
      StmtStep ge (.statement function statement (.switchBody next) locals memory)
        E0 (.statement function .Sskip next locals memory)
  | switch_continue (function next locals memory) :
      StmtStep ge (.statement function .Scontinue (.switchBody next) locals memory)
        E0 (.statement function .Scontinue next locals memory)
  | label (function name body next locals memory) :
      StmtStep ge (.statement function (.Slabel name body) next locals memory)
        E0 (.statement function body next locals memory)
  | goto (function name next locals memory statement target) :
      findLabel name function.fn_body next.callCont = some (statement, target) →
      StmtStep ge (.statement function (.Sgoto name) next locals memory)
        E0 (.statement function statement target locals memory)
  | internal (function args next memory locals allocated entered) :
      (function.fn_params.map Prod.fst ++ function.fn_vars.map Prod.fst).Nodup →
      AllocVariables ge.expressionEnv emptyEnv memory
        (function.fn_params ++ function.fn_vars) locals allocated →
      BindParameters ge.expressionEnv locals allocated function.fn_params args entered →
      StmtStep ge (.call (.Internal function) args next memory)
        E0 (.statement function function.fn_body next locals entered)
  | external (function argsType resultType cc args next memory result trace final) :
      externalCall function (Genv.toSenv ge.globals) args memory trace result final →
      StmtStep ge (.call (.External function argsType resultType cc) args next memory)
        trace (.returned result next final)
  | resume (value function locals context type next memory) :
      StmtStep ge (.returned value (.call function locals context type next) memory)
        E0 (.expression function (context (.Eval value type)) next locals memory)

/-- One transition of the C machine, with every permitted expression reduction order. -/
def Step (ge : GlobalEnv) (initial : State) (trace : Trace) (final : State) : Prop :=
  ExprStep ge initial trace final ∨ StmtStep ge initial trace final

/-- A completed library call returns its value with no pending caller. -/
def Final (state : State) (value : Val) (memory : Mem) : Prop :=
  state = .returned value .stop memory

end Quadrature.CSource.C.SmallStep
