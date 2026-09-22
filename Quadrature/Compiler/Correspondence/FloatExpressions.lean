import CCLib.ClightExecSound
import Quadrature.Compiler.Correspondence.ValueRelation

/-!
# Lowering double expressions from Clight to Cminor

Relates Clight and Cminor double expressions for the ten programs. Read
`FloatExprLowering` first: a syntax relation for binary64 constants, renamed temporaries,
and the four separately rounded operations. `FloatExprLowering.eval_preserved` shows every
successful Clight evaluation has a related Cminor result under `LocalsAgree`, which allows
extra target variables and preserves assignments under an injective renaming. No memory
relation is needed, because the fragment has no loads or addresses.

Vocabulary and scope: `Quadrature.Compiler.Execution.Run`.
-/

namespace Quadrature.Compiler

open CC

/-- Every bound source temporary has a related value at its renamed target identifier. -/
def LocalsAgree (mapping : BlockMap) (rename : Ident → Ident)
    (source : TempEnv) (target : Cminor.Env) : Prop :=
  ∀ id value, source.get id = some value →
    ∃ value', target.get (rename id) = some value' ∧ ValuesAgree mapping value value'

namespace LocalsAgree

/-- Empty environments agree under any map and renaming. -/
theorem empty (mapping : BlockMap) (rename : Ident → Ident) :
    LocalsAgree mapping rename PTree.empty PTree.empty := by
  intro id value h
  simp only [PTree.gempty, reduceCtorEq] at h

/-- Setting a source temporary and its renamed target variable to related values `hv` preserves
agreement, given an injective renaming `hinj`. -/
theorem set {mapping : BlockMap} {rename : Ident → Ident}
    {source : TempEnv} {target : Cminor.Env}
    (h : LocalsAgree mapping rename source target) (hinj : Function.Injective rename)
    (id : Ident) {value value' : Val} (hv : ValuesAgree mapping value value') :
    LocalsAgree mapping rename (source.set id value) (target.set (rename id) value') := by
  intro other v hget
  by_cases heq : id = other
  · subst other
    rw [PTree.gss] at hget
    cases Option.some.inj hget
    exact ⟨value', PTree.gss _ _ _, hv⟩
  · rw [PTree.gso _ _ _ _ heq] at hget
    obtain ⟨v', htarget, hval⟩ := h other v hget
    exact ⟨v', (PTree.gso _ _ _ _ (fun h' => heq (hinj h'))).trans htarget, hval⟩

end LocalsAgree

/-- The four binary operations on C doubles, with their Cminor counterparts. -/
inductive DoubleOp where
  | add | sub | mul | div

/-- The Clight binary operator of a double operation. -/
def DoubleOp.source : DoubleOp → Binop
  | .add => .Oadd
  | .sub => .Osub
  | .mul => .Omul
  | .div => .Odiv

/-- The Cminor float operator of a double operation. -/
def DoubleOp.target : DoubleOp → Cminor.BinaryOp
  | .add => .Oaddf
  | .sub => .Osubf
  | .mul => .Omulf
  | .div => .Odivf

/-- The binary64 function both operators compute. -/
def DoubleOp.apply : DoubleOp → Floats.Float → Floats.Float → Floats.Float
  | .add => Floats.Float.add
  | .sub => Floats.Float.sub
  | .mul => Floats.Float.mul
  | .div => Floats.Float.div

/-- Clight evaluates `op.source` on two doubles as `op.apply`. -/
theorem DoubleOp.source_semantics (op : DoubleOp) (ce : CompositeEnv) (m : Mem)
    (x y : Floats.Float) :
    Cop.semBinaryOperation ce op.source (.Vfloat x) tdouble (.Vfloat y) tdouble m =
      some (.Vfloat (op.apply x y)) := by
  cases op <;> rfl

/-- Cminor evaluates `op.target` on two floats as `op.apply`. -/
theorem DoubleOp.target_semantics (op : DoubleOp) (m : Mem) (x y : Floats.Float) :
    Cminor.evalBinary op.target (.Vfloat x) (.Vfloat y) m =
      some (.Vfloat (op.apply x y)) := by
  cases op <;> rfl

/-- A successful Clight evaluation `h` of `op.source` at double type has float operands and
result. -/
theorem DoubleOp.source_inputs (op : DoubleOp) (ce : CompositeEnv) (m : Mem)
    {left right value : Val}
    (h : Cop.semBinaryOperation ce op.source left tdouble right tdouble m = some value) :
    ∃ x y, left = .Vfloat x ∧ right = .Vfloat y ∧ value = .Vfloat (op.apply x y) := by
  cases op <;> cases left <;> cases right <;>
    first
    | exact ⟨_, _, rfl, rfl, (Option.some.inj h).symm⟩
    | contradiction

/-- A syntax relation for constants, renamed temporaries, and binary double arithmetic. -/
inductive FloatExprLowering (rename : Ident → Ident) : Expr → Cminor.Expr → Prop where
  | constant (value : Floats.Float) :
      FloatExprLowering rename (.Econst_float value tdouble)
        (.Econst (.Ofloatconst value))
  | temp (id : Ident) :
      FloatExprLowering rename (.Etempvar id tdouble) (.Evar (rename id))
  | binary (op : DoubleOp) {left right : Expr} {left' right' : Cminor.Expr} :
      FloatExprLowering rename left left' → FloatExprLowering rename right right' →
      FloatExprLowering rename (.Ebinop op.source left right tdouble)
        (.Ebinop op.target left' right')

namespace FloatExprLowering

/-- Every lowered source expression has type `double`. -/
theorem source_type {rename : Ident → Ident} {source : Expr} {target : Cminor.Expr}
    (h : FloatExprLowering rename source target) : typeof source = tdouble := by
  cases h <;> rfl

/-- Every successful source evaluation yields a related target value. -/
theorem eval_preserved {mapping : BlockMap} {rename : Ident → Ident}
    {source : Expr} {target : Cminor.Expr}
    (h : FloatExprLowering rename source target)
    (sourceGe : CGenv) (targetGe : Cminor.Genv) (e : Env) (stack : Val)
    (sourceMemory targetMemory : Mem) (sourceLocals : TempEnv) (targetLocals : Cminor.Env)
    (hlocals : LocalsAgree mapping rename sourceLocals targetLocals)
    {value : Val} (heval : doEvalExpr sourceGe e sourceLocals sourceMemory source = some value) :
    ∃ value', Cminor.evalExpr targetGe stack targetLocals targetMemory target = some value' ∧
      ValuesAgree mapping value value' := by
  induction h generalizing value with
  | constant f =>
    cases Option.some.inj heval
    exact ⟨_, rfl, .float f⟩
  | temp id => exact hlocals id value heval
  | @binary op left right left' right' hl hr ihl ihr =>
    simp only [doEvalExpr] at heval
    cases hleft : doEvalExpr sourceGe e sourceLocals sourceMemory left with
    | none => simp only [hleft] at heval; contradiction
    | some vl =>
      cases hright : doEvalExpr sourceGe e sourceLocals sourceMemory right with
      | none => simp only [hleft, hright] at heval; contradiction
      | some vr =>
        simp only [hleft, hright, hl.source_type, hr.source_type] at heval
        obtain ⟨x, y, rfl, rfl, rfl⟩ := op.source_inputs _ _ heval
        obtain ⟨vx, hx, hrelx⟩ := ihl hleft
        obtain ⟨vy, hy, hrely⟩ := ihr hright
        cases hrelx
        cases hrely
        refine ⟨_, ?_, .float _⟩
        simp only [Cminor.evalExpr, hx, hy, bind, Option.bind_some, op.target_semantics]

/-- On this syntactic fragment, the Clight evaluator is complete for the relational rules. -/
theorem source_eval_complete {rename : Ident → Ident} {source : Expr} {target : Cminor.Expr}
    (h : FloatExprLowering rename source target)
    {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {value : Val}
    (heval : EvalExpr ge e le m source value) :
    doEvalExpr ge e le m source = some value := by
  induction h generalizing value with
  | constant f =>
    cases heval with
    | Econst_float => rfl
    | Elvalue _ _ _ _ _ hl _ => cases hl
  | temp id =>
    cases heval with
    | Etempvar _ _ _ hv => exact hv
    | Elvalue _ _ _ _ _ hl _ => cases hl
  | binary op _ _ ihl ihr =>
    cases heval with
    | Ebinop _ _ _ _ _ _ _ hl hr hop =>
      simpa only [doEvalExpr, ihl hl, ihr hr] using hop
    | Elvalue _ _ _ _ _ hl _ => cases hl

/-- Preservation stated directly between the two relational expression semantics. -/
theorem eval_relation_preserved {mapping : BlockMap} {rename : Ident → Ident}
    {source : Expr} {target : Cminor.Expr}
    (h : FloatExprLowering rename source target)
    (sourceGe : CGenv) (targetGe : Cminor.Genv) (e : Env) (stack : Val)
    (sourceMemory targetMemory : Mem) (sourceLocals : TempEnv) (targetLocals : Cminor.Env)
    (hlocals : LocalsAgree mapping rename sourceLocals targetLocals)
    {value : Val} (heval : EvalExpr sourceGe e sourceLocals sourceMemory source value) :
    ∃ value', Cminor.EvalExpr targetGe stack targetLocals targetMemory target value' ∧
      ValuesAgree mapping value value' := by
  obtain ⟨value', hv, hrel⟩ := h.eval_preserved sourceGe targetGe e stack
    sourceMemory targetMemory sourceLocals targetLocals hlocals (h.source_eval_complete heval)
  exact ⟨value', Cminor.eval_expr_sound hv, hrel⟩

end FloatExprLowering

end Quadrature.Compiler
