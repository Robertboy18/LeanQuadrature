From Coq Require Import List String ZArith.
From compcert Require Import AST Maps Integers Floats Op Locations Linear.
From CminorImport Require Import ExportCminor ExportCminorSel ExportLTL.

Import ListNotations ExportCminor ExportLTL.
Local Open Scope string_scope.

(** Export every instruction, label, and initialized global before stack layout. *)
Definition instruction (i : Linear.instruction) : string :=
  match i with
  | Lop op args dst => node "Lop" [ExportCminorSel.operation op; items mreg args; mreg dst]
  | Lload c addr args dst => node "Lload" [chunk c; ExportCminorSel.addressing addr;
      items mreg args; mreg dst]
  | Lgetstack s ofs ty dst => node "Lgetstack" [slot s; number ofs; typ ty; mreg dst]
  | Lsetstack src s ofs ty => node "Lsetstack" [mreg src; slot s; number ofs; typ ty]
  | Lstore c addr args src => node "Lstore" [chunk c; ExportCminorSel.addressing addr;
      items mreg args; mreg src]
  | Lcall sg fn => node "Lcall" [signature sg; callee fn]
  | Ltailcall sg fn => node "Ltailcall" [signature sg; callee fn]
  | Lbuiltin ef args dst => node "Lbuiltin" [external ef; items builtinarg args; builtinres dst]
  | Llabel lbl => node "Llabel" [identifier lbl]
  | Lgoto lbl => node "Lgoto" [identifier lbl]
  | Lcond c args lbl => node "Lcond" [ExportCminorSel.condition c; items mreg args; identifier lbl]
  | Ljumptable r table => node "Ljumptable" [mreg r; items identifier table]
  | Lreturn => "Lreturn"
  end.

Definition function (f : Linear.function) : string :=
  node "function" [signature (fn_sig f); number (fn_stacksize f); items instruction (fn_code f)].

Definition fundef (f : Linear.fundef) : string :=
  match f with
  | Internal f => node "Internal" [function f]
  | External ef => node "External" [external ef]
  end.

Definition global (g : globdef Linear.fundef unit) : string :=
  match g with
  | Gfun f => node "Gfun" [fundef f]
  | Gvar v => node "Gvar" [items initializer (gvar_init v);
      boolean (gvar_readonly v); boolean (gvar_volatile v)]
  end.

Definition definition (g : ident * globdef Linear.fundef unit) : string :=
  node "pair" [identifier (fst g); global (snd g)].

Definition program (p : Linear.program) : string :=
  node "program" [items definition (prog_defs p); items identifier (prog_public p);
    identifier (prog_main p)].
