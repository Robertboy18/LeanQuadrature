From Coq Require Import List String ZArith.
From compcert Require Import AST Maps Integers Floats Op RTL.
From CminorImport Require Import ExportCminor ExportCminorSel.

Import ListNotations ExportCminor.
Local Open Scope string_scope.

(** Export actual RTL code with its numeric CFG nodes and pseudo-registers.
    The representation keeps every global and constant. Its two renderings
    still require a separate interpretation between Lean and Rocq. *)
Fixpoint builtinarg (a : builtin_arg positive) : string :=
  match a with
  | BA r => node "BA" [identifier r]
  | BA_int n => node "BA_int" [int n]
  | BA_long n => node "BA_long" [long n]
  | BA_float f => node "BA_float" [float f]
  | BA_single f => node "BA_single" [single f]
  | BA_loadstack c ofs => node "BA_loadstack" [chunk c; offset ofs]
  | BA_addrstack ofs => node "BA_addrstack" [offset ofs]
  | BA_loadglobal c id ofs => node "BA_loadglobal" [chunk c; identifier id; offset ofs]
  | BA_addrglobal id ofs => node "BA_addrglobal" [identifier id; offset ofs]
  | BA_splitlong hi lo => node "BA_splitlong" [builtinarg hi; builtinarg lo]
  | BA_addptr a b => node "BA_addptr" [builtinarg a; builtinarg b]
  end.

Definition callee (f : positive + ident) : string :=
  match f with
  | inl r => node "inl" [identifier r]
  | inr id => node "inr" [identifier id]
  end.

Definition instruction (i : RTL.instruction) : string :=
  match i with
  | Inop pc => node "Inop" [identifier pc]
  | Iop op args dst pc =>
      node "Iop" [ExportCminorSel.operation op; items identifier args;
        identifier dst; identifier pc]
  | Iload c addr args dst pc =>
      node "Iload" [chunk c; ExportCminorSel.addressing addr; items identifier args;
        identifier dst; identifier pc]
  | Istore c addr args src pc =>
      node "Istore" [chunk c; ExportCminorSel.addressing addr; items identifier args;
        identifier src; identifier pc]
  | Icall sg fn args dst pc =>
      node "Icall" [signature sg; callee fn; items identifier args;
        identifier dst; identifier pc]
  | Itailcall sg fn args => node "Itailcall" [signature sg; callee fn; items identifier args]
  | Ibuiltin ef args dst pc =>
      node "Ibuiltin" [external ef; items builtinarg args;
        ExportCminorSel.builtinres dst; identifier pc]
  | Icond c args yes no =>
      node "Icond" [ExportCminorSel.condition c; items identifier args;
        identifier yes; identifier no]
  | Ijumptable r table => node "Ijumptable" [identifier r; items identifier table]
  | Ireturn r => node "Ireturn" [optional identifier r]
  end.

Definition binding (p : positive * RTL.instruction) : string :=
  node "pair" [identifier (fst p); instruction (snd p)].

Definition function (f : RTL.function) : string :=
  node "function" [signature (fn_sig f); items identifier (fn_params f);
    number (fn_stacksize f); items binding (PTree.elements (fn_code f));
    identifier (fn_entrypoint f)].
Definition fundef (f : RTL.fundef) : string :=
  match f with
  | Internal f => node "Internal" [function f]
  | External ef => node "External" [external ef]
  end.
Definition global (g : globdef RTL.fundef unit) : string :=
  match g with
  | Gfun f => node "Gfun" [fundef f]
  | Gvar v => node "Gvar" [items initializer (gvar_init v);
      boolean (gvar_readonly v); boolean (gvar_volatile v)]
  end.
Definition definition (g : ident * globdef RTL.fundef unit) : string :=
  node "pair" [identifier (fst g); global (snd g)].
Definition program (p : RTL.program) : string :=
  node "program" [items definition (prog_defs p); items identifier (prog_public p);
    identifier (prog_main p)].
