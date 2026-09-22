From Coq Require Import List String ZArith.
From compcert Require Import AST Maps Integers Floats Op Locations Mach.
From CminorImport Require Import ExportCminor ExportCminorSel ExportLTL.

Import ListNotations ExportCminor ExportLTL.
Local Open Scope string_scope.

Fixpoint builtinarg (a : builtin_arg Machregs.mreg) : string :=
  match a with
  | BA r => node "BA" [mreg r]
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

(** Stack offsets are serialized as byte offsets, as used by Mach.load_stack. *)
Definition instruction (i : Mach.instruction) : string :=
  match i with
  | Mop op args dst => node "Mop" [ExportCminorSel.operation op; items mreg args; mreg dst]
  | Mload c addr args dst => node "Mload" [chunk c; ExportCminorSel.addressing addr;
      items mreg args; mreg dst]
  | Mgetstack ofs ty dst => node "Mgetstack" [offset ofs; typ ty; mreg dst]
  | Msetstack src ofs ty => node "Msetstack" [mreg src; offset ofs; typ ty]
  | Mgetparam ofs ty dst => node "Mgetparam" [offset ofs; typ ty; mreg dst]
  | Mstore c addr args src => node "Mstore" [chunk c; ExportCminorSel.addressing addr;
      items mreg args; mreg src]
  | Mcall sg fn => node "Mcall" [signature sg; callee fn]
  | Mtailcall sg fn => node "Mtailcall" [signature sg; callee fn]
  | Mbuiltin ef args dst => node "Mbuiltin" [external ef; items builtinarg args; builtinres dst]
  | Mlabel lbl => node "Mlabel" [identifier lbl]
  | Mgoto lbl => node "Mgoto" [identifier lbl]
  | Mcond c args lbl => node "Mcond" [ExportCminorSel.condition c; items mreg args; identifier lbl]
  | Mjumptable r table => node "Mjumptable" [mreg r; items identifier table]
  | Mreturn => "Mreturn"
  end.

Definition function (f : Mach.function) : string :=
  node "function" [signature (fn_sig f); number (fn_stacksize f);
    offset (fn_link_ofs f); offset (fn_retaddr_ofs f); items instruction (fn_code f)].

Definition fundef (f : Mach.fundef) : string :=
  match f with
  | Internal f => node "Internal" [function f]
  | External ef => node "External" [external ef]
  end.

Definition global (g : globdef Mach.fundef unit) : string :=
  match g with
  | Gfun f => node "Gfun" [fundef f]
  | Gvar v => node "Gvar" [items initializer (gvar_init v);
      boolean (gvar_readonly v); boolean (gvar_volatile v)]
  end.

Definition definition (g : ident * globdef Mach.fundef unit) : string :=
  node "pair" [identifier (fst g); global (snd g)].

Definition program (p : Mach.program) : string :=
  node "program" [items definition (prog_defs p); items identifier (prog_public p);
    identifier (prog_main p)].
