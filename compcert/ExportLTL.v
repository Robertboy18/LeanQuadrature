From Coq Require Import List String ZArith.
From compcert Require Import AST Maps Integers Floats Op LTL Locations.
From CminorImport Require Import ExportCminor ExportCminorSel.

Import ListNotations ExportCminor.
Local Open Scope string_scope.

(** Export every location, basic block, and initialized global of the allocated program. *)
Definition mreg (r : Machregs.mreg) : string :=
  match r with
  | Machregs.AX => "AX"
  | Machregs.BX => "BX"
  | Machregs.CX => "CX"
  | Machregs.DX => "DX"
  | Machregs.SI => "SI"
  | Machregs.DI => "DI"
  | Machregs.BP => "BP"
  | Machregs.R8 => "R8"
  | Machregs.R9 => "R9"
  | Machregs.R10 => "R10"
  | Machregs.R11 => "R11"
  | Machregs.R12 => "R12"
  | Machregs.R13 => "R13"
  | Machregs.R14 => "R14"
  | Machregs.R15 => "R15"
  | Machregs.X0 => "X0"
  | Machregs.X1 => "X1"
  | Machregs.X2 => "X2"
  | Machregs.X3 => "X3"
  | Machregs.X4 => "X4"
  | Machregs.X5 => "X5"
  | Machregs.X6 => "X6"
  | Machregs.X7 => "X7"
  | Machregs.X8 => "X8"
  | Machregs.X9 => "X9"
  | Machregs.X10 => "X10"
  | Machregs.X11 => "X11"
  | Machregs.X12 => "X12"
  | Machregs.X13 => "X13"
  | Machregs.X14 => "X14"
  | Machregs.X15 => "X15"
  | Machregs.FP0 => "FP0"
  end.
Definition slot (s : Locations.slot) : string :=
  match s with Local => "Local" | Incoming => "Incoming" | Outgoing => "Outgoing" end.
Definition location (l : loc) : string :=
  match l with
  | R r => node "R" [mreg r]
  | S s ofs ty => node "S" [slot s; number ofs; typ ty]
  end.
Fixpoint builtinres (r : builtin_res Machregs.mreg) : string :=
  match r with
  | BR r => node "BR" [mreg r]
  | BR_none => "BR_none"
  | BR_splitlong hi lo => node "BR_splitlong" [builtinres hi; builtinres lo]
  end.

Fixpoint builtinarg (a : builtin_arg loc) : string :=
  match a with
  | BA r => node "BA" [location r]
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

Definition callee (f : Machregs.mreg + ident) : string :=
  match f with
  | inl r => node "inl" [mreg r]
  | inr id => node "inr" [identifier id]
  end.

Definition instruction (i : LTL.instruction) : string :=
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
  | Lbranch pc => node "Lbranch" [identifier pc]
  | Lcond c args yes no => node "Lcond" [ExportCminorSel.condition c; items mreg args;
      identifier yes; identifier no]
  | Ljumptable r table => node "Ljumptable" [mreg r; items identifier table]
  | Lreturn => "Lreturn"
  end.
Definition binding (p : positive * LTL.bblock) : string :=
  node "pair" [identifier (fst p); items instruction (snd p)].
Definition function (f : LTL.function) : string :=
  node "function" [signature (fn_sig f); number (fn_stacksize f);
    items binding (PTree.elements (fn_code f)); identifier (fn_entrypoint f)].
Definition fundef (f : LTL.fundef) : string :=
  match f with
  | Internal f => node "Internal" [function f]
  | External ef => node "External" [external ef]
  end.
Definition global (g : globdef LTL.fundef unit) : string :=
  match g with
  | Gfun f => node "Gfun" [fundef f]
  | Gvar v => node "Gvar" [items initializer (gvar_init v);
      boolean (gvar_readonly v); boolean (gvar_volatile v)]
  end.
Definition definition (g : ident * globdef LTL.fundef unit) : string :=
  node "pair" [identifier (fst g); global (snd g)].
Definition program (p : LTL.program) : string :=
  node "program" [items definition (prog_defs p); items identifier (prog_public p);
    identifier (prog_main p)].
