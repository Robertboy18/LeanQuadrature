From Coq Require Import List String.
From compcert Require Import AST Integers Floats Op CminorSel Errors.
From CminorImport Require Import ExportCminor.

Import ListNotations ExportCminor.
Local Open Scope string_scope.

(** Concrete instruction-selection output from the configured CompCert revision
    recorded in the reproduction evidence. All constructors are represented,
    with raw IEEE bits and numeric identifiers. This serializer is tooling;
    its output alone is not a semantic-preservation proof. *)
Definition condition (x : Op.condition) : string :=
  match x with
  | Ccomp x0 => node "Ccomp" [comparison x0]
  | Ccompu x0 => node "Ccompu" [comparison x0]
  | Ccompimm x0 x1 => node "Ccompimm" [comparison x0; int x1]
  | Ccompuimm x0 x1 => node "Ccompuimm" [comparison x0; int x1]
  | Ccompl x0 => node "Ccompl" [comparison x0]
  | Ccomplu x0 => node "Ccomplu" [comparison x0]
  | Ccomplimm x0 x1 => node "Ccomplimm" [comparison x0; long x1]
  | Ccompluimm x0 x1 => node "Ccompluimm" [comparison x0; long x1]
  | Ccompf x0 => node "Ccompf" [comparison x0]
  | Cnotcompf x0 => node "Cnotcompf" [comparison x0]
  | Ccompfs x0 => node "Ccompfs" [comparison x0]
  | Cnotcompfs x0 => node "Cnotcompfs" [comparison x0]
  | Cmaskzero x0 => node "Cmaskzero" [int x0]
  | Cmasknotzero x0 => node "Cmasknotzero" [int x0]
  end.

Definition addressing (x : Op.addressing) : string :=
  match x with
  | Aindexed x0 => node "Aindexed" [number x0]
  | Aindexed2 x0 => node "Aindexed2" [number x0]
  | Ascaled x0 x1 => node "Ascaled" [number x0; number x1]
  | Aindexed2scaled x0 x1 => node "Aindexed2scaled" [number x0; number x1]
  | Aglobal x0 x1 => node "Aglobal" [identifier x0; offset x1]
  | Abased x0 x1 => node "Abased" [identifier x0; offset x1]
  | Abasedscaled x0 x1 x2 => node "Abasedscaled" [number x0; identifier x1; offset x2]
  | Ainstack x0 => node "Ainstack" [offset x0]
  end.

Definition operation (x : Op.operation) : string :=
  match x with
  | Omove => "Omove"
  | Ointconst x0 => node "Ointconst" [int x0]
  | Olongconst x0 => node "Olongconst" [long x0]
  | Ofloatconst x0 => node "Ofloatconst" [float x0]
  | Osingleconst x0 => node "Osingleconst" [single x0]
  | Oindirectsymbol x0 => node "Oindirectsymbol" [identifier x0]
  | Ocast8signed => "Ocast8signed"
  | Ocast8unsigned => "Ocast8unsigned"
  | Ocast16signed => "Ocast16signed"
  | Ocast16unsigned => "Ocast16unsigned"
  | Oneg => "Oneg"
  | Osub => "Osub"
  | Omul => "Omul"
  | Omulimm x0 => node "Omulimm" [int x0]
  | Omulhs => "Omulhs"
  | Omulhu => "Omulhu"
  | Odiv => "Odiv"
  | Odivu => "Odivu"
  | Omod => "Omod"
  | Omodu => "Omodu"
  | Oand => "Oand"
  | Oandimm x0 => node "Oandimm" [int x0]
  | Oor => "Oor"
  | Oorimm x0 => node "Oorimm" [int x0]
  | Oxor => "Oxor"
  | Oxorimm x0 => node "Oxorimm" [int x0]
  | Onot => "Onot"
  | Oshl => "Oshl"
  | Oshlimm x0 => node "Oshlimm" [int x0]
  | Oshr => "Oshr"
  | Oshrimm x0 => node "Oshrimm" [int x0]
  | Oshrximm x0 => node "Oshrximm" [int x0]
  | Oshru => "Oshru"
  | Oshruimm x0 => node "Oshruimm" [int x0]
  | Ororimm x0 => node "Ororimm" [int x0]
  | Oshldimm x0 => node "Oshldimm" [int x0]
  | Olea x0 => node "Olea" [addressing x0]
  | Omakelong => "Omakelong"
  | Olowlong => "Olowlong"
  | Ohighlong => "Ohighlong"
  | Ocast32signed => "Ocast32signed"
  | Ocast32unsigned => "Ocast32unsigned"
  | Onegl => "Onegl"
  | Oaddlimm x0 => node "Oaddlimm" [long x0]
  | Osubl => "Osubl"
  | Omull => "Omull"
  | Omullimm x0 => node "Omullimm" [long x0]
  | Omullhs => "Omullhs"
  | Omullhu => "Omullhu"
  | Odivl => "Odivl"
  | Odivlu => "Odivlu"
  | Omodl => "Omodl"
  | Omodlu => "Omodlu"
  | Oandl => "Oandl"
  | Oandlimm x0 => node "Oandlimm" [long x0]
  | Oorl => "Oorl"
  | Oorlimm x0 => node "Oorlimm" [long x0]
  | Oxorl => "Oxorl"
  | Oxorlimm x0 => node "Oxorlimm" [long x0]
  | Onotl => "Onotl"
  | Oshll => "Oshll"
  | Oshllimm x0 => node "Oshllimm" [int x0]
  | Oshrl => "Oshrl"
  | Oshrlimm x0 => node "Oshrlimm" [int x0]
  | Oshrxlimm x0 => node "Oshrxlimm" [int x0]
  | Oshrlu => "Oshrlu"
  | Oshrluimm x0 => node "Oshrluimm" [int x0]
  | Ororlimm x0 => node "Ororlimm" [int x0]
  | Oleal x0 => node "Oleal" [addressing x0]
  | Onegf => "Onegf"
  | Oabsf => "Oabsf"
  | Oaddf => "Oaddf"
  | Osubf => "Osubf"
  | Omulf => "Omulf"
  | Odivf => "Odivf"
  | Omaxf => "Omaxf"
  | Ominf => "Ominf"
  | Onegfs => "Onegfs"
  | Oabsfs => "Oabsfs"
  | Oaddfs => "Oaddfs"
  | Osubfs => "Osubfs"
  | Omulfs => "Omulfs"
  | Odivfs => "Odivfs"
  | Osingleoffloat => "Osingleoffloat"
  | Ofloatofsingle => "Ofloatofsingle"
  | Ointoffloat => "Ointoffloat"
  | Ofloatofint => "Ofloatofint"
  | Ointofsingle => "Ointofsingle"
  | Osingleofint => "Osingleofint"
  | Olongoffloat => "Olongoffloat"
  | Ofloatoflong => "Ofloatoflong"
  | Olongofsingle => "Olongofsingle"
  | Osingleoflong => "Osingleoflong"
  | Ocmp x0 => node "Ocmp" [condition x0]
  | Osel x0 x1 => node "Osel" [condition x0; typ x1]
  end.

Fixpoint expression (e : CminorSel.expr) : string :=
  match e with
  | Evar id => node "Evar" [identifier id]
  | Eop op args => node "Eop" [operation op; expressions args]
  | Eload c a args => node "Eload" [chunk c; addressing a; expressions args]
  | Econdition c a b => node "Econdition" [conditional c; expression a; expression b]
  | Elet a b => node "Elet" [expression a; expression b]
  | Eletvar n => node "Eletvar" [natural n]
  | Ebuiltin ef args => node "Ebuiltin" [external ef; expressions args]
  | Eexternal id sg args =>
      node "Eexternal" [identifier id; signature sg; expressions args]
  end
with expressions (es : CminorSel.exprlist) : string :=
  match es with
  | Enil => "Enil"
  | Econs e es => node "Econs" [expression e; expressions es]
  end
with conditional (c : CminorSel.condexpr) : string :=
  match c with
  | CEcond c args => node "CEcond" [condition c; expressions args]
  | CEcondition c a b => node "CEcondition" [conditional c; conditional a; conditional b]
  | CElet e c => node "CElet" [expression e; conditional c]
  end.

Fixpoint exitexpression (e : exitexpr) : string :=
  match e with
  | XEexit n => node "XEexit" [natural n]
  | XEjumptable e ns => node "XEjumptable" [expression e; items natural ns]
  | XEcondition c a b => node "XEcondition" [conditional c; exitexpression a; exitexpression b]
  | XElet e x => node "XElet" [expression e; exitexpression x]
  end.

Fixpoint builtinarg (a : builtin_arg CminorSel.expr) : string :=
  match a with
  | BA e => node "BA" [expression e]
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

Fixpoint builtinres (r : builtin_res ident) : string :=
  match r with
  | BR id => node "BR" [identifier id]
  | BR_none => "BR_none"
  | BR_splitlong hi lo => node "BR_splitlong" [builtinres hi; builtinres lo]
  end.

Definition callee (f : CminorSel.expr + ident) : string :=
  match f with
  | inl e => node "inl" [expression e]
  | inr id => node "inr" [identifier id]
  end.

Fixpoint statement (s : CminorSel.stmt) : string :=
  match s with
  | Sskip => "Sskip"
  | Sassign id e => node "Sassign" [identifier id; expression e]
  | Sstore c a args e => node "Sstore" [chunk c; addressing a; expressions args; expression e]
  | Scall r sg f args =>
      node "Scall" [optional identifier r; signature sg; callee f; expressions args]
  | Stailcall sg f args => node "Stailcall" [signature sg; callee f; expressions args]
  | Sbuiltin r ef args => node "Sbuiltin" [builtinres r; external ef; items builtinarg args]
  | Sseq a b => node "Sseq" [statement a; statement b]
  | Sifthenelse c a b => node "Sifthenelse" [conditional c; statement a; statement b]
  | Sloop b => node "Sloop" [statement b]
  | Sblock b => node "Sblock" [statement b]
  | Sexit n => node "Sexit" [natural n]
  | Sswitch e => node "Sswitch" [exitexpression e]
  | Sreturn e => node "Sreturn" [optional expression e]
  | Slabel id b => node "Slabel" [identifier id; statement b]
  | Sgoto id => node "Sgoto" [identifier id]
  end.

Definition function (f : CminorSel.function) : string :=
  node "function" [signature (fn_sig f); items identifier (fn_params f);
    items identifier (fn_vars f); number (fn_stackspace f); statement (fn_body f)].
Definition fundef (f : CminorSel.fundef) : string :=
  match f with
  | Internal f => node "Internal" [function f]
  | External ef => node "External" [external ef]
  end.
Definition global (g : globdef CminorSel.fundef unit) : string :=
  match g with
  | Gfun f => node "Gfun" [fundef f]
  | Gvar v => node "Gvar" [items initializer (gvar_init v);
      boolean (gvar_readonly v); boolean (gvar_volatile v)]
  end.
Definition definition (g : ident * globdef CminorSel.fundef unit) : string :=
  node "pair" [identifier (fst g); global (snd g)].
Definition program (p : CminorSel.program) : string :=
  node "program" [items definition (prog_defs p); items identifier (prog_public p);
    identifier (prog_main p)].
