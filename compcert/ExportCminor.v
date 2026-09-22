From Coq Require Import List String Ascii ZArith DecimalString.
From compcert Require Import AST Integers Floats Cminor Errors.

Import ListNotations.
Local Open Scope string_scope.

(** Lossless concrete syntax for inspection and import. Integers and identifiers
    are decimal; floating constants retain their raw IEEE bits. Strings are
    lists of byte values, avoiding escaping conventions between languages.
    The serializer itself is not a compiler-correctness theorem. *)
Definition number (n : Z) : string :=
  match n with
  | Z0 => "0"
  | Zpos p => DecimalString.NilZero.string_of_uint (Pos.to_uint p)
  | Zneg p => "-" ++ DecimalString.NilZero.string_of_uint (Pos.to_uint p)
  end.

Definition natural (n : nat) := number (Z.of_nat n).
Definition identifier (p : positive) := number (Zpos p).
Definition boolean (b : bool) := if b then "true" else "false".
Fixpoint fields (xs : list string) : string :=
  match xs with [] => "" | x :: xs => " " ++ x ++ fields xs end.
Definition node (name : string) (xs : list string) := "(" ++ name ++ fields xs ++ ")".
Definition items {A} (f : A -> string) (xs : list A) := node "list" (map f xs).
Definition optional {A} (f : A -> string) (x : option A) :=
  match x with None => "none" | Some a => node "some" [f a] end.
Fixpoint bytes (s : string) : list string :=
  match s with
  | EmptyString => []
  | String c s => natural (nat_of_ascii c) :: bytes s
  end.
Definition text (s : string) := node "text" (bytes s).

Definition typ (t : AST.typ) :=
  match t with
  | Tint => "Tint" | Tfloat => "Tfloat" | Tlong => "Tlong"
  | Tsingle => "Tsingle" | Tany32 => "Tany32" | Tany64 => "Tany64"
  end.
Definition xtype (t : AST.xtype) :=
  match t with
  | Xbool => "Xbool" | Xint8signed => "Xint8signed" | Xint8unsigned => "Xint8unsigned"
  | Xint16signed => "Xint16signed" | Xint16unsigned => "Xint16unsigned"
  | Xint => "Xint" | Xfloat => "Xfloat" | Xlong => "Xlong" | Xsingle => "Xsingle"
  | Xptr => "Xptr" | Xany32 => "Xany32" | Xany64 => "Xany64" | Xvoid => "Xvoid"
  end.
Definition chunk (c : memory_chunk) :=
  match c with
  | Mbool => "Mbool" | Mint8signed => "Mint8signed" | Mint8unsigned => "Mint8unsigned"
  | Mint16signed => "Mint16signed" | Mint16unsigned => "Mint16unsigned"
  | Mint32 => "Mint32" | Mint64 => "Mint64" | Mfloat32 => "Mfloat32"
  | Mfloat64 => "Mfloat64" | Many32 => "Many32" | Many64 => "Many64"
  end.
Definition callconv (c : calling_convention) :=
  node "callconv" [optional number (cc_vararg c);
    boolean (cc_unproto c); boolean (cc_structret c)].
Definition signature (s : AST.signature) :=
  node "signature" [items xtype (sig_args s); xtype (sig_res s); callconv (sig_cc s)].
Definition external (e : external_function) :=
  match e with
  | EF_external s g => node "EF_external" [text s; signature g]
  | EF_builtin s g => node "EF_builtin" [text s; signature g]
  | EF_runtime s g => node "EF_runtime" [text s; signature g]
  | EF_vload c => node "EF_vload" [chunk c]
  | EF_vstore c => node "EF_vstore" [chunk c]
  | EF_malloc => "EF_malloc"
  | EF_free => "EF_free"
  | EF_memcpy size align => node "EF_memcpy" [number size; number align]
  | EF_annot k s ts => node "EF_annot" [identifier k; text s; items typ ts]
  | EF_annot_val k s t => node "EF_annot_val" [identifier k; text s; typ t]
  | EF_inline_asm s g cs => node "EF_inline_asm" [text s; signature g; items text cs]
  | EF_debug k s ts => node "EF_debug" [identifier k; identifier s; items typ ts]
  end.
Definition int (n : Integers.int) := number (Int.unsigned n).
Definition long (n : int64) := number (Int64.unsigned n).
Definition offset (n : ptrofs) := number (Ptrofs.unsigned n).
Definition float (n : Floats.float) := long (Float.to_bits n).
Definition single (n : float32) := int (Float32.to_bits n).
Definition constant (c : Cminor.constant) :=
  match c with
  | Ointconst n => node "Ointconst" [int n]
  | Ofloatconst n => node "Ofloatconst" [float n]
  | Osingleconst n => node "Osingleconst" [single n]
  | Olongconst n => node "Olongconst" [long n]
  | Oaddrsymbol s o => node "Oaddrsymbol" [identifier s; offset o]
  | Oaddrstack o => node "Oaddrstack" [offset o]
  end.
Definition unary (u : unary_operation) :=
  match u with
  | Ocast8unsigned => "Ocast8unsigned" | Ocast8signed => "Ocast8signed"
  | Ocast16unsigned => "Ocast16unsigned" | Ocast16signed => "Ocast16signed"
  | Onegint => "Onegint" | Onotint => "Onotint"
  | Onegf => "Onegf" | Oabsf => "Oabsf" | Onegfs => "Onegfs" | Oabsfs => "Oabsfs"
  | Osingleoffloat => "Osingleoffloat" | Ofloatofsingle => "Ofloatofsingle"
  | Ointoffloat => "Ointoffloat" | Ointuoffloat => "Ointuoffloat"
  | Ofloatofint => "Ofloatofint" | Ofloatofintu => "Ofloatofintu"
  | Ointofsingle => "Ointofsingle" | Ointuofsingle => "Ointuofsingle"
  | Osingleofint => "Osingleofint" | Osingleofintu => "Osingleofintu"
  | Onegl => "Onegl" | Onotl => "Onotl" | Ointoflong => "Ointoflong"
  | Olongofint => "Olongofint" | Olongofintu => "Olongofintu"
  | Olongoffloat => "Olongoffloat" | Olonguoffloat => "Olonguoffloat"
  | Ofloatoflong => "Ofloatoflong" | Ofloatoflongu => "Ofloatoflongu"
  | Olongofsingle => "Olongofsingle" | Olonguofsingle => "Olonguofsingle"
  | Osingleoflong => "Osingleoflong" | Osingleoflongu => "Osingleoflongu"
  end.
Definition comparison (c : Integers.comparison) :=
  match c with
  | Ceq => "Ceq" | Cne => "Cne" | Clt => "Clt"
  | Cle => "Cle" | Cgt => "Cgt" | Cge => "Cge"
  end.
Definition binary (b : binary_operation) :=
  match b with
  | Oadd => "Oadd" | Osub => "Osub" | Omul => "Omul" | Odiv => "Odiv"
  | Odivu => "Odivu" | Omod => "Omod" | Omodu => "Omodu"
  | Oand => "Oand" | Oor => "Oor" | Oxor => "Oxor"
  | Oshl => "Oshl" | Oshr => "Oshr" | Oshru => "Oshru"
  | Oaddf => "Oaddf" | Osubf => "Osubf" | Omulf => "Omulf" | Odivf => "Odivf"
  | Oaddfs => "Oaddfs" | Osubfs => "Osubfs" | Omulfs => "Omulfs" | Odivfs => "Odivfs"
  | Oaddl => "Oaddl" | Osubl => "Osubl" | Omull => "Omull" | Odivl => "Odivl"
  | Odivlu => "Odivlu" | Omodl => "Omodl" | Omodlu => "Omodlu"
  | Oandl => "Oandl" | Oorl => "Oorl" | Oxorl => "Oxorl"
  | Oshll => "Oshll" | Oshrl => "Oshrl" | Oshrlu => "Oshrlu"
  | Ocmp c => node "Ocmp" [comparison c]
  | Ocmpu c => node "Ocmpu" [comparison c]
  | Ocmpf c => node "Ocmpf" [comparison c]
  | Ocmpfs c => node "Ocmpfs" [comparison c]
  | Ocmpl c => node "Ocmpl" [comparison c]
  | Ocmplu c => node "Ocmplu" [comparison c]
  end.
Fixpoint expression (e : expr) :=
  match e with
  | Evar v => node "Evar" [identifier v]
  | Econst c => node "Econst" [constant c]
  | Eunop u a => node "Eunop" [unary u; expression a]
  | Ebinop b a c => node "Ebinop" [binary b; expression a; expression c]
  | Eload c a => node "Eload" [chunk c; expression a]
  end.
Definition switchcase (c : Z * nat) := node "pair" [number (fst c); natural (snd c)].
Fixpoint statement (s : stmt) :=
  match s with
  | Sskip => "Sskip"
  | Sassign v e => node "Sassign" [identifier v; expression e]
  | Sstore c a e => node "Sstore" [chunk c; expression a; expression e]
  | Scall r g f xs =>
      node "Scall" [optional identifier r; signature g; expression f; items expression xs]
  | Stailcall g f xs => node "Stailcall" [signature g; expression f; items expression xs]
  | Sbuiltin r f xs => node "Sbuiltin" [optional identifier r; external f; items expression xs]
  | Sseq a b => node "Sseq" [statement a; statement b]
  | Sifthenelse c a b => node "Sifthenelse" [expression c; statement a; statement b]
  | Sloop b => node "Sloop" [statement b]
  | Sblock b => node "Sblock" [statement b]
  | Sexit n => node "Sexit" [natural n]
  | Sswitch b e cs d =>
      node "Sswitch" [boolean b; expression e; items switchcase cs; natural d]
  | Sreturn e => node "Sreturn" [optional expression e]
  | Slabel l b => node "Slabel" [identifier l; statement b]
  | Sgoto l => node "Sgoto" [identifier l]
  end.
Definition function (f : Cminor.function) :=
  node "function" [signature (fn_sig f); items identifier (fn_params f);
    items identifier (fn_vars f); number (fn_stackspace f); statement (fn_body f)].
Definition fundef (f : Cminor.fundef) :=
  match f with
  | Internal f => node "Internal" [function f]
  | External e => node "External" [external e]
  end.
Definition initializer (i : init_data) :=
  match i with
  | Init_int8 n => node "Init_int8" [int n]
  | Init_int16 n => node "Init_int16" [int n]
  | Init_int32 n => node "Init_int32" [int n]
  | Init_int64 n => node "Init_int64" [long n]
  | Init_float32 n => node "Init_float32" [single n]
  | Init_float64 n => node "Init_float64" [float n]
  | Init_space n => node "Init_space" [number n]
  | Init_addrof s o => node "Init_addrof" [identifier s; offset o]
  end.
Definition global (g : globdef Cminor.fundef unit) :=
  match g with
  | Gfun f => node "Gfun" [fundef f]
  | Gvar v => node "Gvar" [items initializer (gvar_init v);
      boolean (gvar_readonly v); boolean (gvar_volatile v)]
  end.
Definition definition (g : ident * globdef Cminor.fundef unit) :=
  node "pair" [identifier (fst g); global (snd g)].
Definition program (p : Cminor.program) :=
  node "program" [items definition (prog_defs p); items identifier (prog_public p);
    identifier (prog_main p)].
