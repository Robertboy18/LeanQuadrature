From Coq Require Import List Arith Bool.
From compcert Require Import Coqlib AST Integers Floats Op CminorSel.

(** Exact equality of instruction-selected syntax. Integer and floating-point
    equality use CompCert's decision procedures, which account for the validity
    proofs carried by their representations. This checks syntax, not execution. *)

Fixpoint cs_expr_eq (a b : expr) {struct a} : {a = b} + {a <> b}
with cs_exprlist_eq (a b : exprlist) {struct a} : {a = b} + {a <> b}
with cs_condexpr_eq (a b : condexpr) {struct a} : {a = b} + {a <> b}.
Proof.
- generalize ident_eq eq_operation chunk_eq eq_addressing Nat.eq_dec
    external_function_eq signature_eq; intros. decide equality.
- decide equality.
- generalize eq_condition; intros. decide equality.
Defined.

Definition cs_exitexpr_eq (a b : exitexpr) : {a = b} + {a <> b}.
Proof.
  generalize cs_expr_eq cs_condexpr_eq Nat.eq_dec list_eq_dec; intros. decide equality.
Defined.

Definition cs_stmt_eq (a b : stmt) : {a = b} + {a <> b}.
Proof.
  generalize ident_eq cs_expr_eq cs_exprlist_eq cs_condexpr_eq cs_exitexpr_eq
    chunk_eq eq_addressing external_function_eq signature_eq Nat.eq_dec
    (@eq_builtin_arg expr cs_expr_eq) (@eq_builtin_res ident ident_eq) list_eq_dec;
    intros. decide equality; decide equality.
Defined.

Definition cs_function_eq (a b : function) : {a = b} + {a <> b}.
Proof.
  generalize cs_stmt_eq signature_eq ident_eq list_eq_dec zeq; intros. decide equality.
Defined.

Definition cs_fundef_eq (a b : fundef) : {a = b} + {a <> b}.
Proof.
  generalize cs_function_eq external_function_eq; intros. decide equality.
Defined.

Definition cs_init_data_eq (a b : init_data) : {a = b} + {a <> b}.
Proof.
  generalize Int.eq_dec Int64.eq_dec Float.eq_dec Float32.eq_dec Ptrofs.eq_dec ident_eq zeq;
    intros. decide equality.
Defined.

Definition cs_globvar_eq (a b : globvar unit) : {a = b} + {a <> b}.
Proof.
  generalize cs_init_data_eq list_eq_dec bool_dec; intros.
  decide equality; decide equality.
Defined.

Definition cs_globdef_eq (a b : globdef fundef unit) : {a = b} + {a <> b}.
Proof. generalize cs_fundef_eq cs_globvar_eq; intros. decide equality. Defined.

Definition cs_definition_eq (a b : ident * globdef fundef unit) : {a = b} + {a <> b}.
Proof. generalize ident_eq cs_globdef_eq; intros. decide equality. Defined.

Definition cs_program_eq (a b : program) : {a = b} + {a <> b}.
Proof. generalize cs_definition_eq ident_eq list_eq_dec; intros. decide equality. Defined.

Definition cs_program_eqb (a b : program) : bool :=
  if cs_program_eq a b then true else false.

Lemma cs_program_eqb_sound a b : cs_program_eqb a b = true -> a = b.
Proof. unfold cs_program_eqb. destruct (cs_program_eq a b); congruence. Qed.

Print Assumptions cs_program_eqb_sound.
