From Coq Require Import List Arith Bool ZArith.
From compcert Require Import Coqlib AST Maps Integers Floats Op RTL.
From CminorImport Require Import EqualityCminorSel.

(** Exact equality includes the canonical CFG tree, not just its printed list.
    CompCert's numeric equality procedures account for representation proofs. *)
Definition rtl_instruction_eq (a b : instruction) : {a = b} + {a <> b}.
Proof.
  generalize ident_eq eq_operation chunk_eq eq_addressing signature_eq eq_condition
    external_function_eq (@eq_builtin_arg positive ident_eq)
    (@eq_builtin_res positive ident_eq) list_eq_dec; intros.
  decide equality; decide equality.
Defined.

Scheme tree'_rect := Induction for PTree.tree' Sort Type.
Scheme tree_rect := Induction for PTree.tree Sort Type.

Definition rtl_code_eq (a b : code) : {a = b} + {a <> b}.
Proof.
  assert (eq_nonempty : forall a b : PTree.tree' instruction, {a = b} + {a <> b}).
  { decide equality; apply rtl_instruction_eq. }
  decide equality.
Defined.

Definition rtl_function_eq (a b : function) : {a = b} + {a <> b}.
Proof.
  generalize rtl_code_eq signature_eq ident_eq list_eq_dec zeq; intros. decide equality.
Defined.

Definition rtl_fundef_eq (a b : fundef) : {a = b} + {a <> b}.
Proof. generalize rtl_function_eq external_function_eq; intros. decide equality. Defined.

Definition rtl_globdef_eq (a b : globdef fundef unit) : {a = b} + {a <> b}.
Proof. generalize rtl_fundef_eq cs_globvar_eq; intros. decide equality. Defined.

Definition rtl_definition_eq (a b : ident * globdef fundef unit) : {a = b} + {a <> b}.
Proof. generalize ident_eq rtl_globdef_eq; intros. decide equality. Defined.

Definition rtl_program_eq (a b : program) : {a = b} + {a <> b}.
Proof. generalize rtl_definition_eq ident_eq list_eq_dec; intros. decide equality. Defined.

Definition rtl_program_eqb (a b : program) : bool :=
  if rtl_program_eq a b then true else false.

Lemma rtl_program_eqb_sound a b : rtl_program_eqb a b = true -> a = b.
Proof. unfold rtl_program_eqb. destruct (rtl_program_eq a b); congruence. Qed.

Print Assumptions rtl_program_eqb_sound.
