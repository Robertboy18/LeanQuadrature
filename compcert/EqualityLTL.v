From Coq Require Import List Arith Bool ZArith.
From compcert Require Import Coqlib AST Maps Integers Floats Op LTL Locations.
From CminorImport Require Import EqualityCminorSel.

(** Exact equality includes the canonical CFG tree, not just its printed list.
    CompCert's numeric equality procedures account for representation proofs. *)
Definition ltl_instruction_eq (a b : instruction) : {a = b} + {a <> b}.
Proof.
  generalize ident_eq eq_operation chunk_eq eq_addressing signature_eq eq_condition
    mreg_eq slot_eq typ_eq zeq external_function_eq (@eq_builtin_arg loc Loc.eq)
    (@eq_builtin_res mreg mreg_eq) list_eq_dec; intros.
  decide equality; decide equality.
Defined.

Scheme tree'_rect := Induction for PTree.tree' Sort Type.
Scheme tree_rect := Induction for PTree.tree Sort Type.
Scheme tree'_rec := Induction for PTree.tree' Sort Set.
Scheme tree_rec := Induction for PTree.tree Sort Set.

Definition ltl_code_eq (a b : code) : {a = b} + {a <> b}.
Proof.
  assert (eq_nonempty : forall a b : PTree.tree' bblock, {a = b} + {a <> b}).
  { decide equality; apply list_eq_dec; apply ltl_instruction_eq. }
  decide equality.
Defined.

Definition ltl_function_eq (a b : function) : {a = b} + {a <> b}.
Proof.
  generalize ltl_code_eq signature_eq ident_eq list_eq_dec zeq; intros. decide equality.
Defined.

Definition ltl_fundef_eq (a b : fundef) : {a = b} + {a <> b}.
Proof. generalize ltl_function_eq external_function_eq; intros. decide equality. Defined.

Definition ltl_globdef_eq (a b : globdef fundef unit) : {a = b} + {a <> b}.
Proof. generalize ltl_fundef_eq cs_globvar_eq; intros. decide equality. Defined.

Definition ltl_definition_eq (a b : ident * globdef fundef unit) : {a = b} + {a <> b}.
Proof. generalize ident_eq ltl_globdef_eq; intros. decide equality. Defined.

Definition ltl_program_eq (a b : program) : {a = b} + {a <> b}.
Proof. generalize ltl_definition_eq ident_eq list_eq_dec; intros. decide equality. Defined.

Definition ltl_program_eqb (a b : program) : bool :=
  if ltl_program_eq a b then true else false.

Lemma ltl_program_eqb_sound a b : ltl_program_eqb a b = true -> a = b.
Proof. unfold ltl_program_eqb. destruct (ltl_program_eq a b); congruence. Qed.

Print Assumptions ltl_program_eqb_sound.
