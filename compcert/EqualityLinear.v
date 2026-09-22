From Coq Require Import List Arith Bool ZArith.
From compcert Require Import Coqlib AST Maps Integers Floats Op Locations Linear.
From CminorImport Require Import EqualityCminorSel.

(** Equality of the complete instruction lists, labels, constants, and globals. *)
Definition linear_instruction_eq (a b : Linear.instruction) : {a = b} + {a <> b}.
Proof.
  generalize ident_eq eq_operation chunk_eq eq_addressing signature_eq eq_condition
    mreg_eq slot_eq typ_eq zeq external_function_eq (@eq_builtin_arg loc Loc.eq)
    (@eq_builtin_res mreg mreg_eq) list_eq_dec; intros.
  decide equality; decide equality.
Defined.

Definition linear_code_eq (a b : Linear.code) : {a = b} + {a <> b} :=
  list_eq_dec linear_instruction_eq a b.

Definition linear_function_eq (a b : Linear.function) : {a = b} + {a <> b}.
Proof.
  generalize linear_code_eq signature_eq zeq; intros. decide equality.
Defined.

Definition linear_fundef_eq (a b : Linear.fundef) : {a = b} + {a <> b}.
Proof. generalize linear_function_eq external_function_eq; intros. decide equality. Defined.

Definition linear_globdef_eq (a b : globdef Linear.fundef unit) : {a = b} + {a <> b}.
Proof. generalize linear_fundef_eq cs_globvar_eq; intros. decide equality. Defined.

Definition linear_definition_eq (a b : ident * globdef Linear.fundef unit) : {a = b} + {a <> b}.
Proof. generalize ident_eq linear_globdef_eq; intros. decide equality. Defined.

Definition linear_program_eq (a b : Linear.program) : {a = b} + {a <> b}.
Proof. generalize linear_definition_eq ident_eq list_eq_dec; intros. decide equality. Defined.

Definition linear_program_eqb (a b : Linear.program) : bool :=
  if linear_program_eq a b then true else false.

Lemma linear_program_eqb_sound a b : linear_program_eqb a b = true -> a = b.
Proof. unfold linear_program_eqb. destruct (linear_program_eq a b); congruence. Qed.

Print Assumptions linear_program_eqb_sound.
