From Coq Require Import List Arith Bool ZArith.
From compcert Require Import Coqlib AST Maps Integers Floats Op Locations Mach.
From CminorImport Require Import EqualityCminorSel.

(** Equality includes byte offsets, frame metadata, complete code, and globals. *)
Definition mach_instruction_eq (a b : Mach.instruction) : {a = b} + {a <> b}.
Proof.
  generalize ident_eq eq_operation chunk_eq eq_addressing signature_eq eq_condition
    mreg_eq typ_eq Ptrofs.eq_dec external_function_eq (@eq_builtin_arg mreg mreg_eq)
    (@eq_builtin_res mreg mreg_eq) list_eq_dec; intros.
  decide equality; decide equality.
Defined.

Definition mach_code_eq (a b : Mach.code) : {a = b} + {a <> b} :=
  list_eq_dec mach_instruction_eq a b.

Definition mach_function_eq (a b : Mach.function) : {a = b} + {a <> b}.
Proof.
  generalize mach_code_eq signature_eq zeq Ptrofs.eq_dec; intros. decide equality.
Defined.

Definition mach_fundef_eq (a b : Mach.fundef) : {a = b} + {a <> b}.
Proof. generalize mach_function_eq external_function_eq; intros. decide equality. Defined.

Definition mach_globdef_eq (a b : globdef Mach.fundef unit) : {a = b} + {a <> b}.
Proof. generalize mach_fundef_eq cs_globvar_eq; intros. decide equality. Defined.

Definition mach_definition_eq (a b : ident * globdef Mach.fundef unit) : {a = b} + {a <> b}.
Proof. generalize ident_eq mach_globdef_eq; intros. decide equality. Defined.

Definition mach_program_eq (a b : Mach.program) : {a = b} + {a <> b}.
Proof. generalize mach_definition_eq ident_eq list_eq_dec; intros. decide equality. Defined.

Definition mach_program_eqb (a b : Mach.program) : bool :=
  if mach_program_eq a b then true else false.

Lemma mach_program_eqb_sound a b : mach_program_eqb a b = true -> a = b.
Proof. unfold mach_program_eqb. destruct (mach_program_eq a b); congruence. Qed.

Print Assumptions mach_program_eqb_sound.
