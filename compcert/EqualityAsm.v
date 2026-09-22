From Coq Require Import List Arith Bool ZArith.
From compcert Require Import Coqlib AST Maps Integers Floats Asm.
From CminorImport Require Import EqualityCminorSel.

(** Exact syntax equality includes every assembly constructor and constant bit. *)
Definition asm_addrmode_eq (a b : Asm.addrmode) : {a = b} + {a <> b}.
Proof.
  generalize ireg_eq ident_eq zeq Ptrofs.eq_dec; intros.
  decide equality; decide equality; decide equality.
Defined.

Definition asm_testcond_eq (a b : Asm.testcond) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition asm_instruction_eq (a b : Asm.instruction) : {a = b} + {a <> b}.
Proof.
  generalize ireg_eq freg_eq asm_addrmode_eq asm_testcond_eq ident_eq zeq
    Int.eq_dec Int64.eq_dec Float.eq_dec Float32.eq_dec Ptrofs.eq_dec
    signature_eq external_function_eq (@eq_builtin_arg preg preg_eq)
    (@eq_builtin_res preg preg_eq) list_eq_dec; intros.
  decide equality; decide equality.
Defined.

Definition asm_code_eq (a b : Asm.code) : {a = b} + {a <> b} :=
  list_eq_dec asm_instruction_eq a b.

Definition asm_function_eq (a b : Asm.function) : {a = b} + {a <> b}.
Proof. generalize asm_code_eq signature_eq; intros. decide equality. Defined.

Definition asm_fundef_eq (a b : Asm.fundef) : {a = b} + {a <> b}.
Proof. generalize asm_function_eq external_function_eq; intros. decide equality. Defined.

Definition asm_globdef_eq (a b : globdef Asm.fundef unit) : {a = b} + {a <> b}.
Proof. generalize asm_fundef_eq cs_globvar_eq; intros. decide equality. Defined.

Definition asm_definition_eq (a b : ident * globdef Asm.fundef unit) : {a = b} + {a <> b}.
Proof. generalize ident_eq asm_globdef_eq; intros. decide equality. Defined.

Definition asm_program_eq (a b : Asm.program) : {a = b} + {a <> b}.
Proof. generalize asm_definition_eq ident_eq list_eq_dec; intros. decide equality. Defined.

Definition asm_program_eqb (a b : Asm.program) : bool :=
  if asm_program_eq a b then true else false.

Lemma asm_program_eqb_sound a b : asm_program_eqb a b = true -> a = b.
Proof. unfold asm_program_eqb. destruct (asm_program_eq a b); congruence. Qed.

Print Assumptions asm_program_eqb_sound.
