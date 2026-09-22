From Coq Require Import String ZArith.
From compcert Require Import Errors Compiler Linear Mach Asm.
From CminorImport Require Import LinearBeforeStacking.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** The actual pipeline after concrete stack-frame layout. *)
Definition after_mach (p : res Mach.program) : res Asm.program :=
   p
   @@ print print_Mach
  @@@ time "Asm generation" Asmgen.transf_program.

Theorem stacking_split p :
  after_linear (OK p) = after_mach (Stacking.transf_program p).
Proof. reflexivity. Qed.

Print Assumptions stacking_split.
