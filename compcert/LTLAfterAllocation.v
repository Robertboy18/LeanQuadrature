From Coq Require Import String ZArith.
From compcert Require Import Errors Compiler RTL LTL Asm.
From CminorImport Require Import RTLPreallocation.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** The compiler suffix after register allocation. *)
Definition after_allocation (p : res LTL.program) : res Asm.program :=
   p
   @@ print print_LTL
   @@ time "Branch tunneling" Tunneling.tunnel_program
  @@@ time "CFG linearization" Linearize.transf_program
   @@ time "Label cleanup" CleanupLabels.transf_program
  @@@ partial_if Compopts.debug (time "Debugging info for local variables" Debugvar.transf_program)
  @@@ time "Mach generation" Stacking.transf_program
   @@ print print_Mach
  @@@ time "Asm generation" Asmgen.transf_program.

Theorem allocation_split p :
  allocate_and_finish (OK p) = after_allocation (Allocation.transf_program p).
Proof. reflexivity. Qed.

Print Assumptions allocation_split.
