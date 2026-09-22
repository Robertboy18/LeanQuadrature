From Coq Require Import String ZArith.
From compcert Require Import Errors Compiler LTL Linear Asm.
From CminorImport Require Import LTLAfterAllocation.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** The actual pipeline between allocation and stack-frame layout. *)
Definition linear_prefix (p : LTL.program) : res Linear.program :=
   OK p
   @@ print print_LTL
   @@ time "Branch tunneling" Tunneling.tunnel_program
  @@@ time "CFG linearization" Linearize.transf_program
   @@ time "Label cleanup" CleanupLabels.transf_program
  @@@ partial_if Compopts.debug (time "Debugging info for local variables" Debugvar.transf_program).

Definition after_linear (p : res Linear.program) : res Asm.program :=
   p
  @@@ time "Mach generation" Stacking.transf_program
   @@ print print_Mach
  @@@ time "Asm generation" Asmgen.transf_program.

Theorem linear_split p :
  after_allocation (OK p) = after_linear (linear_prefix p).
Proof. reflexivity. Qed.

Print Assumptions linear_split.
