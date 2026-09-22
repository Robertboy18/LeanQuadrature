From Coq Require Import String ZArith.
From compcert Require Import Errors Compiler RTL Asm.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(** The exact prefix of Compiler.transf_rtl_program ending immediately before
    register allocation. Flags and passes are those of the configured compiler;
    this definition does not select a different optimization policy. *)
Definition preallocation (p : RTL.program) : res RTL.program :=
   OK p
   @@ print (print_RTL 0)
   @@ total_if Compopts.optim_tailcalls (time "Tail calls" Tailcall.transf_program)
   @@ print (print_RTL 1)
  @@@ time "Inlining" Inlining.transf_program
   @@ print (print_RTL 2)
   @@ time "Renumbering" Renumber.transf_program
   @@ print (print_RTL 3)
   @@ total_if Compopts.optim_constprop (time "Constant propagation" Constprop.transf_program)
   @@ print (print_RTL 4)
   @@ total_if Compopts.optim_constprop (time "Renumbering" Renumber.transf_program)
   @@ print (print_RTL 5)
  @@@ partial_if Compopts.optim_CSE (time "CSE" CSE.transf_program)
   @@ print (print_RTL 6)
  @@@ partial_if Compopts.optim_redundancy (time "Redundancy elimination" Deadcode.transf_program)
   @@ print (print_RTL 7)
  @@@ time "Unused globals" Unusedglob.transform_program
   @@ print (print_RTL 8).

(** The remaining compiler suffix, including register allocation. *)
Definition allocate_and_finish (p : res RTL.program) : res Asm.program :=
   p
  @@@ time "Register allocation" Allocation.transf_program
   @@ print print_LTL
   @@ time "Branch tunneling" Tunneling.tunnel_program
  @@@ time "CFG linearization" Linearize.transf_program
   @@ time "Label cleanup" CleanupLabels.transf_program
  @@@ partial_if Compopts.debug (time "Debugging info for local variables" Debugvar.transf_program)
  @@@ time "Mach generation" Stacking.transf_program
   @@ print print_Mach
  @@@ time "Asm generation" Asmgen.transf_program.

(** Definitional equality checks that the boundary splits the actual pipeline. *)
Theorem compiler_split p :
  Compiler.transf_rtl_program p = allocate_and_finish (preallocation p).
Proof. reflexivity. Qed.

Theorem compiler_from_preallocation p q :
  preallocation p = OK q ->
  Compiler.transf_rtl_program p = allocate_and_finish (OK q).
Proof. intro H. rewrite compiler_split, H. reflexivity. Qed.

Print Assumptions compiler_split.
Print Assumptions compiler_from_preallocation.
