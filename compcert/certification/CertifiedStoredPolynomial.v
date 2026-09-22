From Coq Require Import List Lia.
From compcert Require Import Errors Compiler Asm Cminor Smallstep Behaviors Integers.
From compcert Require Iteration Archi Compopts SelectOp Inlining RTLgen Selection Linearize Allocation.
From QuadratureC Require Import StoredPolynomialRules StoredPolynomialCompilation
  StoredPolynomialAccuracy.

(** This certificate is checked only against the explicit compiler configuration
    distributed with it. The standard compiler remains a separate target. *)
Local Transparent Archi.win64 SelectOp.symbol_is_relocatable
  Compopts.optim_for_size Compopts.propagate_float_constants
  Compopts.generate_float_constants Compopts.va_strict Compopts.optim_tailcalls
  Compopts.optim_constprop Compopts.optim_CSE Compopts.optim_redundancy
  Compopts.thumb Compopts.debug
  Inlining.inlining_info Inlining.inlining_analysis Inlining.should_inline
  RTLgen.more_likely Selection.compile_switch Selection.if_conversion_heuristic
  Linearize.enumerate_aux Allocation.regalloc Allocation.choose_allocation
  Allocation.allocation_candidates Compiler.print_Clight Compiler.print_Cminor
  Compiler.print_RTL Compiler.print_LTL Compiler.print_Mach
  Iteration.PrimIter.iterate Iteration.PrimIter.bounded_iter.

Section Order.
Variable n : nat.
Hypothesis hlo : (1 <= n)%nat.
Hypothesis hhi : (n <= 10)%nat.

Definition concrete_cminor : Cminor.program :=
  match (StoredPolynomialCompilation.second_translation n) with
  | OK p => p
  | Error _ => (StoredPolynomialCompilation.cminor_program n hlo hhi)
  end.

Definition backend_result : res Asm.program :=
  Compiler.transf_cminor_program concrete_cminor.

Theorem backend_succeeds : StoredPolynomialCompilation.succeeds backend_result = true.
Proof.
  unfold backend_result, concrete_cminor.
  positive_stored_cases n; vm_compute; reflexivity.
Qed.

Definition compiled_program : { p : Asm.program | backend_result = OK p }.
Proof.
  destruct backend_result as [p | msg] eqn:H.
  - exists p. reflexivity.
  - exfalso. pose proof backend_succeeds as HS. rewrite H in HS. discriminate.
Qed.
Definition assembly_program : Asm.program := proj1_sig compiled_program.

Local Opaque Compiler.transf_cminor_program
  Cshmgen.transl_program Cminorgen.transl_program.

Lemma concrete_cminor_eq : concrete_cminor = (StoredPolynomialCompilation.cminor_program n hlo hhi).
Proof.
  unfold concrete_cminor.
  rewrite (proj2_sig (StoredPolynomialCompilation.second_program n hlo hhi)). reflexivity.
Qed.

Theorem compiled :
  Compiler.transf_cminor_program (StoredPolynomialCompilation.cminor_program n hlo hhi) = OK assembly_program.
Proof.
  rewrite <- concrete_cminor_eq. exact (proj2_sig compiled_program).
Qed.

Theorem application_terminates :
  program_behaves (Asm.semantics assembly_program)
    (Terminates (StoredPolynomialRules.result_trace n) Int.zero).
Proof.
  exact (StoredPolynomialCompilation.assembly_terminates n hlo hhi assembly_program compiled).
Qed.

Theorem application_all_behaviors beh :
  program_behaves (Asm.semantics assembly_program) beh ->
  beh = Terminates (StoredPolynomialRules.result_trace n) Int.zero.
Proof.
  exact (StoredPolynomialCompilation.assembly_all_behaviors n hlo hhi assembly_program compiled beh).
Qed.

Theorem application_accuracy beh :
  program_behaves (Asm.semantics assembly_program) beh -> accurate_behavior n beh.
Proof.
  exact (StoredPolynomialCompilation.assembly_application_accuracy
    n hlo hhi assembly_program compiled beh).
Qed.

End Order.
