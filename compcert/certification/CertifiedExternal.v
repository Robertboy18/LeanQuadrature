From Coq Require Import List.
From compcert Require Import Errors Compiler Asm Cminor Smallstep Behaviors Integers
  Values Events Globalenvs Clight.
From compcert Require Iteration Archi Compopts SelectOp Inlining RTLgen Selection Linearize Allocation.
From QuadratureC Require Import ClightExample ClightApplication CminorApplication
  AsmApplication ApplicationAccuracy.

Import ListNotations.
Module App := ClightApplication.

(** This configuration also compiles the application retaining external cosine.
    Its numerical and behavioral contracts remain explicit below. *)
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

Definition concrete_cminor : Cminor.program :=
  match CminorApplication.second_translation with
  | OK p => p
  | Error _ => CminorApplication.cminor_program
  end.

Definition backend_result : res Asm.program :=
  Compiler.transf_cminor_program concrete_cminor.

Theorem backend_succeeds : CminorApplication.succeeds backend_result = true.
Proof. vm_compute. reflexivity. Qed.

Definition compiled_program : { p : Asm.program | backend_result = OK p }.
Proof.
  destruct backend_result as [p | msg] eqn:H.
  - exists p. reflexivity.
  - exfalso. pose proof backend_succeeds as HS. rewrite H in HS. discriminate.
Qed.
Definition assembly_program : Asm.program := proj1_sig compiled_program.

Local Opaque Compiler.transf_cminor_program
  Cshmgen.transl_program Cminorgen.transl_program.

Lemma concrete_cminor_eq : concrete_cminor = CminorApplication.cminor_program.
Proof.
  unfold concrete_cminor.
  rewrite (proj2_sig CminorApplication.second_program). reflexivity.
Qed.

Theorem compiled :
  Compiler.transf_cminor_program CminorApplication.cminor_program = OK assembly_program.
Proof.
  rewrite <- concrete_cminor_eq. exact (proj2_sig compiled_program).
Qed.

Section ExternalCosine.
Hypothesis cosine_left : external_call cosine_external App.ge [Vfloat left_node]
  App.initial_memory E0 (Vfloat cosine_value) App.initial_memory.
Hypothesis cosine_right : external_call cosine_external App.ge [Vfloat right_node]
  App.initial_memory E0 (Vfloat cosine_value) App.initial_memory.

Theorem application_terminates :
  program_behaves (Asm.semantics assembly_program)
    (Terminates App.result_trace Int.zero).
Proof.
  exact (AsmApplication.application_terminates assembly_program compiled
    cosine_left cosine_right).
Qed.

Theorem application_all_behaviors beh :
  program_behaves (Asm.semantics assembly_program) beh ->
  beh = Terminates App.result_trace Int.zero.
Proof.
  exact (AsmApplication.application_all_behaviors assembly_program compiled
    cosine_left cosine_right beh).
Qed.

Theorem application_accuracy beh :
  program_behaves (Asm.semantics assembly_program) beh -> accurate_behavior beh.
Proof.
  exact (ApplicationAccuracy.assembly_application_accuracy cosine_left cosine_right
    assembly_program compiled beh).
Qed.

End ExternalCosine.

Print Assumptions backend_succeeds.
Print Assumptions compiled.
Print Assumptions application_terminates.
Print Assumptions application_all_behaviors.
Print Assumptions application_accuracy.
