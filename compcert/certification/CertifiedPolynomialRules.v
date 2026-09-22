From Coq Require Import List.
From compcert Require Import Errors Compiler Asm Cminor Smallstep Behaviors Integers.
From compcert Require Iteration Archi Compopts SelectOp Inlining RTLgen Selection Linearize Allocation.
From QuadratureC Require Import ClightRules PolynomialRules PolynomialRulesCompilation
  PolynomialRulesAccuracy.

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
Variable r : rule_order.

Definition concrete_cminor : Cminor.program :=
  match (PolynomialRulesCompilation.second_translation r) with
  | OK p => p
  | Error _ => (PolynomialRulesCompilation.cminor_program r)
  end.

Definition backend_result : res Asm.program :=
  Compiler.transf_cminor_program concrete_cminor.

Theorem backend_succeeds : PolynomialRulesCompilation.succeeds backend_result = true.
Proof.
  unfold backend_result, concrete_cminor.
  destruct r; vm_compute; reflexivity.
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

Lemma concrete_cminor_eq : concrete_cminor = (PolynomialRulesCompilation.cminor_program r).
Proof.
  unfold concrete_cminor.
  rewrite (proj2_sig (PolynomialRulesCompilation.second_program r)). reflexivity.
Qed.

Theorem compiled :
  Compiler.transf_cminor_program (PolynomialRulesCompilation.cminor_program r) = OK assembly_program.
Proof.
  rewrite <- concrete_cminor_eq. exact (proj2_sig compiled_program).
Qed.

Theorem application_terminates :
  program_behaves (Asm.semantics assembly_program)
    (Terminates (PolynomialRules.result_trace r) Int.zero).
Proof.
  exact (PolynomialRulesCompilation.assembly_terminates r assembly_program compiled).
Qed.

Theorem application_all_behaviors beh :
  program_behaves (Asm.semantics assembly_program) beh ->
  beh = Terminates (PolynomialRules.result_trace r) Int.zero.
Proof.
  exact (PolynomialRulesCompilation.assembly_all_behaviors r assembly_program compiled beh).
Qed.

Theorem application_accuracy beh :
  program_behaves (Asm.semantics assembly_program) beh -> accurate_behavior r beh.
Proof.
  exact (PolynomialRulesCompilation.assembly_application_accuracy
    r assembly_program compiled beh).
Qed.

End Order.
