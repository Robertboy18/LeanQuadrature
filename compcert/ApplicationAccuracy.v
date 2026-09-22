From Coq Require Import List Reals String.
From Flocq Require Import IEEE754.Binary.
From compcert Require Import Errors Integers Floats Values Events Globalenvs Behaviors
  Clight Cminor Compiler Asm.
From QuadratureC Require Import ClightExample ClightApplication CminorApplication
  AsmApplication ValueAccuracy ExampleIntegral.

Import ListNotations.
Local Open Scope R_scope.
Local Open Scope string_scope.
Module App := ClightApplication.

(** This specification includes termination, finiteness, the corrected error
    bound, and the failure of the draft's proposed bound. Its real target is
    the Riemann integral, proved within the same kernel as the execution. *)
Definition accurate_behavior (beh : program_behavior) : Prop :=
  exists result : float,
    beh = Terminates
      [Event_annot "quadrature-result" [EVfloat result]] Int.zero /\
    Binary.is_finite 53 1024 result = true /\
    Rabs (B2R 53 1024 result - RiemannInt integrand_integrable) <= 356 / 100000 /\
    ~ Rabs (B2R 53 1024 result - RiemannInt integrand_integrable) <= 224 / 100000.

Lemma result_behavior_accurate :
  accurate_behavior (Terminates App.result_trace Int.zero).
Proof.
  exists cosine_value. split.
  - reflexivity.
  - split.
    + vm_compute. reflexivity.
    + rewrite integral_value. split.
      * exact cosine_value_accuracy.
      * exact cosine_value_draft_bound_false.
Qed.

Section ExternalCosine.
Hypothesis cosine_left : external_call cosine_external App.ge [Vfloat left_node]
  App.initial_memory E0 (Vfloat cosine_value) App.initial_memory.
Hypothesis cosine_right : external_call cosine_external App.ge [Vfloat right_node]
  App.initial_memory E0 (Vfloat cosine_value) App.initial_memory.

Theorem source_application_accuracy beh :
  program_behaves (Clight.semantics2 App.application) beh ->
  accurate_behavior beh.
Proof.
  intro H.
  rewrite (App.application_all_behaviors cosine_left cosine_right beh H).
  exact result_behavior_accurate.
Qed.

Theorem cminor_application_accuracy beh :
  program_behaves (Cminor.semantics CminorApplication.cminor_program) beh ->
  accurate_behavior beh.
Proof.
  intro H.
  rewrite (CminorApplication.application_all_behaviors
    cosine_left cosine_right beh H).
  exact result_behavior_accurate.
Qed.

Theorem assembly_application_accuracy (assembly_program : Asm.program)
    (compiled : Compiler.transf_cminor_program CminorApplication.cminor_program =
      OK assembly_program) beh :
  program_behaves (Asm.semantics assembly_program) beh ->
  accurate_behavior beh.
Proof.
  intro H.
  rewrite (AsmApplication.application_all_behaviors assembly_program compiled
    cosine_left cosine_right beh H).
  exact result_behavior_accurate.
Qed.

End ExternalCosine.

Print Assumptions result_behavior_accurate.
Print Assumptions source_application_accuracy.
Print Assumptions cminor_application_accuracy.
Print Assumptions assembly_application_accuracy.
