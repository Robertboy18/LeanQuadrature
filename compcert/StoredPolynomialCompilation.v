From Coq Require Import List ZArith Lia.
From compcert Require Import Errors Integers Values Events Globalenvs Smallstep Behaviors
  Ctypes Clight Csharpminor Cshmgen Cshmgenproof Cminor Cminorgen Cminorgenproof
  Compiler Asm.
From QuadratureC Require Import StoredPolynomialRules AnnotatedBehavior
  CminorApplication CompilerBackend StoredPolynomialAccuracy.

Import ListNotations.
Module App := StoredPolynomialRules.

Section Order.
Variable n : nat.
Hypothesis hlo : (1 <= n)%nat.
Hypothesis hhi : (n <= 10)%nat.

Definition first_translation := Cshmgen.transl_program (App.application n).
Definition second_translation : res Cminor.program :=
  match first_translation with
  | OK p => Cminorgen.transl_program p
  | Error msg => Error msg
  end.

Definition succeeds {A : Type} (n : res A) : bool :=
  match n with OK _ => true | Error _ => false end.

Lemma first_translation_succeeds : succeeds first_translation = true.
Proof.
  unfold first_translation.
  positive_stored_cases n; vm_compute; reflexivity.
Qed.

Lemma second_translation_succeeds : succeeds second_translation = true.
Proof.
  unfold second_translation, first_translation.
  positive_stored_cases n; vm_compute; reflexivity.
Qed.

Definition first_program : { p : Csharpminor.program | first_translation = OK p }.
Proof.
  destruct first_translation as [p | msg] eqn:H.
  - exists p. reflexivity.
  - exfalso. pose proof first_translation_succeeds as HS. rewrite H in HS. discriminate.
Qed.

Definition second_program : { p : Cminor.program | second_translation = OK p }.
Proof.
  destruct second_translation as [p | msg] eqn:H.
  - exists p. reflexivity.
  - exfalso. pose proof second_translation_succeeds as HS. rewrite H in HS. discriminate.
Qed.

Definition csharpminor_program := proj1_sig first_program.
Definition cminor_program := proj1_sig second_program.

(** Keep the already checked compiler computations folded while identifying
    their witnesses; reducing the whole translated polynomial is unnecessary. *)
Local Opaque Cshmgen.transl_program Cminorgen.transl_program.

Theorem first_program_translation :
  Cshmgen.transl_program (App.application n) = OK csharpminor_program.
Proof. exact (proj2_sig first_program). Qed.

Theorem second_program_translation :
  Cminorgen.transl_program csharpminor_program = OK cminor_program.
Proof.
  pose proof (proj2_sig second_program) as H.
  change (second_translation = OK cminor_program) in H.
  unfold second_translation, first_translation in H.
  rewrite first_program_translation in H. exact H.
Qed.

Theorem application_forward_simulation :
  forward_simulation (Clight.semantics2 (App.application n)) (Cminor.semantics cminor_program).
Proof.
  eapply compose_forward_simulations.
  - apply Cshmgenproof.transl_program_correct.
    apply Cshmgenproof.transf_program_match, first_program_translation.
  - apply Cminorgenproof.transl_program_correct.
    apply Cminorgenproof.transf_program_match, second_program_translation.
Qed.

Theorem application_terminates :
  program_behaves (Cminor.semantics cminor_program) (Terminates (App.result_trace n) Int.zero).
Proof.
  eapply forward_simulation_termination.
  - exact application_forward_simulation.
  - exact (App.main_initial_state n).
  - exact (App.main_steps n hhi).
  - constructor.
Qed.

Theorem application_all_behaviors beh :
  program_behaves (Cminor.semantics cminor_program) beh ->
  beh = Terminates (App.result_trace n) Int.zero.
Proof.
  eapply annotation_terminating_behavior_unique.
  - apply Cminor.semantics_determinate.
  - repeat constructor.
  - exact application_terminates.
Qed.

Theorem cminor_application_accuracy beh :
  program_behaves (Cminor.semantics cminor_program) beh ->
  accurate_behavior n beh.
Proof.
  intro H. rewrite (application_all_behaviors beh H).
  exact (result_behavior_accurate n hlo hhi).
Qed.

Section SuccessfulCompilation.
Variable assembly_program : Asm.program.
Hypothesis compiled :
  Compiler.transf_cminor_program cminor_program = OK assembly_program.

Theorem assembly_forward_simulation :
  forward_simulation (Clight.semantics2 (App.application n))
    (Asm.semantics assembly_program).
Proof.
  eapply compose_forward_simulations.
  - exact application_forward_simulation.
  - apply successful_cminor_compilation_forward. exact compiled.
Qed.

Theorem assembly_terminates :
  program_behaves (Asm.semantics assembly_program)
    (Terminates (App.result_trace n) Int.zero).
Proof.
  eapply forward_simulation_termination.
  - exact assembly_forward_simulation.
  - exact (App.main_initial_state n).
  - exact (App.main_steps n hhi).
  - constructor.
Qed.

Theorem assembly_all_behaviors beh :
  program_behaves (Asm.semantics assembly_program) beh ->
  beh = Terminates (App.result_trace n) Int.zero.
Proof.
  eapply annotation_terminating_behavior_unique.
  - apply Asm.semantics_determinate.
  - repeat constructor.
  - exact assembly_terminates.
Qed.

(** The polynomial application has no external cosine premise. Only successful
    backend compilation is required to transfer its integral accuracy to Asm. *)
Theorem assembly_application_accuracy beh :
  program_behaves (Asm.semantics assembly_program) beh ->
  accurate_behavior n beh.
Proof.
  intro H. rewrite (assembly_all_behaviors beh H).
  exact (result_behavior_accurate n hlo hhi).
Qed.

End SuccessfulCompilation.
End Order.
