From Coq Require Import List ZArith.
From compcert Require Import Errors Integers Values Events Globalenvs Smallstep Behaviors
  Ctypes Clight Csharpminor Cshmgen Cshmgenproof Cminor Cminorgen Cminorgenproof.
From QuadratureC Require Import ClightExample ClightApplication AnnotatedBehavior.

Import ListNotations.
Module App := ClightApplication.

Definition first_translation := Cshmgen.transl_program App.application.
Definition second_translation : res Cminor.program :=
  match first_translation with
  | OK p => Cminorgen.transl_program p
  | Error msg => Error msg
  end.

Definition succeeds {A : Type} (r : res A) : bool :=
  match r with OK _ => true | Error _ => false end.

Lemma first_translation_succeeds : succeeds first_translation = true.
Proof. vm_compute. reflexivity. Qed.

Lemma second_translation_succeeds : succeeds second_translation = true.
Proof. vm_compute. reflexivity. Qed.

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

Theorem first_program_translation :
  Cshmgen.transl_program App.application = OK csharpminor_program.
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
  forward_simulation (Clight.semantics2 App.application) (Cminor.semantics cminor_program).
Proof.
  eapply compose_forward_simulations.
  - apply Cshmgenproof.transl_program_correct.
    apply Cshmgenproof.transf_program_match, first_program_translation.
  - apply Cminorgenproof.transl_program_correct.
    apply Cminorgenproof.transf_program_match, second_program_translation.
Qed.

(** Transfer an existing terminating execution directly. This needs no axiom
    selecting behaviors for states that might be stuck or divergent. *)
Lemma forward_simulation_termination L1 L2
  (FS : forward_simulation L1 L2) s tr last r :
  Smallstep.initial_state L1 s ->
  Star L1 s tr last ->
  Smallstep.final_state L1 last r ->
  program_behaves L2 (Terminates tr r).
Proof.
  intros INIT RUN FINAL.
  destruct FS as [index order matches properties].
  destruct (@fsim_match_initial_states L1 L2 index order matches properties s INIT)
    as [i [ts [TINIT MATCH]]].
  destruct (@simulation_star L1 L2 index order matches properties
    s tr last RUN i ts MATCH) as [i' [last' [TRUN MATCH']]].
  eapply program_runs; [exact TINIT |].
  eapply state_terminates; [exact TRUN |].
  eapply fsim_match_final_states; eassumption.
Qed.

Section ExternalCosine.
Hypothesis cosine_left : external_call cosine_external App.ge [Vfloat left_node]
  App.initial_memory E0 (Vfloat cosine_value) App.initial_memory.
Hypothesis cosine_right : external_call cosine_external App.ge [Vfloat right_node]
  App.initial_memory E0 (Vfloat cosine_value) App.initial_memory.

Theorem application_terminates :
  program_behaves (Cminor.semantics cminor_program) (Terminates App.result_trace Int.zero).
Proof.
  eapply forward_simulation_termination.
  - exact application_forward_simulation.
  - exact App.main_initial_state.
  - exact (App.main_steps cosine_left cosine_right).
  - constructor.
Qed.

Theorem application_all_behaviors beh :
  program_behaves (Cminor.semantics cminor_program) beh ->
  beh = Terminates App.result_trace Int.zero.
Proof.
  eapply annotation_terminating_behavior_unique.
  - apply Cminor.semantics_determinate.
  - repeat constructor.
  - exact application_terminates.
Qed.

End ExternalCosine.

Print Assumptions first_program_translation.
Print Assumptions second_program_translation.
Print Assumptions application_forward_simulation.
Print Assumptions application_terminates.
Print Assumptions application_all_behaviors.
