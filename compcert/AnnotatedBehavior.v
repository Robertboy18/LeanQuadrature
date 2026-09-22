From Coq Require Import List.
From compcert Require Import Coqlib Events Smallstep Behaviors.

Import ListNotations.

(** Annotation events carry observations but do not request an input from the
    environment. Matching an annotation therefore fixes its complete value. *)
Definition annotation_event (e : event) : Prop :=
  match e with Event_annot _ _ => True | _ => False end.

Definition annotation_trace (t : trace) : Prop := Forall annotation_event t.

Lemma annotation_trace_app t u :
  annotation_trace (t ** u) <-> annotation_trace t /\ annotation_trace u.
Proof. apply Forall_app. Qed.

Lemma match_annotation_trace ge t u :
  annotation_trace t -> match_traces ge t u -> t = u.
Proof.
  intros AN MT. inversion MT; subst; try reflexivity.
  all: inversion AN; contradiction.
Qed.

Section DeterminateSemantics.

Variable L : semantics.
Hypothesis DET : determinate L.

Definition successor (next current : state L) : Prop :=
  exists t, Step L current t next.

Lemma annotation_step_determ s t next u other :
  annotation_trace t ->
  Step L s t next -> Step L s u other ->
  t = u /\ next = other.
Proof.
  intros AN FIRST OTHER.
  destruct (sd_determ DET _ _ _ _ _ FIRST OTHER) as [MT EQ].
  assert (SAME : t = u) by (eapply match_annotation_trace; eauto).
  split; [exact SAME | exact (EQ SAME)].
Qed.

Lemma annotation_termination_step s tr last :
  Star L s tr last -> annotation_trace tr -> Nostep L last ->
  forall t next, Step L s t next ->
    exists rest, tr = t ** rest /\ Star L next rest last /\ annotation_trace rest.
Proof.
  intros RUN AN LAST t next STEP.
  inversion RUN as [| s0 t1 s1 t2 s2 t0 FIRST REST TRACE]; subst.
  - exfalso. exact (LAST _ _ STEP).
  - apply annotation_trace_app in AN. destruct AN as [AN1 AN2].
    destruct (annotation_step_determ _ _ _ _ _ AN1 FIRST STEP); subst.
    exists t2. auto.
Qed.

Lemma annotation_termination_prefix s tr last :
  Star L s tr last -> annotation_trace tr -> Nostep L last ->
  forall t next, Star L s t next ->
    exists rest, tr = t ** rest /\ Star L next rest last /\ annotation_trace rest.
Proof.
  intros RUN AN LAST t next PREFIX. revert tr RUN AN.
  induction PREFIX as [x | x t1 y t2 z t STEP MORE IH TRACE];
    intros tr RUN AN.
  - exists tr. auto.
  - destruct (annotation_termination_step _ _ _ RUN AN LAST _ _ STEP)
      as [rest [EQ [REM AR]]].
    destruct (IH _ REM AR) as [tail [EQ' [END AT]]].
    exists tail. split; [| auto].
    subst. symmetry. apply Eapp_assoc.
Qed.

Lemma annotation_termination_accessible s tr last :
  Star L s tr last -> annotation_trace tr -> Nostep L last ->
  Acc successor s.
Proof.
  intros RUN. induction RUN as [x | x t1 y t2 z t STEP MORE IH TRACE];
    intros AN LAST.
  - constructor. intros next [u OTHER]. exact (False_ind _ (LAST _ _ OTHER)).
  - subst t. apply annotation_trace_app in AN. destruct AN as [AN1 AN2].
    constructor. intros next [u OTHER].
    destruct (annotation_step_determ _ _ _ _ _ AN1 STEP OTHER); subst.
    exact (IH AN2 LAST).
Qed.

Lemma accessible_star s t next :
  Star L s t next -> Acc successor s -> Acc successor next.
Proof.
  intros RUN. induction RUN; intros AC.
  - exact AC.
  - apply IHRUN. eapply Acc_inv; [exact AC |]. exists t1. exact H.
Qed.

Lemma accessible_not_silent s :
  Acc successor s -> ~ Forever_silent L s.
Proof.
  intros AC. induction AC as [s AC IH]. intros RUN.
  inversion RUN; subst. eapply IH; [eexists; eassumption | eassumption].
Qed.

Lemma accessible_not_reactive s :
  Acc successor s -> forall T, ~ Forever_reactive L s T.
Proof.
  intros AC. induction AC as [s AC IH]. intros T RUN.
  inversion RUN as [s0 next t tail PREFIX NONEMPTY REST]; subst.
  inversion PREFIX as [| x t1 y t2 z tr STEP MORE TRACE]; subst.
  - contradiction.
  - eapply IH; [eexists; exact STEP |].
    eapply star_forever_reactive; eassumption.
Qed.

Theorem annotation_run_behavior s tr last r :
  Star L s tr last -> annotation_trace tr -> final_state L last r ->
  forall beh, state_behaves L s beh -> beh = Terminates tr r.
Proof.
  intros RUN AN FINAL beh BEH.
  assert (LAST : Nostep L last) by (eapply sd_final_nostep; eauto).
  assert (AC : Acc successor s) by (eapply annotation_termination_accessible; eauto).
  inversion BEH; subst.
  - destruct (annotation_termination_prefix _ _ _ RUN AN LAST _ _ H)
      as [rest [EQ [REM AR]]].
    inversion REM; subst.
    + rewrite E0_right.
      f_equal. eapply sd_final_determ; eauto.
    + exfalso. eapply sd_final_nostep; eauto.
  - exfalso. eapply accessible_not_silent; [| eassumption].
    eapply accessible_star; eassumption.
  - exfalso. eapply accessible_not_reactive; eassumption.
  - destruct (annotation_termination_prefix _ _ _ RUN AN LAST _ _ H)
      as [rest [EQ [REM AR]]].
    inversion REM; subst.
    + exfalso. eapply H1; eassumption.
    + exfalso. eapply H0; eassumption.
Qed.

Theorem annotation_program_behavior s tr last r :
  initial_state L s ->
  Star L s tr last -> annotation_trace tr -> final_state L last r ->
  forall beh, program_behaves L beh -> beh = Terminates tr r.
Proof.
  intros INIT RUN AN FINAL beh BEH. inversion BEH; subst.
  - assert (s0 = s) by (eapply sd_initial_determ; eauto). subst s0.
    eapply annotation_run_behavior; eassumption.
  - exfalso. eapply H; eassumption.
Qed.

Theorem annotation_terminating_behavior_unique tr r :
  annotation_trace tr ->
  program_behaves L (Terminates tr r) ->
  forall beh, program_behaves L beh -> beh = Terminates tr r.
Proof.
  intros AN KNOWN. inversion KNOWN; subst.
  inversion H0; subst. eapply annotation_program_behavior; eassumption.
Qed.

End DeterminateSemantics.

Print Assumptions annotation_terminating_behavior_unique.
