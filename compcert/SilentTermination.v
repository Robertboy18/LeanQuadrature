From compcert Require Import Events Smallstep.

(** A finite silent execution in a determinate semantics fixes every competing
    prefix and excludes divergence.  The terminal state can be a library
    return, without being an integer-valued whole-program final state. *)
Module SilentTermination.
Section Semantics.
Variable L : semantics.
Hypothesis DET : determinate L.

Lemma termination_step s last :
  star (step L) (globalenv L) s E0 last ->
  nostep (step L) (globalenv L) last ->
  forall t next, step L (globalenv L) s t next ->
    t = E0 /\ star (step L) (globalenv L) next E0 last.
Proof.
  intros RUN LAST t next STEP.
  inversion RUN as [| s0 t1 s1 t2 s2 t0 FIRST REST TRACE]; subst.
  - exfalso. exact (LAST _ _ STEP).
  - destruct (Eapp_E0_inv _ _ (eq_sym TRACE)); subst.
    destruct (@sd_determ_3 L DET _ _ _ _ STEP FIRST) as [HT HE]. subst.
    split; [reflexivity | exact REST].
Qed.

Theorem termination_prefix s last :
  star (step L) (globalenv L) s E0 last ->
  nostep (step L) (globalenv L) last ->
  forall t next, star (step L) (globalenv L) s t next ->
    t = E0 /\ star (step L) (globalenv L) next E0 last.
Proof.
  intros RUN LAST t next PREFIX. revert RUN.
  induction PREFIX as [x | x t1 y t2 z t STEP MORE IH TRACE]; intros RUN.
  - auto.
  - destruct (termination_step _ _ RUN LAST _ _ STEP) as [HT REM].
    destruct (IH REM) as [HT' END]. subst.
    split; [reflexivity | exact END].
Qed.

Theorem terminal_unique s last :
  star (step L) (globalenv L) s E0 last ->
  nostep (step L) (globalenv L) last ->
  forall t other, star (step L) (globalenv L) s t other ->
    nostep (step L) (globalenv L) other -> t = E0 /\ other = last.
Proof.
  intros RUN LAST t other PREFIX OTHER.
  destruct (termination_prefix _ _ RUN LAST _ _ PREFIX) as [HT REM].
  split; [exact HT |]. inversion REM; subst; [reflexivity |].
  exfalso. eapply OTHER; eassumption.
Qed.

Definition successor (next current : state L) :=
  exists t, step L (globalenv L) current t next.

Theorem termination_accessible s last :
  star (step L) (globalenv L) s E0 last ->
  nostep (step L) (globalenv L) last -> Acc successor s.
Proof.
  apply (@star_E0_ind _ _ (step L) (globalenv L)
    (fun s last => nostep (step L) (globalenv L) last -> Acc successor s)).
  - intros s0 LAST. constructor. intros next [t STEP]. exfalso. exact (LAST _ _ STEP).
  - intros s0 s1 s2 STEP IH LAST. constructor. intros next [t OTHER].
    destruct (@sd_determ_3 L DET _ _ _ _ OTHER STEP); subst.
    exact (IH LAST).
Qed.

Theorem termination_safe s last :
  star (step L) (globalenv L) s E0 last ->
  nostep (step L) (globalenv L) last ->
  forall t next, star (step L) (globalenv L) s t next ->
    t = E0 /\ (next = last \/ exists next', step L (globalenv L) next E0 next').
Proof.
  intros RUN LAST t next PREFIX.
  destruct (termination_prefix _ _ RUN LAST _ _ PREFIX) as [HT REM].
  split; [exact HT |].
  inversion REM as [| s0 t1 s1 t2 s2 t0 FIRST REST TRACE]; subst.
  - left. reflexivity.
  - destruct (Eapp_E0_inv _ _ (eq_sym TRACE)); subst. right. eauto.
Qed.
End Semantics.
End SilentTermination.
