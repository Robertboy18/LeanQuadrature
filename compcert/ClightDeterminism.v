From Coq Require Import List.
From compcert Require Import Coqlib Maps Integers Values Events Memory
  Globalenvs Ctypes Cop Clight Smallstep.

Import ListNotations.

(** Determinacy of the pure expressions in normalized Clight. *)
Lemma deref_loc_determ ty m b ofs bf v1 v2 :
  deref_loc ty m b ofs bf v1 ->
  deref_loc ty m b ofs bf v2 ->
  v1 = v2.
Proof.
  intros H1 H2. inversion H1; inversion H2; subst; try congruence.
  repeat match goal with H : load_bitfield _ _ _ _ _ _ _ _ |- _ =>
    inversion H; subst; clear H
  end. congruence.
Qed.

Lemma assign_loc_determ ce ty m b ofs bf v m1 m2 :
  assign_loc ce ty m b ofs bf v m1 ->
  assign_loc ce ty m b ofs bf v m2 ->
  m1 = m2.
Proof.
  intros H1 H2. inversion H1; inversion H2; subst; try congruence.
  all: repeat match goal with H : store_bitfield _ _ _ _ _ _ _ _ _ _ |- _ =>
    inversion H; subst; clear H
  end.
  all: congruence.
Qed.

Section Expressions.

Variable ge : genv.
Variable e : env.
Variable le : temp_env.
Variable m : mem.

Ltac eliminate_non_lvalues :=
  repeat match goal with
  | H : eval_lvalue _ _ _ _ ?a _ _ _ |- _ =>
      lazymatch a with
      | Econst_int _ _ => inversion H
      | Econst_float _ _ => inversion H
      | Econst_single _ _ => inversion H
      | Econst_long _ _ => inversion H
      | Etempvar _ _ => inversion H
      | Eaddrof _ _ => inversion H
      | Eunop _ _ _ => inversion H
      | Ebinop _ _ _ _ => inversion H
      | Ecast _ _ => inversion H
      | Esizeof _ _ => inversion H
      | Ealignof _ _ => inversion H
      end
  end.

Ltac use_expression_induction :=
  repeat match goal with
  | IH : forall v', eval_expr ge e le m ?a v' -> ?v = v',
    HE : eval_expr ge e le m ?a ?v' |- _ =>
      tryif constr_eq v v' then fail 0 else
        let EQ := fresh "EQ" in
        pose proof (IH _ HE) as EQ; clear IH; inversion EQ; subst; try clear EQ
  | IH : forall b' ofs' bf', eval_lvalue ge e le m ?a b' ofs' bf' ->
      ?b = b' /\ ?ofs = ofs' /\ ?bf = bf',
    HL : eval_lvalue ge e le m ?a ?b' ?ofs' ?bf' |- _ =>
      tryif (constr_eq b b'; constr_eq ofs ofs'; constr_eq bf bf') then fail 0 else
        let EB := fresh "EB" in let EO := fresh "EO" in let EF := fresh "EF" in
        destruct (IH _ _ _ HL) as [EB [EO EF]]; clear IH; subst
  end.

Lemma eval_expr_lvalue_determ :
  (forall a v, eval_expr ge e le m a v ->
    forall v', eval_expr ge e le m a v' -> v = v') /\
  (forall a b ofs bf, eval_lvalue ge e le m a b ofs bf ->
    forall b' ofs' bf', eval_lvalue ge e le m a b' ofs' bf' ->
      b = b' /\ ofs = ofs' /\ bf = bf').
Proof.
  apply eval_expr_lvalue_ind; intros.
  all: match goal with
    | H : eval_expr _ _ _ _ _ ?v' |- _ = ?v' => inversion H; subst; clear H
    | H : eval_lvalue _ _ _ _ _ ?b' ?ofs' ?bf' |- _ /\ _ =>
        inversion H; subst; clear H
    end.
  all: eliminate_non_lvalues.
  all: use_expression_induction.
  all: try solve [repeat split; congruence].
  all: eapply deref_loc_determ; eassumption.
Qed.

Lemma eval_expr_determ a v1 v2 :
  eval_expr ge e le m a v1 ->
  eval_expr ge e le m a v2 -> v1 = v2.
Proof. intros H1 H2. exact (proj1 eval_expr_lvalue_determ a v1 H1 v2 H2). Qed.

Lemma eval_lvalue_determ a b1 ofs1 bf1 b2 ofs2 bf2 :
  eval_lvalue ge e le m a b1 ofs1 bf1 ->
  eval_lvalue ge e le m a b2 ofs2 bf2 ->
  b1 = b2 /\ ofs1 = ofs2 /\ bf1 = bf2.
Proof.
  intros H1 H2.
  exact (proj2 eval_expr_lvalue_determ a b1 ofs1 bf1 H1 b2 ofs2 bf2 H2).
Qed.

Lemma eval_exprlist_determ al tyl vl1 vl2 :
  eval_exprlist ge e le m al tyl vl1 ->
  eval_exprlist ge e le m al tyl vl2 -> vl1 = vl2.
Proof.
  intros H1. revert vl2. induction H1; intros vl2 H2; inversion H2; subst.
  - reflexivity.
  - match goal with HE : eval_expr _ _ _ _ _ _ |- _ =>
      pose proof (eval_expr_determ _ _ _ H HE) as EQ
    end.
    subst. f_equal; [congruence |].
    match goal with
    | IH : forall vs, eval_exprlist _ _ _ _ _ _ vs -> _ = vs |- _ =>
        eapply IH; eassumption
    end.
Qed.

End Expressions.

Lemma alloc_variables_determ ge e m vars e1 m1 e2 m2 :
  alloc_variables ge e m vars e1 m1 ->
  alloc_variables ge e m vars e2 m2 ->
  e1 = e2 /\ m1 = m2.
Proof.
  intros H1. revert e2 m2.
  induction H1; intros e' m' H2; inversion H2; subst.
  - auto.
  - match goal with
    | HA : Mem.alloc _ _ _ = ?p1, HB : Mem.alloc _ _ _ = ?p2 |- _ =>
        tryif constr_eq p1 p2 then fail 0 else
          assert (p1 = p2) as EQ by congruence;
          inversion EQ; subst; try clear EQ
    end.
    eapply IHalloc_variables; eassumption.
Qed.

Lemma function_entry2_determ ge f args m e1 le1 m1 e2 le2 m2 :
  function_entry2 ge f args m e1 le1 m1 ->
  function_entry2 ge f args m e2 le2 m2 ->
  e1 = e2 /\ le1 = le2 /\ m1 = m2.
Proof.
  intros H1 H2. inversion H1; inversion H2; subst.
  match goal with
  | HA : alloc_variables _ _ _ _ e1 m1,
    HB : alloc_variables _ _ _ _ e2 m2 |- _ =>
      destruct (alloc_variables_determ _ _ _ _ _ _ _ _ HA HB)
  end.
  subst. repeat split; congruence.
Qed.

Ltac identify_functional_results :=
  repeat match goal with
  | H1 : ?lhs = ?rhs1, H2 : ?lhs = ?rhs2 |- _ =>
      tryif constr_eq rhs1 rhs2 then fail 0 else
        let EQ := fresh "EQ" in
        assert (rhs1 = rhs2) as EQ by congruence;
        clear H2; inversion EQ; subst; try clear EQ
  end.

Ltac identify_expression_results :=
  repeat match goal with
  | H1 : eval_expr ?ge ?e ?le ?m ?a ?v1,
    H2 : eval_expr ?ge ?e ?le ?m ?a ?v2 |- _ =>
      tryif constr_eq v1 v2 then fail 0 else
        let EQ := fresh "EQ" in
        pose proof (eval_expr_determ _ _ _ _ _ _ _ H1 H2) as EQ;
        clear H2; subst
  | H1 : eval_lvalue ?ge ?e ?le ?m ?a ?b1 ?ofs1 ?bf1,
    H2 : eval_lvalue ?ge ?e ?le ?m ?a ?b2 ?ofs2 ?bf2 |- _ =>
      tryif (constr_eq b1 b2; constr_eq ofs1 ofs2; constr_eq bf1 bf2)
      then fail 0 else
        let EB := fresh in let EO := fresh in let EF := fresh in
        destruct (eval_lvalue_determ _ _ _ _ _ _ _ _ _ _ _ H1 H2)
          as [EB [EO EF]]; clear H2; subst
  | H1 : eval_exprlist ?ge ?e ?le ?m ?al ?tyl ?vs1,
    H2 : eval_exprlist ?ge ?e ?le ?m ?al ?tyl ?vs2 |- _ =>
      tryif constr_eq vs1 vs2 then fail 0 else
        let EQ := fresh "EQ" in
        pose proof (eval_exprlist_determ _ _ _ _ _ _ _ _ H1 H2) as EQ;
        clear H2; subst
  end.

(** Normalized Clight is determinate under CompCert's external-call contract.
    A matching trace may vary only in values supplied by the environment. *)
Theorem step2_determinate ge s t1 s1 :
  step2 ge s t1 s1 ->
  forall t2 s2, step2 ge s t2 s2 ->
    match_traces ge t1 t2 /\ (t1 = t2 -> s1 = s2).
Proof.
  intros H1 t2 s2 H2.
  inversion H1; subst; inversion H2; subst; clear H1 H2.
  all: repeat match goal with H : _ \/ _ |- _ => destruct H; subst end.
  all: try discriminate.
  all: try contradiction.
  all: identify_functional_results.
  all: identify_expression_results.
  all: identify_functional_results.
  all: try solve [split; [constructor | intros; reflexivity]].
  all: try solve [
    match goal with
    | H1 : assign_loc _ _ _ _ _ _ _ _,
      H2 : assign_loc _ _ _ _ _ _ _ _ |- _ =>
        split; [constructor | intros; f_equal; eapply assign_loc_determ; eassumption]
    end].
  all: try solve [
    match goal with
    | H1 : function_entry2 _ _ _ _ _ _ _,
      H2 : function_entry2 _ _ _ _ _ _ _ |- _ =>
        destruct (function_entry2_determ _ _ _ _ _ _ _ _ _ _ H1 H2)
          as [? [? ?]]; subst; split; [constructor | intros; reflexivity]
    end].
  all: try solve [
    match goal with
    | H1 : external_call ?ef ?ge ?args ?m ?t1 ?v1 ?m1,
      H2 : external_call ?ef ?ge ?args ?m ?t2 ?v2 ?m2 |- _ =>
        destruct (external_call_determ ef ge args m t1 v1 m1 t2 v2 m2 H1 H2)
          as [HT HE]; split; [exact HT |];
        intros EQ; destruct (HE EQ); subst; reflexivity
    end].
Qed.

Theorem semantics2_determinate p : determinate (Clight.semantics2 p).
Proof.
  constructor; simpl.
  - intros s t1 s1 t2 s2 H1 H2.
    exact (step2_determinate (Clight.globalenv p) s t1 s1 H1 t2 s2 H2).
  - red; simpl; intros. inversion H; subst; simpl; try lia.
    all: eapply external_call_trace_length; eauto.
  - intros s1 s2 H1 H2. inversion H1; inversion H2; subst.
    unfold ge, ge0 in *. congruence.
  - intros s r FINAL t next STEP. inversion FINAL; subst. inversion STEP.
  - intros s r1 r2 H1 H2. inversion H1; inversion H2; subst. congruence.
Qed.

(** An empty trace also fixes every competing trace. *)
Theorem step2_silent_determ ge s s1 :
  step2 ge s E0 s1 ->
  forall t s2, step2 ge s t s2 -> t = E0 /\ s1 = s2.
Proof.
  intros H1 t s2 H2.
  destruct (step2_determinate _ _ _ _ H1 _ _ H2) as [HT EQ].
  inversion HT; subst. split; [reflexivity | exact (EQ eq_refl)].
Qed.

Lemma silent_termination_step ge s last :
  star step2 ge s E0 last ->
  nostep step2 ge last ->
  forall t next, step2 ge s t next ->
    t = E0 /\ star step2 ge next E0 last.
Proof.
  intros RUN LAST t next STEP.
  inversion RUN as [| s0 t1 s1 t2 s2 t0 FIRST REST TRACE]; subst.
  - exfalso. exact (LAST _ _ STEP).
  - destruct (Eapp_E0_inv _ _ (eq_sym TRACE)); subst.
    destruct (step2_silent_determ _ _ _ FIRST _ _ STEP); subst.
    split; [reflexivity | exact REST].
Qed.

(** Every finite execution prefix remains on a path to the specified return. *)
Theorem silent_termination_prefix ge s last :
  star step2 ge s E0 last ->
  nostep step2 ge last ->
  forall t next, star step2 ge s t next ->
    t = E0 /\ star step2 ge next E0 last.
Proof.
  intros RUN LAST t next PREFIX. revert RUN.
  induction PREFIX as [x | x t1 y t2 z t STEP MORE IH TRACE]; intros RUN.
  - auto.
  - destruct (silent_termination_step _ _ _ RUN LAST _ _ STEP) as [HT REM].
    destruct (IH REM) as [HT' END]. subst.
    split; [reflexivity | exact END].
Qed.

Lemma return_Kstop_nostep ge v m :
  nostep step2 ge (Returnstate v Kstop m).
Proof. intros t s H. inversion H. Qed.

Theorem silent_return_safe ge s v m :
  star step2 ge s E0 (Returnstate v Kstop m) ->
  forall t next, star step2 ge s t next ->
    t = E0 /\
    (next = Returnstate v Kstop m \/ exists next', step2 ge next E0 next').
Proof.
  intros RUN t next PREFIX.
  destruct (silent_termination_prefix _ _ _ RUN
    (return_Kstop_nostep _ _ _) _ _ PREFIX) as [HT REM].
  split; [exact HT |].
  inversion REM as [| s0 t1 s1 t2 s2 t0 FIRST REST TRACE]; subst.
  - left. reflexivity.
  - destruct (Eapp_E0_inv _ _ (eq_sym TRACE)); subst.
    right. eauto.
Qed.

Theorem silent_return_unique ge s v m :
  star step2 ge s E0 (Returnstate v Kstop m) ->
  forall t v' m', star step2 ge s t (Returnstate v' Kstop m') ->
    t = E0 /\ v' = v /\ m' = m.
Proof.
  intros RUN t v' m' PREFIX.
  destruct (silent_termination_prefix _ _ _ RUN
    (return_Kstop_nostep _ _ _) _ _ PREFIX) as [HT REM].
  split; [exact HT |].
  inversion REM; subst.
  - auto.
  - exfalso. eapply return_Kstop_nostep; eassumption.
Qed.

(** Accessibility of the successor relation rules out every infinite execution,
    not merely divergence along the constructed execution witness. *)
Definition step_successor ge (next current : Clight.state) : Prop :=
  exists t, step2 ge current t next.

Theorem silent_termination_accessible ge s last :
  star step2 ge s E0 last ->
  nostep step2 ge last ->
  Acc (step_successor ge) s.
Proof.
  apply (@star_E0_ind _ _ step2 ge
    (fun s last => nostep step2 ge last -> Acc (step_successor ge) s)).
  - intros s0 LAST. constructor. intros next [t STEP].
    exfalso. exact (LAST _ _ STEP).
  - intros s0 s1 s2 STEP IH LAST. constructor. intros next [t OTHER].
    destruct (step2_silent_determ _ _ _ STEP _ _ OTHER); subst.
    exact (IH LAST).
Qed.

Record total_call_correct ge s v m : Prop := {
  call_execution : star step2 ge s E0 (Returnstate v Kstop m);
  call_accessible : Acc (step_successor ge) s;
  call_reachable_safe : forall t next, star step2 ge s t next ->
    t = E0 /\
    (next = Returnstate v Kstop m \/ exists next', step2 ge next E0 next');
  call_unique_return : forall t v' m',
    star step2 ge s t (Returnstate v' Kstop m') ->
    t = E0 /\ v' = v /\ m' = m
}.

Theorem silent_total_call_correct ge s v m :
  star step2 ge s E0 (Returnstate v Kstop m) ->
  total_call_correct ge s v m.
Proof.
  intros RUN. constructor.
  - exact RUN.
  - eapply silent_termination_accessible; [exact RUN | apply return_Kstop_nostep].
  - apply silent_return_safe. exact RUN.
  - apply silent_return_unique. exact RUN.
Qed.

Print Assumptions step2_silent_determ.
Print Assumptions semantics2_determinate.
Print Assumptions silent_return_safe.
Print Assumptions silent_return_unique.
Print Assumptions silent_termination_accessible.
Print Assumptions silent_total_call_correct.
