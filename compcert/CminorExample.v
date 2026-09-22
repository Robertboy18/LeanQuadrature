From Coq Require Import List ZArith.
From compcert Require Import Coqlib Maps Errors Integers Floats AST Values Events
  Memory Globalenvs Smallstep Ctypes Clight Csharpminor Cshmgen Cminor
  Cminorgen Cminorgenproof.
From QuadratureC Require Import quadrules ClightExample ClightRules CsharpminorExample.

Import ListNotations.
Module CS := CsharpminorExample.

(** Compose the two actual lowering passes on the pinned source artifact. *)
Definition cminor_translation : res Cminor.program :=
  match Cshmgen.transl_program quadrules.prog with
  | OK p => Cminorgen.transl_program p
  | Error msg => Error msg
  end.

Lemma cminorgen_succeeds : translation_succeeded cminor_translation = true.
Proof. vm_compute. reflexivity. Qed.

Definition compiled_program : { p : Cminor.program | cminor_translation = OK p }.
Proof.
  destruct cminor_translation as [p | msg] eqn:H.
  - exists p. reflexivity.
  - exfalso. pose proof cminorgen_succeeds as HS. rewrite H in HS. discriminate.
Qed.

Definition tprog := proj1_sig compiled_program.

Theorem program_translation : Cminorgen.transl_program CS.tprog = OK tprog.
Proof.
  pose proof (proj2_sig compiled_program) as H.
  change (cminor_translation = OK tprog) in H.
  unfold cminor_translation in H. rewrite CS.program_translation in H. exact H.
Qed.

Lemma programs_match : Cminorgenproof.match_prog CS.tprog tprog.
Proof. apply Cminorgenproof.transf_program_match, program_translation. Qed.

Theorem compiled_program_initializes : Genv.init_mem tprog = Some initial_memory.
Proof.
  exact (Genv.init_mem_transf_partial programs_match CS.compiled_program_initializes).
Qed.

Lemma transfer_steps :
  forall s tr s', star Csharpminor.step (Genv.globalenv CS.tprog) s tr s' ->
  forall ts, Cminorgenproof.match_states CS.tprog s ts ->
  exists ts',
    star Cminor.step (Genv.globalenv tprog) ts tr ts' /\
    Cminorgenproof.match_states CS.tprog s' ts'.
Proof.
  intros s tr s' RUN.
  induction RUN as [s | s1 t1 s2 t2 s3 t STEP REST IH TRACE]; intros ts HM.
  - exists ts. split; [apply star_refl | exact HM].
  - destruct (Cminorgenproof.transl_step_correct CS.tprog tprog programs_match
      _ _ _ STEP _ HM) as [[ts2 [TSTEP HM2]] | [MEASURE [HT HM2]]].
    + destruct (IH _ HM2) as [ts3 [TREST HM3]].
      exists ts3. split; [| exact HM3].
      eapply star_trans; [apply plus_star; exact TSTEP | exact TREST | assumption].
    + subst t1. simpl in TRACE. subst t.
      exact (IH _ HM2).
Qed.

Lemma match_float_return_Kstop value m ts :
  Cminorgenproof.match_states CS.tprog
    (Csharpminor.Returnstate (Vfloat value) Csharpminor.Kstop m) ts ->
  exists tm inj,
    ts = Cminor.Returnstate (Vfloat value) Cminor.Kstop tm /\
    Mem.inject inj m tm.
Proof.
  intros HM. inversion HM; subst. inversion MK; subst.
  inversion RESINJ; subst. eauto.
Qed.

Lemma transfer_library_call sfd args value b :
  Genv.find_funct_ptr (Genv.globalenv CS.tprog) b = Some sfd ->
  Val.inject_list (Mem.flat_inj (Mem.nextblock initial_memory)) args args ->
  star Csharpminor.step (Genv.globalenv CS.tprog)
    (Csharpminor.Callstate sfd args Csharpminor.Kstop initial_memory) E0
    (Csharpminor.Returnstate (Vfloat value) Csharpminor.Kstop initial_memory) ->
  exists tfd tm inj,
    Genv.find_funct_ptr (Genv.globalenv tprog) b = Some tfd /\
    star Cminor.step (Genv.globalenv tprog)
      (Cminor.Callstate tfd args Cminor.Kstop initial_memory) E0
      (Cminor.Returnstate (Vfloat value) Cminor.Kstop tm) /\
    Mem.inject inj initial_memory tm.
Proof.
  intros HF HA RUN.
  destruct (Cminorgenproof.function_ptr_translated CS.tprog tprog programs_match
    _ _ HF) as [tfd [HTF HT]].
  assert (HM : Cminorgenproof.match_states CS.tprog
    (Csharpminor.Callstate sfd args Csharpminor.Kstop initial_memory)
    (Cminor.Callstate tfd args Cminor.Kstop initial_memory)).
  { eapply Cminorgenproof.match_callstate with
      (f := Mem.flat_inj (Mem.nextblock initial_memory))
      (cs := []) (cenv := PTree.empty Z).
    - exact HT.
    - eapply Genv.initmem_inject. exact CS.compiled_program_initializes.
    - apply Cminorgenproof.mcs_nil with (Mem.nextblock initial_memory).
      + apply Cminorgenproof.match_globalenvs_init. exact CS.compiled_program_initializes.
      + apply Ple_refl.
      + apply Ple_refl.
    - constructor.
    - exact I.
    - exact HA. }
  destruct (transfer_steps _ _ _ RUN _ HM) as [ts [HR HM']].
  destruct (match_float_return_Kstop _ _ _ HM') as [tm [inj [HE HI]]].
  subst ts. exists tfd, tm, inj.
  split; [exact HTF | split; assumption].
Qed.

Section ExternalCosine.

Hypothesis cosine_left :
  external_call cosine_external ge [Vfloat left_node] initial_memory E0
    (Vfloat cosine_value) initial_memory.
Hypothesis cosine_right :
  external_call cosine_external ge [Vfloat right_node] initial_memory E0
    (Vfloat cosine_value) initial_memory.

Theorem integrate_testfun_compiled_execution :
  exists tfd tm inj,
    Genv.find_symbol (Genv.globalenv tprog) _integrate_testfun = Some CS.entry_block /\
    Genv.find_funct_ptr (Genv.globalenv tprog) CS.entry_block = Some tfd /\
    star Cminor.step (Genv.globalenv tprog)
      (Cminor.Callstate tfd [] Cminor.Kstop initial_memory) E0
      (Cminor.Returnstate (Vfloat cosine_value) Cminor.Kstop tm) /\
    Mem.inject inj initial_memory tm.
Proof.
  destruct (CS.integrate_testfun_compiled_execution cosine_left cosine_right)
    as [sfd [HS [HF RUN]]].
  destruct (transfer_library_call _ [] _ _ HF (ltac:(constructor)) RUN)
    as [tfd [tm [inj [HTF [HR HI]]]]].
  exists tfd, tm, inj. split.
  - rewrite (Cminorgenproof.symbols_preserved CS.tprog tprog programs_match). exact HS.
  - split; [exact HTF | split; assumption].
Qed.

End ExternalCosine.

Lemma clight_function_valid_block (p : Clight.program) m b fd :
  Genv.init_mem p = Some m ->
  Genv.find_funct (Clight.globalenv p) (Vptr b Ptrofs.zero) = Some fd ->
  Mem.valid_block m b.
Proof.
  intros HM HF. rewrite Genv.find_funct_find_funct_ptr in HF.
  exact (Genv.find_funct_ptr_not_fresh p b HM HF).
Qed.

Theorem integrate_rule_compiled_execution r f b fd
  (HF : Genv.find_funct ge (Vptr b Ptrofs.zero) = Some fd)
  (HT : type_of_fundef fd =
    Tfunction [Tfloat F64 noattr] (Tfloat F64 noattr) cc_default)
  (HC : forall i, (i < rule_size r)%nat ->
    ClightBigstep.Clight2.eval_funcall ge initial_memory fd
      [Vfloat (rule_node r i)] E0 initial_memory (Vfloat (f (rule_node r i)))) :
  exists tfd tm inj,
    Genv.find_symbol (Genv.globalenv tprog) _integrate = Some CS.integrate_block /\
    Genv.find_funct_ptr (Genv.globalenv tprog) CS.integrate_block = Some tfd /\
    star Cminor.step (Genv.globalenv tprog)
      (Cminor.Callstate tfd
        [Vptr b Ptrofs.zero; Vint (Int.repr (Z.of_nat (rule_size r)))]
        Cminor.Kstop initial_memory) E0
      (Cminor.Returnstate (Vfloat (rule_value f r)) Cminor.Kstop tm) /\
    Mem.inject inj initial_memory tm.
Proof.
  destruct (CS.integrate_rule_compiled_execution r f b fd HF HT HC)
    as [sfd [HS [HSF RUN]]].
  assert (HB : Plt b (Mem.nextblock initial_memory)).
  { exact (clight_function_valid_block quadrules.prog _ _ _
      initial_memory_exists HF). }
  assert (HP : Val.inject (Mem.flat_inj (Mem.nextblock initial_memory))
    (Vptr b Ptrofs.zero) (Vptr b Ptrofs.zero)).
  { eapply Val.inject_ptr with (delta := 0%Z).
    - unfold Mem.flat_inj. apply pred_dec_true. exact HB.
    - reflexivity. }
  destruct (transfer_library_call _
    [Vptr b Ptrofs.zero; Vint (Int.repr (Z.of_nat (rule_size r)))]
    _ _ HSF (ltac:(constructor; [exact HP | repeat constructor])) RUN)
    as [tfd [tm [inj [HTF [HR HI]]]]].
  exists tfd, tm, inj. split.
  - rewrite (Cminorgenproof.symbols_preserved CS.tprog tprog programs_match). exact HS.
  - split; [exact HTF | split; assumption].
Qed.

Print Assumptions program_translation.
Print Assumptions compiled_program_initializes.
Print Assumptions integrate_testfun_compiled_execution.
Print Assumptions integrate_rule_compiled_execution.
