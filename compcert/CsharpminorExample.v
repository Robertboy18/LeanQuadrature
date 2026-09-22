From Coq Require Import List ZArith.
From compcert Require Import Coqlib Errors Integers AST Linking Values Events Memory
  Globalenvs Smallstep Ctypes Clight Csharpminor Cshmgen Cshmgenproof.
From QuadratureC Require Import quadrules ClightExample ClightRules.

Import ListNotations.

(** The first lowering pass runs on the pinned, normalized Clight artifact. *)
Definition translation_succeeded {A : Type} (r : res A) : bool :=
  match r with OK _ => true | Error _ => false end.

Lemma cshmgen_succeeds :
  translation_succeeded (Cshmgen.transl_program prog) = true.
Proof. vm_compute. reflexivity. Qed.

Definition compiled_program :
  { tp : Csharpminor.program | Cshmgen.transl_program prog = OK tp }.
Proof.
  destruct (Cshmgen.transl_program prog) as [tp | msg] eqn:H.
  - exists tp. reflexivity.
  - exfalso. pose proof cshmgen_succeeds as HS. rewrite H in HS. discriminate.
Qed.

Definition tprog := proj1_sig compiled_program.

Theorem program_translation : Cshmgen.transl_program prog = OK tprog.
Proof. exact (proj2_sig compiled_program). Qed.

Lemma programs_match : Cshmgenproof.match_prog prog tprog.
Proof. apply Cshmgenproof.transf_program_match, program_translation. Qed.

Theorem compiled_program_initializes :
  Genv.init_mem tprog = Some initial_memory.
Proof. eapply Genv.init_mem_match; [exact programs_match | exact initial_memory_exists]. Qed.

(** Lift the official pass simulation to a finite library-call execution. *)
Lemma transfer_steps :
  forall s tr s',
    star Clight.step2 ge s tr s' ->
    forall ts, Cshmgenproof.match_states prog tprog s ts ->
    exists ts',
      star Csharpminor.step (Genv.globalenv tprog) ts tr ts' /\
      Cshmgenproof.match_states prog tprog s' ts'.
Proof.
  intros s tr s' H. induction H; intros ts HM.
  - exists ts. split; [apply star_refl | exact HM].
  - destruct (Cshmgenproof.transl_step prog tprog programs_match
      _ _ _ H _ HM) as [ts2 [Hstep HM2]].
    destruct (IHstar _ HM2) as [ts3 [Hsteps HM3]].
    exists ts3. split; [| exact HM3].
    eapply star_trans; [apply plus_star; exact Hstep | exact Hsteps | assumption].
Qed.

Lemma match_return_Kstop v m ts :
  Cshmgenproof.match_states prog tprog
    (Clight.Returnstate v Clight.Kstop m) ts ->
  ts = Csharpminor.Returnstate v Csharpminor.Kstop m.
Proof.
  intros H. inversion H; subst. inversion MK; subst. reflexivity.
Qed.

Lemma transfer_library_call sfd args result block argtypes restype cc :
  Genv.find_funct_ptr ge block = Some sfd ->
  type_of_fundef sfd = Tfunction argtypes restype cc ->
  Val.has_argtype_list args (map argtype_of_type argtypes) ->
  star Clight.step2 ge
    (Clight.Callstate sfd args Clight.Kstop initial_memory) E0
    (Clight.Returnstate result Clight.Kstop initial_memory) ->
  exists tfd,
    Genv.find_funct_ptr (Genv.globalenv tprog) block = Some tfd /\
    star Csharpminor.step (Genv.globalenv tprog)
      (Csharpminor.Callstate tfd args Csharpminor.Kstop initial_memory) E0
      (Csharpminor.Returnstate result Csharpminor.Kstop initial_memory).
Proof.
  intros HF HTY HARGS HE.
  destruct (Cshmgenproof.function_ptr_translated prog tprog programs_match
    _ _ HF) as [cu [tfd [HTF [HT HLINK]]]].
  assert (HM : Cshmgenproof.match_states prog tprog
    (Clight.Callstate sfd args Clight.Kstop initial_memory)
    (Csharpminor.Callstate tfd args Csharpminor.Kstop initial_memory)).
  { eapply Cshmgenproof.match_callstate with
      (cu := cu) (ce := prog_comp_env prog)
      (targs := argtypes) (tres := restype) (cconv := cc).
    - exact HLINK.
    - exact HT.
    - constructor.
    - exact I.
    - exact HTY.
    - exact HARGS. }
  destruct (transfer_steps _ _ _ HE _ HM) as [ts [Hrun Hreturn]].
  apply match_return_Kstop in Hreturn. subst ts.
  exists tfd. split; assumption.
Qed.

Definition entry_block :=
  match Genv.find_symbol ge _integrate_testfun with
  | Some b => b
  | None => 1%positive
  end.

Lemma entry_found :
  Genv.find_symbol ge _integrate_testfun = Some entry_block /\
  Genv.find_funct_ptr ge entry_block = Some (Ctypes.Internal f_integrate_testfun).
Proof. vm_compute. split; reflexivity. Qed.

Section ExternalCosine.

Hypothesis cosine_left :
  external_call cosine_external ge [Vfloat left_node] initial_memory E0
    (Vfloat cosine_value) initial_memory.
Hypothesis cosine_right :
  external_call cosine_external ge [Vfloat right_node] initial_memory E0
    (Vfloat cosine_value) initial_memory.

Theorem integrate_testfun_compiled_execution :
  exists tfd,
    Genv.find_symbol (Genv.globalenv tprog) _integrate_testfun = Some entry_block /\
    Genv.find_funct_ptr (Genv.globalenv tprog) entry_block = Some tfd /\
    star Csharpminor.step (Genv.globalenv tprog)
      (Csharpminor.Callstate tfd [] Csharpminor.Kstop initial_memory) E0
      (Csharpminor.Returnstate (Vfloat cosine_value) Csharpminor.Kstop initial_memory).
Proof.
  destruct entry_found as [HS HF].
  pose proof (integrate_testfun_steps cosine_left cosine_right Clight.Kstop I) as HE.
  destruct (transfer_library_call _ _ _ _ [] (Tfloat F64 noattr) cc_default
    HF eq_refl (ltac:(constructor)) HE) as [tfd [HTF Hrun]].
  exists tfd. split.
  - rewrite (Cshmgenproof.symbols_preserved prog tprog programs_match). exact HS.
  - split; assumption.
Qed.

End ExternalCosine.

Definition integrate_block :=
  match Genv.find_symbol ge _integrate with
  | Some b => b
  | None => 1%positive
  end.

Lemma integrate_found :
  Genv.find_symbol ge _integrate = Some integrate_block /\
  Genv.find_funct_ptr ge integrate_block = Some (Ctypes.Internal f_integrate).
Proof. vm_compute. split; reflexivity. Qed.

Theorem integrate_rule_compiled_execution r f b fd
  (HF : Genv.find_funct ge (Vptr b Ptrofs.zero) = Some fd)
  (HT : type_of_fundef fd =
    Tfunction [Tfloat F64 noattr] (Tfloat F64 noattr) cc_default)
  (HC : forall i, (i < rule_size r)%nat ->
    ClightBigstep.Clight2.eval_funcall ge initial_memory fd
      [Vfloat (rule_node r i)] E0 initial_memory (Vfloat (f (rule_node r i)))) :
  exists tfd,
    Genv.find_symbol (Genv.globalenv tprog) _integrate = Some integrate_block /\
    Genv.find_funct_ptr (Genv.globalenv tprog) integrate_block = Some tfd /\
    star Csharpminor.step (Genv.globalenv tprog)
      (Csharpminor.Callstate tfd
        [Vptr b Ptrofs.zero; Vint (Integers.Int.repr (Z.of_nat (rule_size r)))]
        Csharpminor.Kstop initial_memory) E0
      (Csharpminor.Returnstate (Vfloat (rule_value f r)) Csharpminor.Kstop initial_memory).
Proof.
  destruct integrate_found as [HS HIF].
  pose proof (integrate_rule_steps r f b fd HF HT HC Clight.Kstop I) as HE.
  destruct (transfer_library_call _
    [Vptr b Ptrofs.zero; Vint (Int.repr (Z.of_nat (rule_size r)))]
    _ _ (map snd (Clight.fn_params f_integrate))
    (Tfloat F64 noattr) cc_default HIF eq_refl (ltac:(repeat constructor)) HE)
    as [tfd [HTF Hrun]].
  exists tfd. split.
  - rewrite (Cshmgenproof.symbols_preserved prog tprog programs_match). exact HS.
  - split; assumption.
Qed.

Print Assumptions program_translation.
Print Assumptions compiled_program_initializes.
Check integrate_testfun_compiled_execution.
Print Assumptions integrate_testfun_compiled_execution.
Check integrate_rule_compiled_execution.
Print Assumptions integrate_rule_compiled_execution.
