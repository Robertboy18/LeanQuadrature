From Coq Require Import List ZArith String.
From compcert Require Import Coqlib Maps Integers Floats Values AST Memory Events
  Globalenvs Smallstep Behaviors Ctypes Cop Clight ClightBigstep.
From QuadratureC Require Import quadrules ClightExample ClightLibrary
  ClightDeterminism AnnotatedBehavior.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(** A normalized Clight application around the unmodified quadrature library.
    The annotation makes the computed binary64 result observable in CompCert's
    trace semantics. It is not a C-library printing implementation. *)
Definition result_temp : ident := 1000%positive.
Definition result_annotation := EF_annot 1 "quadrature-result" [AST.Tfloat].
Definition result_trace : trace :=
  [Event_annot "quadrature-result" [EVfloat cosine_value]].

Definition application_main : Clight.function := {| 
  fn_return := type_int32s;
  fn_callconv := cc_default;
  fn_params := [];
  fn_vars := [];
  fn_temps := [(result_temp, Tfloat F64 noattr)];
  fn_body :=
    Ssequence
      (Scall (Some result_temp)
        (Evar _integrate_testfun
          (Tfunction [] (Tfloat F64 noattr) cc_default)) [])
      (Ssequence
        (Sbuiltin None result_annotation [Tfloat F64 noattr]
          [Etempvar result_temp (Tfloat F64 noattr)])
        (Sreturn (Some (Econst_int Int.zero type_int32s))))
|}.

Definition application : Clight.program := {|
  prog_defs := quadrules.prog.(prog_defs) ++ [(_main, Gfun (Internal application_main))];
  prog_public := _main :: quadrules.prog.(prog_public);
  prog_main := _main;
  prog_types := quadrules.prog.(prog_types);
  prog_comp_env := quadrules.prog.(prog_comp_env);
  prog_comp_env_eq := quadrules.prog.(prog_comp_env_eq)
|}.

Definition ge := Clight.globalenv application.

Lemma application_initializes : exists m, Genv.init_mem application = Some m.
Proof.
  apply Genv.init_mem_exists.
  intros id v H.
  change (In (id, Gvar v)
    (global_definitions ++ [(_main, Gfun (Internal application_main))])) in H.
  apply in_app_or in H. destruct H as [H | H].
  2: { destruct H as [H | H]; [discriminate | contradiction]. }
  cbn [global_definitions In] in H.
  repeat match type of H with
  | _ \/ _ => destruct H as [H | H]; [inversion H; subst; clear H |]
  end; try contradiction;
  split.
  all: try (intros i o H; simpl in H; intuition discriminate).
  all: cbn [v___stringlit_1 v___stringlit_2 v___stderrp v_gauss_pts v_gauss_wts
    gvar_init Genv.init_data_list_aligned Genv.init_data_alignment init_data_size].
  all: repeat match goal with |- _ /\ _ => split end.
  all: try exact I.
  all: apply Z.mod_divide; [discriminate | reflexivity].
Qed.

Definition initialized_memory : { m : mem | Genv.init_mem application = Some m }.
Proof.
  destruct (Genv.init_mem application) as [m |] eqn:H.
  - exists m. reflexivity.
  - exfalso. destruct application_initializes as [m Hm]. congruence.
Qed.

Definition initial_memory := proj1_sig initialized_memory.

Theorem initial_memory_exists : Genv.init_mem application = Some initial_memory.
Proof. exact (proj2_sig initialized_memory). Qed.

Lemma application_point_loads :
  Mem.load Mfloat64 initial_memory points_block 8 = Some (Vfloat left_node) /\
  Mem.load Mfloat64 initial_memory points_block 16 = Some (Vfloat right_node).
Proof.
  assert (HF : Genv.find_var_info (Genv.globalenv application) points_block =
    Some v_gauss_pts) by reflexivity.
  pose proof (Genv.init_mem_characterization application points_block HF
    initial_memory_exists) as [_ [_ [H _]]].
  specialize (H eq_refl). cbn [Genv.load_store_init_data gvar_init] in H.
  exact (conj (proj1 (proj2 H)) (proj1 (proj2 (proj2 H)))).
Qed.

Lemma application_weight_loads :
  Mem.load Mfloat64 initial_memory weights_block 8 = Some (Vfloat one) /\
  Mem.load Mfloat64 initial_memory weights_block 16 = Some (Vfloat one).
Proof.
  assert (HF : Genv.find_var_info (Genv.globalenv application) weights_block =
    Some v_gauss_wts) by reflexivity.
  pose proof (Genv.init_mem_characterization application weights_block HF
    initial_memory_exists) as [_ [_ [H _]]].
  specialize (H eq_refl). cbn [Genv.load_store_init_data gvar_init] in H.
  exact (conj (proj1 (proj2 H)) (proj1 (proj2 (proj2 H)))).
Qed.

Definition application_context : library_context.
Proof.
  refine {| context_program := application; context_memory := initial_memory;
    context_cosine :=
      External cosine_external [Tfloat F64 noattr] (Tfloat F64 noattr) cc_default |}.
  - intros id H. cbn [library_symbols In] in H.
    repeat match type of H with
    | _ \/ _ => destruct H as [H | H]; [subst id; vm_compute; reflexivity |]
    end. contradiction.
  - intros id H. cbn [library_functions In] in H.
    repeat match type of H with
    | _ \/ _ => destruct H as [H | H]; [subst id; vm_compute; reflexivity |]
    end. contradiction.
  - vm_compute. reflexivity.
  - reflexivity.
  - exact application_point_loads.
  - exact application_weight_loads.
Defined.

Local Opaque initial_memory.

Section ExternalCosine.
Hypothesis cosine_left : external_call cosine_external ge [Vfloat left_node]
  initial_memory E0 (Vfloat cosine_value) initial_memory.
Hypothesis cosine_right : external_call cosine_external ge [Vfloat right_node]
  initial_memory E0 (Vfloat cosine_value) initial_memory.

Theorem library_execution :
  ClightBigstep.Clight2.eval_funcall ge initial_memory
    (Internal f_integrate_testfun) [] E0 initial_memory (Vfloat cosine_value).
Proof.
  apply (ClightLibrary.integrate_testfun_execution application_context).
  - apply eval_funcall_external. exact cosine_left.
  - apply eval_funcall_external. exact cosine_right.
Qed.

Theorem main_execution :
  ClightBigstep.Clight2.eval_funcall ge initial_memory (Internal application_main)
    [] result_trace initial_memory (Vint Int.zero).
Proof.
  unfold ClightBigstep.Clight2.eval_funcall.
  eapply eval_funcall_internal with
    (e := empty_env) (m1 := initial_memory) (m2 := initial_memory).
  - eapply function_entry2_intro.
    + constructor.
    + constructor.
    + vm_compute. intuition congruence.
    + change (alloc_variables ge empty_env initial_memory [] empty_env initial_memory).
      constructor.
    + reflexivity.
  - cbn [application_main fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := result_trace).
    + eapply exec_Scall.
      * reflexivity.
      * eapply eval_Elvalue.
        -- eapply eval_Evar_global; vm_compute; reflexivity.
        -- apply deref_loc_reference. reflexivity.
      * constructor.
      * vm_compute. reflexivity.
      * reflexivity.
      * exact library_execution.
    + rewrite <- (E0_right result_trace).
      eapply exec_Sseq_1 with (t1 := result_trace) (t2 := E0).
      * eapply exec_Sbuiltin.
        -- eapply eval_Econs.
           ++ apply eval_Etempvar. reflexivity.
           ++ reflexivity.
           ++ constructor.
        -- cbn [result_annotation external_call].
           constructor. repeat constructor.
      * apply exec_Sreturn_some. constructor.
  - split; [discriminate | reflexivity].
  - reflexivity.
Qed.

Theorem main_initial_state :
  Clight.initial_state application
    (Callstate (Internal application_main) [] Kstop initial_memory).
Proof.
  eapply initial_state_intro.
  - exact initial_memory_exists.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
Qed.

Theorem main_steps :
  star Clight.step2 ge
    (Callstate (Internal application_main) [] Kstop initial_memory)
    result_trace (Returnstate (Vint Int.zero) Kstop initial_memory).
Proof.
  eapply (ClightBigstep.eval_funcall_steps function_entry2 application).
  - exact main_execution.
  - exact I.
Qed.

Theorem application_terminates :
  program_behaves (Clight.semantics2 application) (Terminates result_trace Int.zero).
Proof.
  eapply program_runs.
  - exact main_initial_state.
  - eapply state_terminates.
    + exact main_steps.
    + constructor.
Qed.

Theorem application_all_behaviors beh :
  program_behaves (Clight.semantics2 application) beh ->
  beh = Terminates result_trace Int.zero.
Proof.
  eapply annotation_terminating_behavior_unique.
  - apply semantics2_determinate.
  - repeat constructor.
  - exact application_terminates.
Qed.

End ExternalCosine.

Print Assumptions initial_memory_exists.
Print Assumptions application_terminates.
Print Assumptions application_all_behaviors.
