From Coq Require Import List ZArith String.
From compcert Require Import Coqlib Maps Integers Floats Values AST Memory Events
  Globalenvs Smallstep Behaviors Ctypes Cop Clight ClightBigstep.
From QuadratureC Require Import quadrules ClightExample ClightLibrary
  ClightDeterminism AnnotatedBehavior ClightApplication InternalCosine.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(** A separate application variant replaces the external cosine declaration
    with the internally evaluated degree-14 polynomial. Every other library
    definition, including the stored quadrature constants, is retained. *)
Definition result_temp := ClightApplication.result_temp.
Definition result_annotation := ClightApplication.result_annotation.
Definition result_trace := ClightApplication.result_trace.
Definition application_main := ClightApplication.application_main.

Definition replace_cosine (entry : ident * globdef Clight.fundef type) :=
  if Pos.eqb (fst entry) _cos
  then (fst entry, Gfun (Internal cosine_function))
  else entry.

Definition polynomial_definitions := map replace_cosine global_definitions.

Definition application : Clight.program := {|
  prog_defs := polynomial_definitions ++ [(_main, Gfun (Internal application_main))];
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
    (polynomial_definitions ++ [(_main, Gfun (Internal application_main))])) in H.
  apply in_app_or in H. destruct H as [H | H].
  2: { destruct H as [H | H]; [discriminate | contradiction]. }
  unfold polynomial_definitions in H.
  apply in_map_iff in H. destruct H as [[name def] [Heq H]].
  unfold replace_cosine in Heq. cbn [fst] in Heq.
  destruct (Pos.eqb name _cos); [discriminate |].
  inversion Heq; subst; clear Heq.
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
      Internal cosine_function |}.
  - intros id H. cbn [library_symbols In] in H.
    repeat match type of H with
    | _ \/ _ => destruct H as [H | H]; [subst id; vm_compute; reflexivity |]
    end. contradiction.
  - intros id H. cbn [library_functions In] in H.
    repeat match type of H with
    | _ \/ _ => destruct H as [H | H]; [subst id; vm_compute; reflexivity |]
    end. contradiction.
  - reflexivity.
  - reflexivity.
  - exact application_point_loads.
  - exact application_weight_loads.
Defined.

Local Opaque initial_memory.

Theorem library_execution :
  ClightBigstep.Clight2.eval_funcall ge initial_memory
    (Internal f_integrate_testfun) [] E0 initial_memory (Vfloat cosine_value).
Proof.
  apply (ClightLibrary.integrate_testfun_execution application_context).
  - apply InternalCosine.cosine_left_execution.
  - apply InternalCosine.cosine_right_execution.
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

Print Assumptions initial_memory_exists.
Print Assumptions application_terminates.
Print Assumptions application_all_behaviors.
