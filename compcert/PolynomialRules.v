From Coq Require Import List ZArith String.
From compcert Require Import Coqlib Maps Integers Floats Values AST Memory Events
  Globalenvs Smallstep Behaviors Ctypes Cop Clight ClightBigstep.
From QuadratureC Require Import quadrules ClightExample ClightRules RuleLibrary
  ClightDeterminism AnnotatedBehavior InternalCosine.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Module RL := RuleLibrary.RuleLibrary.

Definition testfun_value x :=
  Float.mul (Float.mul half (Float.sub one x)) (polynomial_value x).
Definition result_value r := rule_value testfun_value r.
Definition result_trace r : trace :=
  [Event_annot "quadrature-result" [EVfloat (result_value r)]].
Definition result_temp : ident := 1000%positive.
Definition result_annotation := EF_annot 1 "quadrature-result" [AST.Tfloat].
Definition callback_type := Tfunction [Tfloat F64 noattr] (Tfloat F64 noattr) cc_default.
Definition callback_pointer_type := Tpointer callback_type noattr.

Definition replace_cosine (entry : ident * globdef Clight.fundef type) :=
  if Pos.eqb (fst entry) _cos
  then (fst entry, Gfun (Internal cosine_function))
  else entry.
Definition polynomial_definitions := map replace_cosine global_definitions.

Definition program_of_main (entry : Clight.function) : Clight.program := {|
  prog_defs := polynomial_definitions ++ [(_main, Gfun (Internal entry))];
  prog_public := _main :: quadrules.prog.(prog_public);
  prog_main := _main;
  prog_types := quadrules.prog.(prog_types);
  prog_comp_env := quadrules.prog.(prog_comp_env);
  prog_comp_env_eq := quadrules.prog.(prog_comp_env_eq)
|}.
Lemma program_main_found entry :
  exists b,
    Genv.find_symbol (Genv.globalenv (program_of_main entry)) _main = Some b /\
    Genv.find_funct_ptr (Genv.globalenv (program_of_main entry)) b =
      Some (Internal entry).
Proof. eexists. split; vm_compute; reflexivity. Qed.

Section Order.
Variable r : rule_order.
Definition application_main : Clight.function := {|
  fn_return := type_int32s;
  fn_callconv := cc_default;
  fn_params := [];
  fn_vars := [];
  fn_temps := [(result_temp, Tfloat F64 noattr)];
  fn_body :=
    Ssequence
      (Scall (Some result_temp)
        (Evar _integrate
          (Tfunction [callback_pointer_type; type_int32s] (Tfloat F64 noattr) cc_default))
        [Eaddrof (Evar _testfun callback_type) callback_pointer_type;
         Econst_int (Int.repr (Z.of_nat (rule_size r))) type_int32s])
      (Ssequence
        (Sbuiltin None result_annotation [Tfloat F64 noattr]
          [Etempvar result_temp (Tfloat F64 noattr)])
        (Sreturn (Some (Econst_int Int.zero type_int32s))))
|}.
Definition application := program_of_main application_main.
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

Definition application_context : RL.context.
Proof.
  refine {| RL.context_program := application; RL.context_memory := initial_memory |}.
  - exact initial_memory_exists.
  - intros id H. cbn [RL.library_symbols In] in H.
    repeat match type of H with
    | _ \/ _ => destruct H as [H | H]; [subst id; vm_compute; reflexivity |]
    end. contradiction.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

Local Opaque initial_memory.

Ltac eval_application_args :=
  lazymatch goal with
  | |- eval_exprlist _ _ _ _ [] [] _ => constructor
  | |- eval_exprlist _ _ _ _ (_ :: _) (_ :: _) _ =>
      eapply eval_Econs;
        [ClightExample.eval_closed_expr | reflexivity | eval_application_args]
  end.

Theorem testfun_execution x :
  ClightBigstep.Clight2.eval_funcall ge initial_memory (Internal f_testfun)
    [Vfloat x] E0 initial_memory (Vfloat (testfun_value x)).
Proof.
  unfold ClightBigstep.Clight2.eval_funcall.
  eapply eval_funcall_internal with
    (e := empty_env) (m1 := initial_memory) (m2 := initial_memory).
  - eapply function_entry2_intro.
    + vm_compute. repeat constructor; simpl; intuition congruence.
    + vm_compute. repeat constructor; simpl; intuition congruence.
    + vm_compute. intuition congruence.
    + change (alloc_variables ge empty_env initial_memory [] empty_env initial_memory).
      constructor.
    + reflexivity.
  - cbn [f_testfun fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply exec_Scall with (f := Internal cosine_function).
      * reflexivity.
      * ClightExample.eval_closed_expr.
      * eval_application_args.
      * reflexivity.
      * reflexivity.
      * apply InternalCosine.cosine_execution.
    + apply exec_Sreturn_some. ClightExample.eval_closed_expr.
  - split; [discriminate | reflexivity].
  - reflexivity.
Qed.

Theorem library_execution :
  ClightBigstep.Clight2.eval_funcall ge initial_memory (Internal f_integrate)
    [Vptr ClightExample.testfun_block Ptrofs.zero;
     Vint (Int.repr (Z.of_nat (rule_size r)))] E0 initial_memory
    (Vfloat (result_value r)).
Proof.
  apply (RL.integrate_rule_execution application_context r testfun_value
    ClightExample.testfun_block (Internal f_testfun)).
  - reflexivity.
  - reflexivity.
  - intros i HI. apply testfun_execution.
Qed.

Theorem main_execution :
  ClightBigstep.Clight2.eval_funcall ge initial_memory (Internal application_main)
    [] (result_trace r) initial_memory (Vint Int.zero).
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
    eapply exec_Sseq_1 with (t1 := E0) (t2 := result_trace r).
    + eapply exec_Scall.
      * reflexivity.
      * ClightExample.eval_closed_expr.
      * eval_application_args.
      * reflexivity.
      * reflexivity.
      * exact library_execution.
    + rewrite <- (E0_right (result_trace r)).
      eapply exec_Sseq_1 with (t1 := result_trace r) (t2 := E0).
      * eapply exec_Sbuiltin.
        -- eapply eval_Econs.
           ++ apply eval_Etempvar. reflexivity.
           ++ reflexivity.
           ++ constructor.
        -- cbn [result_annotation external_call]. constructor. repeat constructor.
      * apply exec_Sreturn_some. constructor.
  - split; [discriminate | reflexivity].
  - reflexivity.
Qed.

Theorem main_initial_state :
  Clight.initial_state application
    (Callstate (Internal application_main) [] Kstop initial_memory).
Proof.
  destruct (program_main_found application_main) as [b [HS HF]].
  eapply initial_state_intro.
  - exact initial_memory_exists.
  - exact HS.
  - exact HF.
  - reflexivity.
Qed.

Theorem main_steps :
  star Clight.step2 ge
    (Callstate (Internal application_main) [] Kstop initial_memory)
    (result_trace r) (Returnstate (Vint Int.zero) Kstop initial_memory).
Proof.
  eapply (ClightBigstep.eval_funcall_steps function_entry2 application).
  - exact main_execution.
  - exact I.
Qed.

Theorem application_terminates :
  program_behaves (Clight.semantics2 application) (Terminates (result_trace r) Int.zero).
Proof.
  eapply program_runs.
  - exact main_initial_state.
  - eapply state_terminates.
    + exact main_steps.
    + constructor.
Qed.

Theorem application_all_behaviors beh :
  program_behaves (Clight.semantics2 application) beh ->
  beh = Terminates (result_trace r) Int.zero.
Proof.
  eapply annotation_terminating_behavior_unique.
  - apply semantics2_determinate.
  - repeat constructor.
  - exact application_terminates.
Qed.

End Order.
