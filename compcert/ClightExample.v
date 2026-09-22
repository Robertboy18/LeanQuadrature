From Coq Require Import List ZArith.
From compcert Require Import Coqlib Maps Integers Floats Values AST Memory Events
  Globalenvs Ctypes Cop Clight ClightBigstep.
From QuadratureC Require Import quadrules.

Import ListNotations.
Local Open Scope Z_scope.

(** Concrete arithmetic in CompCert's floating-point semantics. *)
Definition left_node := Float.of_bits (Int64.repr 13826747565314421532).
Definition right_node := Float.of_bits (Int64.repr 4603375528459645724).
Definition cosine_value := Float.of_bits (Int64.repr 4605722458335229421).
Definition one := Float.of_bits (Int64.repr 4607182418800017408).
Definition half := Float.of_bits (Int64.repr 4602678819172646912).

Lemma int_one_float : Float.of_int (Int.repr 1) = one.
Proof.
  rewrite Float.of_int_from_words.
  match goal with |- ?x = _ => rewrite <- (Float.of_to_bits x) end.
  vm_compute. reflexivity.
Qed.

Definition callback (x : float) :=
  Float.mul (Float.mul half (Float.sub one x)) cosine_value.

Definition quadrature_value :=
  Float.add (Float.add Float.zero (Float.mul one (callback left_node)))
    (Float.mul one (callback right_node)).

Theorem quadrature_value_bits :
  Float.to_bits quadrature_value = Int64.repr 4605722458335229421.
Proof. vm_compute. reflexivity. Qed.

Theorem quadrature_value_exact : quadrature_value = cosine_value.
Proof.
  rewrite <- (Float.of_to_bits quadrature_value), quadrature_value_bits.
  reflexivity.
Qed.

Print Assumptions quadrature_value_bits.
Print Assumptions quadrature_value_exact.

(** The memory used below is the actual initialized memory of the pinned AST. *)
Definition ge := globalenv prog.

Lemma program_initializes : exists m, Genv.init_mem prog = Some m.
Proof.
  apply Genv.init_mem_exists.
  intros id v H.
  change (In (id, Gvar v) global_definitions) in H.
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

Definition initialized_memory : { m : mem | Genv.init_mem prog = Some m }.
Proof.
  destruct (Genv.init_mem prog) as [m |] eqn:H.
  - exists m. reflexivity.
  - exfalso. destruct program_initializes as [m Hm]. congruence.
Qed.

Definition initial_memory := proj1_sig initialized_memory.

Theorem initial_memory_exists : Genv.init_mem prog = Some initial_memory.
Proof. exact (proj2_sig initialized_memory). Qed.

Definition points_block :=
  match Genv.find_symbol ge _gauss_pts with Some b => b | None => 1%positive end.

Lemma points_block_info :
  Genv.find_var_info (Genv.globalenv prog) points_block = Some v_gauss_pts.
Proof. reflexivity. Qed.

Lemma point_loads :
  Mem.load Mfloat64 initial_memory points_block 8 = Some (Vfloat left_node) /\
  Mem.load Mfloat64 initial_memory points_block 16 = Some (Vfloat right_node).
Proof.
  pose proof (Genv.init_mem_characterization prog points_block
    points_block_info initial_memory_exists) as [_ [_ [H _]]].
  specialize (H eq_refl).
  cbn [Genv.load_store_init_data gvar_init] in H.
  exact (conj (proj1 (proj2 H)) (proj1 (proj2 (proj2 H)))).
Qed.

Definition weights_block :=
  match Genv.find_symbol ge _gauss_wts with Some b => b | None => 1%positive end.

Lemma weights_block_info :
  Genv.find_var_info (Genv.globalenv prog) weights_block = Some v_gauss_wts.
Proof. reflexivity. Qed.

Lemma weight_loads :
  Mem.load Mfloat64 initial_memory weights_block 8 = Some (Vfloat one) /\
  Mem.load Mfloat64 initial_memory weights_block 16 = Some (Vfloat one).
Proof.
  pose proof (Genv.init_mem_characterization prog weights_block
    weights_block_info initial_memory_exists) as [_ [_ [H _]]].
  specialize (H eq_refl).
  cbn [Genv.load_store_init_data gvar_init] in H.
  exact (conj (proj1 (proj2 H)) (proj1 (proj2 (proj2 H)))).
Qed.

(** Subsequent proofs use the initialization lemmas instead of reducing memory. *)
Local Opaque initial_memory.

Ltac solve_closed_operation :=
  lazymatch goal with
  | |- sem_binary_operation _ Osub (Vint ?i) _ (Vfloat ?x) _ _ = Some ?v =>
      change (Some (Vfloat (Float.sub (Float.of_int i) x)) = Some v);
      rewrite int_one_float; reflexivity
  | |- sem_binary_operation _ Omul (Vfloat ?x) _ (Vfloat ?y) _ _ = Some ?v =>
      change (Some (Vfloat (Float.mul x y)) = Some v); reflexivity
  | |- sem_binary_operation _ Oadd (Vfloat ?x) _ (Vfloat ?y) _ _ = Some ?v =>
      change (Some (Vfloat (Float.add x y)) = Some v); reflexivity
  | |- sem_cast (Vfloat ?x) _ _ _ = Some ?v =>
      change (Some (Vfloat x) = Some v); reflexivity
  | _ => vm_compute; reflexivity
  end.

Ltac eval_closed_expr :=
  lazymatch goal with
  | |- eval_expr _ _ _ _ (Econst_int _ _) _ => constructor
  | |- eval_expr _ _ _ _ (Econst_float _ _) _ => constructor
  | |- eval_expr _ _ _ _ (Etempvar _ _) _ =>
      apply eval_Etempvar; reflexivity
  | |- eval_expr _ _ _ _ (Ebinop _ _ _ _) _ =>
      eapply eval_Ebinop;
        [eval_closed_expr | eval_closed_expr | solve_closed_operation]
  | |- eval_expr _ _ _ _ (Eaddrof _ _) _ =>
      eapply eval_Eaddrof; eapply eval_Evar_global; vm_compute; reflexivity
  | |- eval_expr _ _ _ _ (Evar _ _) _ =>
      eapply eval_Elvalue;
        [eapply eval_Evar_global; vm_compute; reflexivity |
         apply deref_loc_reference; reflexivity]
  | |- eval_expr _ _ _ _ (Ederef _ _) _ =>
      eapply eval_Elvalue;
        [eapply eval_Ederef; eval_closed_expr |
         eapply deref_loc_value;
           [reflexivity |
            first [exact (proj1 point_loads) | exact (proj2 point_loads) |
              exact (proj1 weight_loads) | exact (proj2 weight_loads)]]]
  end.

Ltac enter_closed_function :=
  eapply eval_funcall_internal with
    (e := empty_env) (m1 := initial_memory) (m2 := initial_memory);
  [ eapply function_entry2_intro;
      [ vm_compute; repeat constructor; simpl; intuition congruence
      | vm_compute; repeat constructor; simpl; intuition congruence
      | vm_compute; intuition congruence
      | change (alloc_variables ge empty_env initial_memory [] empty_env initial_memory);
        constructor
      | vm_compute; reflexivity ]
  | cbn [f_gauss_point f_gauss_weight f_testfun f_integrate f_integrate_testfun fn_body]
  | idtac
  | reflexivity ].

Theorem gauss_point_left_execution :
  ClightBigstep.Clight2.eval_funcall ge initial_memory (Internal f_gauss_point)
    [Vint (Int.repr 0); Vint (Int.repr 2)] E0 initial_memory (Vfloat left_node).
Proof.
  unfold ClightBigstep.Clight2.eval_funcall.
  enter_closed_function.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply exec_Sset. eval_closed_expr.
    + apply exec_Sreturn_some. eval_closed_expr.
  - split; [discriminate | reflexivity].
Qed.

Theorem gauss_point_right_execution :
  ClightBigstep.Clight2.eval_funcall ge initial_memory (Internal f_gauss_point)
    [Vint (Int.repr 1); Vint (Int.repr 2)] E0 initial_memory (Vfloat right_node).
Proof.
  unfold ClightBigstep.Clight2.eval_funcall.
  enter_closed_function.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply exec_Sset. eval_closed_expr.
    + apply exec_Sreturn_some. eval_closed_expr.
  - split; [discriminate | reflexivity].
Qed.

Theorem gauss_weight_left_execution :
  ClightBigstep.Clight2.eval_funcall ge initial_memory (Internal f_gauss_weight)
    [Vint (Int.repr 0); Vint (Int.repr 2)] E0 initial_memory (Vfloat one).
Proof.
  unfold ClightBigstep.Clight2.eval_funcall.
  enter_closed_function.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply exec_Sset. eval_closed_expr.
    + apply exec_Sreturn_some. eval_closed_expr.
  - split; [discriminate | reflexivity].
Qed.

Theorem gauss_weight_right_execution :
  ClightBigstep.Clight2.eval_funcall ge initial_memory (Internal f_gauss_weight)
    [Vint (Int.repr 1); Vint (Int.repr 2)] E0 initial_memory (Vfloat one).
Proof.
  unfold ClightBigstep.Clight2.eval_funcall.
  enter_closed_function.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply exec_Sset. eval_closed_expr.
    + apply exec_Sreturn_some. eval_closed_expr.
  - split; [discriminate | reflexivity].
Qed.

Ltac eval_closed_args :=
  lazymatch goal with
  | |- eval_exprlist _ _ _ _ [] [] _ => constructor
  | |- eval_exprlist _ _ _ _ (_ :: _) (_ :: _) _ =>
      eapply eval_Econs;
        [eval_closed_expr | solve_closed_operation | eval_closed_args]
  end.

Definition cosine_external :=
  EF_external "cos"
    (mksignature [AST.Xfloat] AST.Xfloat cc_default).

(** These are contracts for the two external library calls, not a proof of libm. *)
Section ExternalCosine.
Hypothesis cosine_left :
  external_call cosine_external ge [Vfloat left_node] initial_memory
    E0 (Vfloat cosine_value) initial_memory.
Hypothesis cosine_right :
  external_call cosine_external ge [Vfloat right_node] initial_memory
    E0 (Vfloat cosine_value) initial_memory.

Ltac execute_cosine_call :=
  eapply exec_Scall;
    [reflexivity | eval_closed_expr | eval_closed_args |
     vm_compute; reflexivity | reflexivity |
     apply eval_funcall_external; first [exact cosine_left | exact cosine_right]].

Theorem testfun_left_execution :
  ClightBigstep.Clight2.eval_funcall ge initial_memory (Internal f_testfun)
    [Vfloat left_node] E0 initial_memory (Vfloat (callback left_node)).
Proof.
  unfold ClightBigstep.Clight2.eval_funcall.
  enter_closed_function.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + execute_cosine_call.
    + apply exec_Sreturn_some. eval_closed_expr.
  - split; [discriminate | reflexivity].
Qed.

Theorem testfun_right_execution :
  ClightBigstep.Clight2.eval_funcall ge initial_memory (Internal f_testfun)
    [Vfloat right_node] E0 initial_memory (Vfloat (callback right_node)).
Proof.
  unfold ClightBigstep.Clight2.eval_funcall.
  enter_closed_function.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + execute_cosine_call.
    + apply exec_Sreturn_some. eval_closed_expr.
  - split; [discriminate | reflexivity].
Qed.

Definition testfun_block :=
  match Genv.find_symbol ge _testfun with Some b => b | None => 1%positive end.

Ltac execute_proved_call :=
  eapply exec_Scall;
    [reflexivity | eval_closed_expr | eval_closed_args |
     vm_compute; reflexivity | reflexivity |
     first [exact gauss_point_left_execution |
       exact gauss_point_right_execution |
       exact gauss_weight_left_execution |
       exact gauss_weight_right_execution |
       exact testfun_left_execution |
       exact testfun_right_execution]].

(** The fuel counts loop iterations in this finite example; every step is
    justified by a constructor of CompCert's execution relation. *)
Ltac execute_closed_stmt fuel :=
  lazymatch goal with
  | |- exec_stmt _ _ _ _ _ Sskip _ _ _ _ => constructor
  | |- exec_stmt _ _ _ _ _ Sbreak _ _ _ _ => constructor
  | |- exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ =>
      eapply exec_Sset; eval_closed_expr
  | |- exec_stmt _ _ _ _ _ (Sreturn (Some _)) _ _ _ _ =>
      apply exec_Sreturn_some; eval_closed_expr
  | |- exec_stmt _ _ _ _ _ (Scall _ _ _) _ _ _ _ => execute_proved_call
  | |- exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ =>
      first
        [eapply exec_Sseq_1 with (t1 := E0) (t2 := E0);
          [execute_closed_stmt fuel | execute_closed_stmt fuel]
        |eapply exec_Sseq_2;
          [execute_closed_stmt fuel | discriminate]]
  | |- exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ =>
      eapply exec_Sifthenelse;
        [eval_closed_expr | vm_compute; reflexivity |
         cbn; execute_closed_stmt fuel]
  | |- exec_stmt _ _ _ _ _ (Sloop _ _) _ _ _ _ =>
      lazymatch fuel with
      | O => eapply exec_Sloop_stop1;
          [execute_closed_stmt fuel | constructor]
      | S ?remaining =>
          eapply exec_Sloop_loop with (t1 := E0) (t2 := E0) (t3 := E0);
            [execute_closed_stmt fuel | constructor |
             execute_closed_stmt fuel | execute_closed_stmt remaining]
      end
  end.

Theorem integrate_execution :
  ClightBigstep.Clight2.eval_funcall ge initial_memory (Internal f_integrate)
    [Vptr testfun_block Ptrofs.zero; Vint (Int.repr 2)]
    E0 initial_memory (Vfloat quadrature_value).
Proof.
  unfold ClightBigstep.Clight2.eval_funcall.
  enter_closed_function.
  - execute_closed_stmt (S (S O)).
  - split; [discriminate | reflexivity].
Qed.

Theorem integrate_testfun_execution :
  ClightBigstep.Clight2.eval_funcall ge initial_memory (Internal f_integrate_testfun)
    [] E0 initial_memory (Vfloat cosine_value).
Proof.
  rewrite <- quadrature_value_exact.
  unfold ClightBigstep.Clight2.eval_funcall.
  enter_closed_function.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply exec_Scall;
        [reflexivity | eval_closed_expr | eval_closed_args |
         vm_compute; reflexivity | reflexivity | exact integrate_execution].
    + apply exec_Sreturn_some. eval_closed_expr.
  - split; [discriminate | reflexivity].
Qed.

Theorem integrate_testfun_execution_bits :
  exists value,
    ClightBigstep.Clight2.eval_funcall ge initial_memory
      (Internal f_integrate_testfun) [] E0 initial_memory (Vfloat value) /\
    Float.to_bits value = Int64.repr 4605722458335229421.
Proof.
  exists cosine_value. split.
  - exact integrate_testfun_execution.
  - apply Float.to_of_bits.
Qed.

Theorem integrate_testfun_steps (k : cont) (hk : is_call_cont k) :
  Smallstep.star Clight.step2 ge
    (Callstate (Internal f_integrate_testfun) [] k initial_memory)
    E0 (Returnstate (Vfloat cosine_value) k initial_memory).
Proof.
  eapply (ClightBigstep.eval_funcall_steps function_entry2 prog).
  - exact integrate_testfun_execution.
  - exact hk.
Qed.

End ExternalCosine.

Check integrate_testfun_execution_bits.
Print Assumptions initial_memory_exists.
Print Assumptions gauss_point_left_execution.
Print Assumptions testfun_left_execution.
Print Assumptions integrate_testfun_execution_bits.
Print Assumptions integrate_testfun_steps.
