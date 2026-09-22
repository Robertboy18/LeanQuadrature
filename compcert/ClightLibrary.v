From Coq Require Import List ZArith.
From compcert Require Import Coqlib Maps Integers Floats Values AST Memory Events
  Globalenvs Ctypes Cop Clight ClightBigstep.
From QuadratureC Require Import quadrules ClightExample.

Import ListNotations.
Local Open Scope Z_scope.

(** The library uses only these symbols and function definitions. This context
    allows its execution proof to be instantiated after adding an application. *)
Definition library_symbols : list ident :=
  [_gauss_pts; _gauss_wts; _gauss_point; _gauss_weight;
   _testfun; _cos; _integrate; _integrate_testfun].

Definition library_functions : list ident :=
  [_gauss_point; _gauss_weight; _testfun; _integrate; _integrate_testfun].

Definition library_block (id : ident) : block :=
  match Genv.find_symbol ClightExample.ge id with
  | Some b => b | None => 1%positive
  end.

Record library_context := {
  context_program : Clight.program;
  context_memory : mem;
  context_symbols : forall id, In id library_symbols ->
    Genv.find_symbol (Clight.globalenv context_program) id =
      Genv.find_symbol ClightExample.ge id;
  context_functions : forall id, In id library_functions ->
    Genv.find_funct (Clight.globalenv context_program)
      (Vptr (library_block id) Ptrofs.zero) =
    Genv.find_funct ClightExample.ge (Vptr (library_block id) Ptrofs.zero);
  context_cosine : Clight.fundef;
  context_cosine_found :
    Genv.find_funct (Clight.globalenv context_program)
      (Vptr (library_block _cos) Ptrofs.zero) = Some context_cosine;
  context_cosine_type :
    type_of_fundef context_cosine =
      Tfunction [Tfloat F64 noattr] (Tfloat F64 noattr) cc_default;
  context_point_loads :
    Mem.load Mfloat64 context_memory points_block 8 = Some (Vfloat left_node) /\
    Mem.load Mfloat64 context_memory points_block 16 = Some (Vfloat right_node);
  context_weight_loads :
    Mem.load Mfloat64 context_memory weights_block 8 = Some (Vfloat one) /\
    Mem.load Mfloat64 context_memory weights_block 16 = Some (Vfloat one)
}.

Definition context_ge (ctx : library_context) := Clight.globalenv (context_program ctx).

Section LibraryExecution.
Variable ctx : library_context.

Ltac solve_context_symbol :=
  first [reflexivity |
    rewrite (context_symbols ctx) by (simpl; intuition congruence);
    vm_compute; reflexivity].

Ltac solve_context_function :=
  first
    [etransitivity; [apply (context_functions ctx _gauss_point); simpl; intuition congruence |]
    |etransitivity; [apply (context_functions ctx _gauss_weight); simpl; intuition congruence |]
    |etransitivity; [apply (context_functions ctx _testfun); simpl; intuition congruence |]
    |etransitivity; [apply (context_functions ctx _integrate); simpl; intuition congruence |]
    |etransitivity; [apply (context_functions ctx _integrate_testfun); simpl; intuition congruence |]];
  vm_compute; reflexivity.

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
      eapply eval_Eaddrof; eapply eval_Evar_global; solve_context_symbol
  | |- eval_expr _ _ _ _ (Evar _ _) _ =>
      eapply eval_Elvalue;
        [eapply eval_Evar_global; solve_context_symbol |
         apply deref_loc_reference; reflexivity]
  | |- eval_expr _ _ _ _ (Ederef _ _) _ =>
      eapply eval_Elvalue;
        [eapply eval_Ederef; eval_closed_expr |
         eapply deref_loc_value;
           [reflexivity |
            first [exact (proj1 (context_point_loads ctx)) | exact (proj2 (context_point_loads ctx)) |
              exact (proj1 (context_weight_loads ctx)) | exact (proj2 (context_weight_loads ctx))]]]
  end.

Ltac enter_closed_function :=
  eapply eval_funcall_internal with
    (e := empty_env) (m1 := (context_memory ctx)) (m2 := (context_memory ctx));
  [ eapply function_entry2_intro;
      [ vm_compute; repeat constructor; simpl; intuition congruence
      | vm_compute; repeat constructor; simpl; intuition congruence
      | vm_compute; intuition congruence
      | change (alloc_variables (context_ge ctx) empty_env (context_memory ctx) [] empty_env (context_memory ctx));
        constructor
      | vm_compute; reflexivity ]
  | cbn [f_gauss_point f_gauss_weight f_testfun f_integrate f_integrate_testfun fn_body]
  | idtac
  | reflexivity ].

Theorem gauss_point_left_execution :
  ClightBigstep.Clight2.eval_funcall (context_ge ctx) (context_memory ctx) (Internal f_gauss_point)
    [Vint (Int.repr 0); Vint (Int.repr 2)] E0 (context_memory ctx) (Vfloat left_node).
Proof.
  unfold ClightBigstep.Clight2.eval_funcall.
  enter_closed_function.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply exec_Sset. eval_closed_expr.
    + apply exec_Sreturn_some. eval_closed_expr.
  - split; [discriminate | reflexivity].
Qed.

Theorem gauss_point_right_execution :
  ClightBigstep.Clight2.eval_funcall (context_ge ctx) (context_memory ctx) (Internal f_gauss_point)
    [Vint (Int.repr 1); Vint (Int.repr 2)] E0 (context_memory ctx) (Vfloat right_node).
Proof.
  unfold ClightBigstep.Clight2.eval_funcall.
  enter_closed_function.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply exec_Sset. eval_closed_expr.
    + apply exec_Sreturn_some. eval_closed_expr.
  - split; [discriminate | reflexivity].
Qed.

Theorem gauss_weight_left_execution :
  ClightBigstep.Clight2.eval_funcall (context_ge ctx) (context_memory ctx) (Internal f_gauss_weight)
    [Vint (Int.repr 0); Vint (Int.repr 2)] E0 (context_memory ctx) (Vfloat one).
Proof.
  unfold ClightBigstep.Clight2.eval_funcall.
  enter_closed_function.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply exec_Sset. eval_closed_expr.
    + apply exec_Sreturn_some. eval_closed_expr.
  - split; [discriminate | reflexivity].
Qed.

Theorem gauss_weight_right_execution :
  ClightBigstep.Clight2.eval_funcall (context_ge ctx) (context_memory ctx) (Internal f_gauss_weight)
    [Vint (Int.repr 1); Vint (Int.repr 2)] E0 (context_memory ctx) (Vfloat one).
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

(** The same library proof supports either an external cosine contract or a
    proved internal implementation. Its actual function definition is part of
    the context, and each required call must be proved in that environment. *)
Hypothesis cosine_left :
  ClightBigstep.Clight2.eval_funcall (context_ge ctx) (context_memory ctx)
    (context_cosine ctx) [Vfloat left_node] E0 (context_memory ctx) (Vfloat cosine_value).
Hypothesis cosine_right :
  ClightBigstep.Clight2.eval_funcall (context_ge ctx) (context_memory ctx)
    (context_cosine ctx) [Vfloat right_node] E0 (context_memory ctx) (Vfloat cosine_value).

Ltac execute_cosine_call :=
  eapply exec_Scall with (f := context_cosine ctx);
    [reflexivity | eval_closed_expr | eval_closed_args |
     exact (context_cosine_found ctx) | exact (context_cosine_type ctx) |
     first [exact cosine_left | exact cosine_right]].

Theorem testfun_left_execution :
  ClightBigstep.Clight2.eval_funcall (context_ge ctx) (context_memory ctx) (Internal f_testfun)
    [Vfloat left_node] E0 (context_memory ctx) (Vfloat (callback left_node)).
Proof.
  unfold ClightBigstep.Clight2.eval_funcall.
  enter_closed_function.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + execute_cosine_call.
    + apply exec_Sreturn_some. eval_closed_expr.
  - split; [discriminate | reflexivity].
Qed.

Theorem testfun_right_execution :
  ClightBigstep.Clight2.eval_funcall (context_ge ctx) (context_memory ctx) (Internal f_testfun)
    [Vfloat right_node] E0 (context_memory ctx) (Vfloat (callback right_node)).
Proof.
  unfold ClightBigstep.Clight2.eval_funcall.
  enter_closed_function.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + execute_cosine_call.
    + apply exec_Sreturn_some. eval_closed_expr.
  - split; [discriminate | reflexivity].
Qed.

Ltac execute_proved_call :=
  eapply exec_Scall;
    [reflexivity | eval_closed_expr | eval_closed_args |
     solve_context_function | reflexivity |
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
  ClightBigstep.Clight2.eval_funcall (context_ge ctx) (context_memory ctx) (Internal f_integrate)
    [Vptr testfun_block Ptrofs.zero; Vint (Int.repr 2)]
    E0 (context_memory ctx) (Vfloat quadrature_value).
Proof.
  unfold ClightBigstep.Clight2.eval_funcall.
  enter_closed_function.
  - execute_closed_stmt (S (S O)).
  - split; [discriminate | reflexivity].
Qed.

Theorem integrate_testfun_execution :
  ClightBigstep.Clight2.eval_funcall (context_ge ctx) (context_memory ctx) (Internal f_integrate_testfun)
    [] E0 (context_memory ctx) (Vfloat cosine_value).
Proof.
  rewrite <- quadrature_value_exact.
  unfold ClightBigstep.Clight2.eval_funcall.
  enter_closed_function.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply exec_Scall;
        [reflexivity | eval_closed_expr | eval_closed_args |
         solve_context_function | reflexivity | exact integrate_execution].
    + apply exec_Sreturn_some. eval_closed_expr.
  - split; [discriminate | reflexivity].
Qed.

End LibraryExecution.

Print Assumptions integrate_testfun_execution.
