From Coq Require Import List ZArith Lia.
From compcert Require Import Coqlib Maps Integers Floats Values AST Memory Events
  Globalenvs Ctypes Cop Clight ClightBigstep.
From QuadratureC Require Import quadrules ClightExample ClightRules StoredRules.

Import ListNotations.
Local Open Scope Z_scope.
Module RuleLibrary.

Definition library_symbols : list ident :=
  [_gauss_pts; _gauss_wts; _gauss_point; _gauss_weight].
Definition library_block id :=
  match Genv.find_symbol ClightExample.ge id with
  | Some b => b | None => 1%positive
  end.

(** A program may add an entry point or replace a callback while retaining the
    initialized quadrature tables and accessor functions.  These local context
    conditions are sufficient for every stored slice of at most ten nodes. *)
Record context := {
  context_program : Clight.program;
  context_memory : mem;
  context_initializes : Genv.init_mem context_program = Some context_memory;
  context_symbols : forall id, In id library_symbols ->
    Genv.find_symbol (Clight.globalenv context_program) id =
      Genv.find_symbol ClightExample.ge id;
  context_points : Genv.find_var_info (Genv.globalenv context_program) points_block =
    Some v_gauss_pts;
  context_weights : Genv.find_var_info (Genv.globalenv context_program) weights_block =
    Some v_gauss_wts;
  context_point_function :
    Genv.find_funct (Clight.globalenv context_program)
      (Vptr (library_block _gauss_point) Ptrofs.zero) = Some (Internal f_gauss_point);
  context_weight_function :
    Genv.find_funct (Clight.globalenv context_program)
      (Vptr (library_block _gauss_weight) Ptrofs.zero) = Some (Internal f_gauss_weight)
}.

Section Execution.
Variable ctx : context.
Let ge := Clight.globalenv (context_program ctx).
Let initial_memory := context_memory ctx.

Lemma load_float_table_nth fs b ofs i :
  Genv.load_store_init_data ge initial_memory b ofs (map Init_float64 fs) ->
  (i < length fs)%nat ->
  Mem.load Mfloat64 initial_memory b (ofs + 8 * Z.of_nat i) =
    Some (Vfloat (nth i fs Float.zero)).
Proof.
  revert ofs i. induction fs as [| x xs IH]; intros ofs i HL HI.
  - simpl in HI. lia.
  - cbn [map Genv.load_store_init_data init_data_size] in HL.
    destruct HL as [HX HXS]. destruct i as [| i].
    + replace (ofs + 8 * Z.of_nat 0) with ofs by lia. exact HX.
    + replace (ofs + 8 * Z.of_nat (S i)) with ((ofs + 8) + 8 * Z.of_nat i) by lia.
      apply IH; [exact HXS | simpl in HI; lia].
Qed.

Theorem point_table_load i (hi : (i < 55)%nat) :
  Mem.load Mfloat64 initial_memory points_block (8 * Z.of_nat i) =
    Some (Vfloat (nth i nodes Float.zero)).
Proof.
  pose proof (Genv.init_mem_characterization (context_program ctx) points_block
    (context_points ctx) (context_initializes ctx)) as [_ [_ [H _]]].
  specialize (H eq_refl).
  rewrite <- nodes_initializer in H.
  exact (load_float_table_nth nodes points_block 0 i H hi).
Qed.

Theorem weight_table_load i (hi : (i < 55)%nat) :
  Mem.load Mfloat64 initial_memory weights_block (8 * Z.of_nat i) =
    Some (Vfloat (nth i weights Float.zero)).
Proof.
  pose proof (Genv.init_mem_characterization (context_program ctx) weights_block
    (context_weights ctx) (context_initializes ctx)) as [_ [_ [H _]]].
  specialize (H eq_refl).
  rewrite <- weights_initializer in H.
  exact (load_float_table_nth weights weights_block 0 i H hi).
Qed.

Ltac solve_rule_symbol :=
  first [reflexivity |
    unfold ge; rewrite (context_symbols ctx) by (simpl; intuition congruence);
    vm_compute; reflexivity].

Ltac enter_rule_function :=
  eapply eval_funcall_internal with
    (e := empty_env) (m1 := initial_memory) (m2 := initial_memory);
  [ eapply function_entry2_intro;
      [ vm_compute; repeat constructor; simpl; intuition congruence
      | vm_compute; repeat constructor; simpl; intuition congruence
      | vm_compute; intuition congruence
      | change (alloc_variables ge empty_env initial_memory [] empty_env initial_memory);
        constructor
      | vm_compute; reflexivity ]
  | cbn [f_gauss_point f_gauss_weight f_integrate fn_body]
  | idtac
  | reflexivity ].

Ltac load_initialized_table :=
  cbn [Mem.loadv];
  lazymatch goal with
  | |- Mem.load Mfloat64 initial_memory ?b ?ofs = _ =>
      let i := eval vm_compute in (Z.to_nat (ofs / 8)) in
      first [exact (point_table_load i (ltac:(lia))) |
             exact (weight_table_load i (ltac:(lia)))]
  end.

Ltac eval_rule_expr :=
  lazymatch goal with
  | |- eval_expr _ _ _ _ (Econst_int _ _) _ => constructor
  | |- eval_expr _ _ _ _ (Econst_float _ _) _ => constructor
  | |- eval_expr _ _ _ _ (Etempvar _ _) _ =>
      apply eval_Etempvar; reflexivity
  | |- eval_expr _ _ _ _ (Ebinop _ _ _ _) _ =>
      eapply eval_Ebinop;
        [eval_rule_expr | eval_rule_expr | solve_closed_operation]
  | |- eval_expr _ _ _ _ (Eaddrof _ _) _ =>
      eapply eval_Eaddrof; eapply eval_Evar_global; solve_rule_symbol
  | |- eval_expr _ _ _ _ (Evar _ _) _ =>
      eapply eval_Elvalue;
        [eapply eval_Evar_global; solve_rule_symbol |
         apply deref_loc_reference; reflexivity]
  | |- eval_expr _ _ _ _ (Ederef _ _) _ =>
      eapply eval_Elvalue;
        [eapply eval_Ederef; eval_rule_expr |
         eapply deref_loc_value; [reflexivity | load_initialized_table]]
  end.

Ltac enumerate_index i :=
  first [lia | destruct i as [| i]; [idtac | enumerate_index i]].

Ltac prove_accessor :=
  unfold ClightBigstep.Clight2.eval_funcall;
  once enter_rule_function;
  [eapply exec_Sseq_1 with (t1 := E0) (t2 := E0);
    [eapply exec_Sset; eval_rule_expr |
     apply exec_Sreturn_some; eval_rule_expr] |
   split; [discriminate | reflexivity]].

Theorem stored_gauss_point_execution n (hn : (n <= 10)%nat) i (hi : (i < n)%nat) :
  ClightBigstep.Clight2.eval_funcall ge initial_memory (Internal f_gauss_point)
    [Vint (Int.repr (Z.of_nat i)); Vint (Int.repr (Z.of_nat (n)))]
    E0 initial_memory (Vfloat (stored_node n i)).
Proof.
  enumerate_index n; enumerate_index i.
  all: prove_accessor.
Qed.

Theorem stored_gauss_weight_execution n (hn : (n <= 10)%nat) i (hi : (i < n)%nat) :
  ClightBigstep.Clight2.eval_funcall ge initial_memory (Internal f_gauss_weight)
    [Vint (Int.repr (Z.of_nat i)); Vint (Int.repr (Z.of_nat (n)))]
    E0 initial_memory (Vfloat (stored_weight n i)).
Proof.
  enumerate_index n; enumerate_index i.
  all: prove_accessor.
Qed.

Ltac eval_rule_args :=
  lazymatch goal with
  | |- eval_exprlist _ _ _ _ [] [] _ => constructor
  | |- eval_exprlist _ _ _ _ (_ :: _) (_ :: _) _ =>
      eapply eval_Econs;
        [eval_rule_expr | solve_closed_operation | eval_rule_args]
  end.

Section Callback.

Variable n : nat.
Hypothesis order_bound : (n <= 10)%nat.
Variable f : float -> float.
Variable b : block.
Variable fd : Clight.fundef.

Hypothesis callback_found : Genv.find_funct ge (Vptr b Ptrofs.zero) = Some fd.
Hypothesis callback_type :
  type_of_fundef fd = Tfunction [Tfloat F64 noattr] (Tfloat F64 noattr) cc_default.
Hypothesis callback_contract :
  forall i, (i < n)%nat ->
    ClightBigstep.Clight2.eval_funcall ge initial_memory fd
      [Vfloat (stored_node n i)] E0 initial_memory (Vfloat (f (stored_node n i))).

Ltac apply_accessor_contract :=
  let order := lazymatch type of callback_contract with
    | forall i : nat, (i < ?order)%nat -> _ => constr:(order)
    end in
  lazymatch goal with
  | |- ClightBigstep.eval_funcall _ _ _ _ [Vint ?iv; Vint _] _ _ _ =>
      let i := eval vm_compute in (Z.to_nat (Int.unsigned iv)) in
      first [exact (stored_gauss_point_execution order (ltac:(lia)) i (ltac:(lia))) |
             exact (stored_gauss_weight_execution order (ltac:(lia)) i (ltac:(lia)))]
  end.

Ltac apply_callback_contract :=
  first [apply (callback_contract 0%nat); cbn [rule_size]; lia |
         apply (callback_contract 1%nat); cbn [rule_size]; lia |
         apply (callback_contract 2%nat); cbn [rule_size]; lia |
         apply (callback_contract 3%nat); lia |
         apply (callback_contract 4%nat); lia |
         apply (callback_contract 5%nat); lia |
         apply (callback_contract 6%nat); lia |
         apply (callback_contract 7%nat); lia |
         apply (callback_contract 8%nat); lia |
         apply (callback_contract 9%nat); lia].

Ltac execute_rule_call :=
  eapply exec_Scall;
    [reflexivity | eval_rule_expr | eval_rule_args |
     first [exact callback_found | exact (context_point_function ctx) |
       exact (context_weight_function ctx)] |
     first [exact callback_type | reflexivity] |
     first [apply_accessor_contract | apply_callback_contract]].

Ltac execute_rule_stmt fuel :=
  lazymatch goal with
  | |- exec_stmt _ _ _ _ _ Sskip _ _ _ _ => constructor
  | |- exec_stmt _ _ _ _ _ Sbreak _ _ _ _ => constructor
  | |- exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _ =>
      eapply exec_Sset; eval_rule_expr
  | |- exec_stmt _ _ _ _ _ (Sreturn (Some _)) _ _ _ _ =>
      apply exec_Sreturn_some; eval_rule_expr
  | |- exec_stmt _ _ _ _ _ (Scall _ _ _) _ _ _ _ => execute_rule_call
  | |- exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _ =>
      first
        [eapply exec_Sseq_1 with (t1 := E0) (t2 := E0);
          [execute_rule_stmt fuel | execute_rule_stmt fuel]
        |eapply exec_Sseq_2;
          [execute_rule_stmt fuel | discriminate]]
  | |- exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ =>
      eapply exec_Sifthenelse;
        [eval_rule_expr | vm_compute; reflexivity |
         cbn; execute_rule_stmt fuel]
  | |- exec_stmt _ _ _ _ _ (Sloop _ _) _ _ _ _ =>
      first
        [eapply exec_Sloop_stop1;
          [execute_rule_stmt fuel | constructor]
        |lazymatch fuel with
         | S ?remaining =>
             eapply exec_Sloop_loop with (t1 := E0) (t2 := E0) (t3 := E0);
               [execute_rule_stmt fuel | constructor |
                execute_rule_stmt fuel | execute_rule_stmt remaining]
         end]
  end.

(** Each callback is supplied independently; the theorem proves all table
    accesses, loop control, and rounded multiplication and accumulation. *)
Theorem stored_integrate_execution :
  ClightBigstep.Clight2.eval_funcall ge initial_memory (Internal f_integrate)
    [Vptr b Ptrofs.zero; Vint (Int.repr (Z.of_nat (n)))]
    E0 initial_memory (Vfloat (stored_value f n)).
Proof.
  assert (Hcases : n = 0%nat \/ n = 1%nat \/ n = 2%nat \/ n = 3%nat \/ n = 4%nat \/ n = 5%nat \/ n = 6%nat \/ n = 7%nat \/ n = 8%nat \/ n = 9%nat \/ n = 10%nat) by lia.
  repeat match type of Hcases with
  | _ \/ _ => destruct Hcases as [Hcases | Hcases]
  end; subst n.
  all: unfold ClightBigstep.Clight2.eval_funcall.
  all: enter_rule_function;
    [execute_rule_stmt (S (S (S (S (S (S (S (S (S (S O)))))))))) |
     split; [discriminate | reflexivity]].
Qed.

Theorem stored_integrate_steps (k : cont) (hk : is_call_cont k) :
  Smallstep.star Clight.step2 ge
    (Callstate (Internal f_integrate)
      [Vptr b Ptrofs.zero; Vint (Int.repr (Z.of_nat (n)))]
      k initial_memory)
    E0 (Returnstate (Vfloat (stored_value f n)) k initial_memory).
Proof.
  eapply (ClightBigstep.eval_funcall_steps function_entry2 (context_program ctx)).
  - exact stored_integrate_execution.
  - exact hk.
Qed.

End Callback.

(** The previous four-order interface is an instance of the stored-table proof. *)
Theorem gauss_point_execution r i (hi : (i < rule_size r)%nat) :
  ClightBigstep.Clight2.eval_funcall ge initial_memory (Internal f_gauss_point)
    [Vint (Int.repr (Z.of_nat i)); Vint (Int.repr (Z.of_nat (rule_size r)))]
    E0 initial_memory (Vfloat (rule_node r i)).
Proof.
  exact (stored_gauss_point_execution (rule_size r)
    (ltac:(destruct r; cbn [rule_size]; lia)) i hi).
Qed.

Theorem gauss_weight_execution r i (hi : (i < rule_size r)%nat) :
  ClightBigstep.Clight2.eval_funcall ge initial_memory (Internal f_gauss_weight)
    [Vint (Int.repr (Z.of_nat i)); Vint (Int.repr (Z.of_nat (rule_size r)))]
    E0 initial_memory (Vfloat (rule_weight r i)).
Proof.
  exact (stored_gauss_weight_execution (rule_size r)
    (ltac:(destruct r; cbn [rule_size]; lia)) i hi).
Qed.

Section RuleOrder.
Variable r : rule_order.
Variable f : float -> float.
Variable b : block.
Variable fd : Clight.fundef.
Hypothesis callback_found : Genv.find_funct ge (Vptr b Ptrofs.zero) = Some fd.
Hypothesis callback_type :
  type_of_fundef fd = Tfunction [Tfloat F64 noattr] (Tfloat F64 noattr) cc_default.
Hypothesis callback_contract :
  forall i, (i < rule_size r)%nat ->
    ClightBigstep.Clight2.eval_funcall ge initial_memory fd
      [Vfloat (rule_node r i)] E0 initial_memory (Vfloat (f (rule_node r i))).

Theorem integrate_rule_execution :
  ClightBigstep.Clight2.eval_funcall ge initial_memory (Internal f_integrate)
    [Vptr b Ptrofs.zero; Vint (Int.repr (Z.of_nat (rule_size r)))]
    E0 initial_memory (Vfloat (rule_value f r)).
Proof.
  exact (stored_integrate_execution (rule_size r)
    (ltac:(destruct r; cbn [rule_size]; lia)) f b fd
    callback_found callback_type callback_contract).
Qed.

Theorem integrate_rule_steps (k : cont) (hk : is_call_cont k) :
  Smallstep.star Clight.step2 ge
    (Callstate (Internal f_integrate)
      [Vptr b Ptrofs.zero; Vint (Int.repr (Z.of_nat (rule_size r)))]
      k initial_memory)
    E0 (Returnstate (Vfloat (rule_value f r)) k initial_memory).
Proof.
  eapply (ClightBigstep.eval_funcall_steps function_entry2 (context_program ctx)).
  - exact integrate_rule_execution.
  - exact hk.
Qed.
End RuleOrder.

End Execution.
End RuleLibrary.
