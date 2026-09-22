From Coq Require Import List ZArith Lia.
From compcert Require Import Coqlib Maps Integers Floats Values AST Memory Events
  Globalenvs Ctypes Cop Clight ClightBigstep.
From QuadratureC Require Import quadrules ClightExample.

Import ListNotations.
Local Open Scope Z_scope.

(** Read the tables from the pinned initializer, including its three-point weight. *)
Definition initializer_float (d : init_data) : float :=
  match d with Init_float64 f => f | _ => Float.zero end.
Definition nodes := map initializer_float (gvar_init v_gauss_pts).
Definition weights := map initializer_float (gvar_init v_gauss_wts).

Lemma nodes_initializer : map Init_float64 nodes = gvar_init v_gauss_pts.
Proof. reflexivity. Qed.

Lemma weights_initializer : map Init_float64 weights = gvar_init v_gauss_wts.
Proof. reflexivity. Qed.

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
  pose proof (Genv.init_mem_characterization prog points_block
    points_block_info initial_memory_exists) as [_ [_ [H _]]].
  specialize (H eq_refl).
  rewrite <- nodes_initializer in H.
  exact (load_float_table_nth nodes points_block 0 i H hi).
Qed.

Theorem weight_table_load i (hi : (i < 55)%nat) :
  Mem.load Mfloat64 initial_memory weights_block (8 * Z.of_nat i) =
    Some (Vfloat (nth i weights Float.zero)).
Proof.
  pose proof (Genv.init_mem_characterization prog weights_block
    weights_block_info initial_memory_exists) as [_ [_ [H _]]].
  specialize (H eq_refl).
  rewrite <- weights_initializer in H.
  exact (load_float_table_nth weights weights_block 0 i H hi).
Qed.

Inductive rule_order := One | Two | Three | Four.
Definition rule_size (r : rule_order) : nat :=
  match r with One => 1 | Two => 2 | Three => 3 | Four => 4 end.
Definition table_index (r : rule_order) (i : nat) : nat :=
  rule_size r * (rule_size r - 1) / 2 + i.
Definition rule_node r i := nth (table_index r i) nodes Float.zero.
Definition rule_weight r i := nth (table_index r i) weights Float.zero.
Definition rule_terms r : list (float * float) :=
  map (fun i => (rule_weight r i, rule_node r i)) (seq 0 (rule_size r)).

(** A functional specification in CompCert's own floating-point operations. *)
Definition rule_value (f : float -> float) r :=
  fold_left (fun acc term => Float.add acc (Float.mul (fst term) (f (snd term))))
    (rule_terms r) Float.zero.

Local Opaque initial_memory.

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
      eapply eval_Eaddrof; eapply eval_Evar_global; vm_compute; reflexivity
  | |- eval_expr _ _ _ _ (Evar _ _) _ =>
      eapply eval_Elvalue;
        [eapply eval_Evar_global; vm_compute; reflexivity |
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
  enter_closed_function;
  [eapply exec_Sseq_1 with (t1 := E0) (t2 := E0);
    [eapply exec_Sset; eval_rule_expr |
     apply exec_Sreturn_some; eval_rule_expr] |
   split; [discriminate | reflexivity]].

Theorem gauss_point_execution r i (hi : (i < rule_size r)%nat) :
  ClightBigstep.Clight2.eval_funcall ge initial_memory (Internal f_gauss_point)
    [Vint (Int.repr (Z.of_nat i)); Vint (Int.repr (Z.of_nat (rule_size r)))]
    E0 initial_memory (Vfloat (rule_node r i)).
Proof.
  destruct r; cbn [rule_size] in hi; enumerate_index i.
  all: prove_accessor.
Qed.

Theorem gauss_weight_execution r i (hi : (i < rule_size r)%nat) :
  ClightBigstep.Clight2.eval_funcall ge initial_memory (Internal f_gauss_weight)
    [Vint (Int.repr (Z.of_nat i)); Vint (Int.repr (Z.of_nat (rule_size r)))]
    E0 initial_memory (Vfloat (rule_weight r i)).
Proof.
  destruct r; cbn [rule_size] in hi; enumerate_index i.
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

Ltac apply_accessor_contract :=
  let order := lazymatch type of callback_contract with
    | forall i : nat, (i < rule_size ?order)%nat -> _ => constr:(order)
    end in
  lazymatch goal with
  | |- ClightBigstep.eval_funcall _ _ _ _ [Vint ?iv; Vint _] _ _ _ =>
      let i := eval vm_compute in (Z.to_nat (Int.unsigned iv)) in
      first [exact (gauss_point_execution order i (ltac:(cbn [rule_size]; lia))) |
             exact (gauss_weight_execution order i (ltac:(cbn [rule_size]; lia)))]
  end.

Ltac apply_callback_contract :=
  first [apply (callback_contract 0%nat); cbn [rule_size]; lia |
         apply (callback_contract 1%nat); cbn [rule_size]; lia |
         apply (callback_contract 2%nat); cbn [rule_size]; lia |
         apply (callback_contract 3%nat); cbn [rule_size]; lia].

Ltac execute_rule_call :=
  eapply exec_Scall;
    [reflexivity | eval_rule_expr | eval_rule_args |
     first [exact callback_found | vm_compute; reflexivity] |
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
Theorem integrate_rule_execution :
  ClightBigstep.Clight2.eval_funcall ge initial_memory (Internal f_integrate)
    [Vptr b Ptrofs.zero; Vint (Int.repr (Z.of_nat (rule_size r)))]
    E0 initial_memory (Vfloat (rule_value f r)).
Proof.
  destruct r.
  all: unfold ClightBigstep.Clight2.eval_funcall.
  all: enter_closed_function;
    [execute_rule_stmt (S (S (S (S O)))) |
     split; [discriminate | reflexivity]].
Qed.

Theorem integrate_rule_steps (k : cont) (hk : is_call_cont k) :
  Smallstep.star Clight.step2 ge
    (Callstate (Internal f_integrate)
      [Vptr b Ptrofs.zero; Vint (Int.repr (Z.of_nat (rule_size r)))]
      k initial_memory)
    E0 (Returnstate (Vfloat (rule_value f r)) k initial_memory).
Proof.
  eapply (ClightBigstep.eval_funcall_steps function_entry2 prog).
  - exact integrate_rule_execution.
  - exact hk.
Qed.

End Callback.

Print Assumptions gauss_point_execution.
Print Assumptions gauss_weight_execution.
Check integrate_rule_execution.
Print Assumptions integrate_rule_execution.
Print Assumptions integrate_rule_steps.
