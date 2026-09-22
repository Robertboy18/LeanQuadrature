From Coq Require Import Reals List ZArith Lia.
From compcert Require Import Integers Floats Values AST Memory Events
  Globalenvs Ctypes Clight ClightBigstep Smallstep.
From QuadratureC Require Import quadrules ClightExample ClightRules
  ClightDeterminism ClightSafety FiniteArithmetic.

Import ListNotations Binary64Roundoff.
Local Open Scope R_scope.
Local Transparent Float.zero.

(** These are the weights in the initialized C table, including the distinct
    three-point literal discussed in the paper assessment. *)
Lemma rule_weight_finite r i (HI : (i < rule_size r)%nat) :
  finite (rule_weight r i).
Proof.
  destruct r; cbn [rule_size] in HI; enumerate_index i.
  all: vm_compute; reflexivity.
Qed.

Lemma rule_terms_length r : length (rule_terms r) = rule_size r.
Proof. unfold rule_terms. rewrite map_length, seq_length. reflexivity. Qed.

Lemma rule_terms_finite f r :
  (forall i, (i < rule_size r)%nat -> finite (f (rule_node r i))) ->
  forall t, In t (rule_terms r) -> finite (fst t) /\ finite (f (snd t)).
Proof.
  intros HF t HT. apply in_map_iff in HT.
  destruct HT as [i [<- HI]]. apply in_seq in HI.
  cbn [fst snd]. split; [apply rule_weight_finite | apply HF]; lia.
Qed.

Theorem rule_value_bounded radius f r :
  radius <= max_value ->
  (forall i, (i < rule_size r)%nat -> finite (f (rule_node r i))) ->
  product_mass f (rule_terms r) + 2 * INR (rule_size r) * epsilon radius <= radius ->
  finite_steps f (rule_terms r) Float.zero /\
  finite (rule_value f r) /\
  real (rule_value f r) = rounded_sum f (rule_terms r) 0 /\
  Rabs (real (rule_value f r) - exact_sum f (rule_terms r)) <=
    2 * INR (rule_size r) * epsilon radius.
Proof.
  intros HM HF HB.
  assert (HZ : finite Float.zero) by reflexivity.
  assert (HB' : Rabs (real Float.zero) + product_mass f (rule_terms r) +
      2 * INR (length (rule_terms r)) * epsilon radius <= radius).
  { change (real Float.zero) with 0. rewrite Rabs_R0, Rplus_0_l, rule_terms_length.
    exact HB. }
  pose proof (integrate_bounded radius f (rule_terms r) Float.zero HM HZ
    (rule_terms_finite f r HF) HB') as H.
  change (real Float.zero) with 0 in H.
  rewrite Rplus_0_l, rule_terms_length in H. exact H.
Qed.

Section Callback.

Variable r : rule_order.
Variable f : Floats.float -> Floats.float.
Variable b : block.
Variable fd : Clight.fundef.

Hypothesis callback_found : Genv.find_funct ge (Vptr b Ptrofs.zero) = Some fd.
Hypothesis callback_type :
  type_of_fundef fd = Tfunction [Tfloat F64 noattr] (Tfloat F64 noattr) cc_default.
Hypothesis callback_contract :
  forall i, (i < rule_size r)%nat ->
    ClightBigstep.Clight2.eval_funcall ge initial_memory fd
      [Vfloat (rule_node r i)] E0 initial_memory (Vfloat (f (rule_node r i))).

Theorem integrate_rule_numeric_correct radius :
  radius <= max_value ->
  (forall i, (i < rule_size r)%nat -> finite (f (rule_node r i))) ->
  product_mass f (rule_terms r) + 2 * INR (rule_size r) * epsilon radius <= radius ->
  total_call_correct ge
    (Callstate (Internal f_integrate)
      [Vptr b Ptrofs.zero; Vint (Int.repr (Z.of_nat (rule_size r)))]
      Kstop initial_memory)
    (Vfloat (rule_value f r)) initial_memory /\
  finite_steps f (rule_terms r) Float.zero /\
  finite (rule_value f r) /\
  real (rule_value f r) = rounded_sum f (rule_terms r) 0 /\
  Rabs (real (rule_value f r) - exact_sum f (rule_terms r)) <=
    2 * INR (rule_size r) * epsilon radius.
Proof.
  intros HM HF HB. split.
  - exact (integrate_rule_total_correct r f b fd
      callback_found callback_type callback_contract).
  - exact (rule_value_bounded radius f r HM HF HB).
Qed.

(** The bound applies to every return of the C call. Its error is measured
    against the exact sum of stored weights and decoded callback outputs;
    table perturbations and the analytic quadrature remainder are separate. *)
Theorem integrate_rule_all_returns_roundoff radius t value m :
  radius <= max_value ->
  (forall i, (i < rule_size r)%nat -> finite (f (rule_node r i))) ->
  product_mass f (rule_terms r) + 2 * INR (rule_size r) * epsilon radius <= radius ->
  star Clight.step2 ge
    (Callstate (Internal f_integrate)
      [Vptr b Ptrofs.zero; Vint (Int.repr (Z.of_nat (rule_size r)))]
      Kstop initial_memory)
    t (Returnstate (Vfloat value) Kstop m) ->
  t = E0 /\ m = initial_memory /\ finite value /\
  real value = rounded_sum f (rule_terms r) 0 /\
  Rabs (real value - exact_sum f (rule_terms r)) <=
    2 * INR (rule_size r) * epsilon radius.
Proof.
  intros HM HF HB RUN.
  destruct (integrate_rule_numeric_correct radius HM HF HB)
    as [HTOTAL [_ [HFIN [HREAL HERR]]]].
  destruct (call_unique_return _ _ _ _ HTOTAL _ _ _ RUN) as [HT [HV HMEM]].
  inversion HV; subst. auto.
Qed.

End Callback.
