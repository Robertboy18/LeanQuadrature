From Coq Require Import Reals List Lia Psatz.
From Coquelicot Require Import Coquelicot.
From QuadratureC Require Import ClightRules TableAccuracy CallbackAccuracy.

Import ListNotations Binary64TableAccuracy Binary64CallbackAccuracy.
Local Open Scope R_scope.

Module GaussianPolynomialAccuracy.

Definition polynomial (c : nat -> R) (degree : nat) (x : R) :=
  sum_f_R0 (fun k => c k * x ^ k) degree.

Lemma ideal_value_plus g h r :
  ideal_value (fun x => g x + h x) r = ideal_value g r + ideal_value h r.
Proof.
  unfold ideal_value. induction (seq 0 (rule_size r)); cbn [fold_right];
    [ring | rewrite IHl; ring].
Qed.

Lemma ideal_value_scal c g r :
  ideal_value (fun x => c * g x) r = c * ideal_value g r.
Proof.
  unfold ideal_value. induction (seq 0 (rule_size r)); cbn [fold_right];
    [ring | rewrite IHl; ring].
Qed.

Lemma ideal_value_uniform_error g h r error :
  (forall x, -1 <= x <= 1 -> Rabs (g x - h x) <= error) ->
  Rabs (ideal_value g r - ideal_value h r) <= 2 * error.
Proof.
  intros H. unfold ideal_value.
  change (Rabs (sum_on (seq 0 (rule_size r))
    (fun i => ideal_weight r i * g (ideal_node r i)) -
    sum_on (seq 0 (rule_size r))
    (fun i => ideal_weight r i * h (ideal_node r i))) <= 2 * error).
  eapply Rle_trans; [apply sum_on_abs_sub |].
  eapply Rle_trans with (r2 := sum_on (seq 0 (rule_size r))
    (fun i => ideal_weight r i * error)).
  - apply sum_on_le. intros i HI. apply in_seq in HI.
    assert (HIB : (i < rule_size r)%nat) by lia.
    replace (ideal_weight r i * g (ideal_node r i) -
      ideal_weight r i * h (ideal_node r i)) with
      (ideal_weight r i * (g (ideal_node r i) - h (ideal_node r i))) by ring.
    rewrite Rabs_mult, Rabs_pos_eq by (pose proof (ideal_weight_positive r i HIB); lra).
    apply Rmult_le_compat_l.
    + pose proof (ideal_weight_positive r i HIB). lra.
    + apply H, ideal_node_interval, HIB.
  - rewrite sum_on_mul. unfold sum_on. rewrite ideal_weights_sum. lra.
Qed.

Lemma power_integrable k a b : ex_RInt (fun x => x ^ k) a b.
Proof. eexists. apply is_RInt_pow. Qed.

Lemma power_integral k a b :
  RInt (fun x => x ^ k) a b = b ^ S k / INR (S k) - a ^ S k / INR (S k).
Proof. apply is_RInt_unique, is_RInt_pow. Qed.

Lemma ideal_power_integral r k (HK : (k < 2 * rule_size r)%nat) :
  ideal_value (fun x => x ^ k) r = RInt (fun x => x ^ k) (-1) 1.
Proof.
  rewrite (ideal_moment r k HK), power_integral.
  assert (HK8 : (k < 8)%nat) by (destruct r; cbn [rule_size] in HK; lia).
  clear HK. enumerate_index k.
  all: cbn [Nat.even INR pow]; field.
Qed.

Lemma polynomial_integrable c degree a b : ex_RInt (polynomial c degree) a b.
Proof.
  induction degree.
  - change (ex_RInt (fun x => c O * x ^ O) a b).
    apply (@ex_RInt_scal R_NormedModule), power_integrable.
  - change (ex_RInt (fun x => polynomial c degree x + c (S degree) * x ^ S degree) a b).
    apply (@ex_RInt_plus R_NormedModule); [exact IHdegree | apply (@ex_RInt_scal R_NormedModule), power_integrable].
Qed.

Lemma real_integral_plus (f g : R -> R) a b :
  ex_RInt f a b -> ex_RInt g a b ->
  RInt (fun x => f x + g x) a b = RInt f a b + RInt g a b.
Proof. exact (@RInt_plus R_CompleteNormedModule f g a b). Qed.

Lemma real_integral_minus (f g : R -> R) a b :
  ex_RInt f a b -> ex_RInt g a b ->
  RInt (fun x => f x - g x) a b = RInt f a b - RInt g a b.
Proof. exact (@RInt_minus R_CompleteNormedModule f g a b). Qed.

Lemma real_integral_scal c (f : R -> R) a b :
  ex_RInt f a b -> RInt (fun x => c * f x) a b = c * RInt f a b.
Proof. exact (@RInt_scal R_CompleteNormedModule f a b c). Qed.

Lemma ideal_polynomial_integral r c degree (HD : (degree < 2 * rule_size r)%nat) :
  ideal_value (polynomial c degree) r = RInt (polynomial c degree) (-1) 1.
Proof.
  induction degree.
  - change (ideal_value (fun x => c O * x ^ O) r =
      RInt (fun x => c O * x ^ O) (-1) 1).
    rewrite (ideal_value_scal (c O) (fun x => x ^ O) r),
      (real_integral_scal (c O) (fun x => x ^ O) (-1) 1) by apply power_integrable.
    now rewrite (ideal_power_integral r O HD).
  - change (ideal_value (fun x => polynomial c degree x + c (S degree) * x ^ S degree) r =
      RInt (fun x => polynomial c degree x + c (S degree) * x ^ S degree) (-1) 1).
    rewrite (ideal_value_plus (polynomial c degree)
      (fun x => c (S degree) * x ^ S degree) r).
    rewrite (real_integral_plus (polynomial c degree)
      (fun x => c (S degree) * x ^ S degree) (-1) 1
      (polynomial_integrable c degree (-1) 1)
      (@ex_RInt_scal R_NormedModule (fun x => x ^ S degree) (-1) 1
        (c (S degree)) (power_integrable (S degree) (-1) 1))).
    rewrite (ideal_value_scal (c (S degree)) (fun x => x ^ S degree) r).
    rewrite (real_integral_scal (c (S degree)) (fun x => x ^ S degree)
      (-1) 1 (power_integrable (S degree) (-1) 1)).
    rewrite (IHdegree (ltac:(lia))), (ideal_power_integral r (S degree) HD). reflexivity.
Qed.

Theorem polynomial_comparison g r c degree error :
  (degree < 2 * rule_size r)%nat -> ex_RInt g (-1) 1 ->
  (forall x, -1 <= x <= 1 -> Rabs (g x - polynomial c degree x) <= error) ->
  Rabs (RInt g (-1) 1 - ideal_value g r) <= 4 * error.
Proof.
  intros HD HG HE.
  pose proof (polynomial_integrable c degree (-1) 1) as HP.
  pose proof (ideal_value_uniform_error g (polynomial c degree) r error HE) as HQ.
  pose proof (abs_RInt_le_const (fun x => g x - polynomial c degree x)
    (-1) 1 error (ltac:(lra)) (@ex_RInt_minus R_NormedModule g (polynomial c degree) (-1) 1 HG HP) HE) as HI.
  rewrite (real_integral_minus g (polynomial c degree) (-1) 1 HG HP) in HI.
  pose proof (ideal_polynomial_integral r c degree HD) as HEXACT.
  replace (RInt g (-1) 1 - ideal_value g r) with
    ((RInt g (-1) 1 - RInt (polynomial c degree) (-1) 1) +
      (ideal_value (polynomial c degree) r - ideal_value g r)) by lra.
  eapply Rle_trans; [apply Rabs_triang |].
  rewrite Rabs_minus_sym in HQ. lra.
Qed.

End GaussianPolynomialAccuracy.
