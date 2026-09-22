From Coq Require Import Reals List Lia Psatz.
From compcert Require Import Floats.
From QuadratureC Require Import ClightRules FiniteArithmetic ClightRoundoff TableAccuracy.

Import ListNotations Binary64Roundoff Binary64TableAccuracy.
Local Open Scope R_scope.

(** Accuracy before the analytic quadrature remainder. We compare the
    floating-point loop with the ideal real rule, accounting for table
    perturbations and callback error as well as arithmetic rounding. *)
Module Binary64CallbackAccuracy.

Definition sum_on (indices : list nat) (h : nat -> R) :=
  fold_right (fun i acc => h i + acc) 0 indices.

Lemma sum_on_le indices h k :
  (forall i, In i indices -> h i <= k i) -> sum_on indices h <= sum_on indices k.
Proof.
  induction indices as [|i is IH]; intros H; cbn [sum_on fold_right].
  - lra.
  - apply Rplus_le_compat; [apply H; now left | apply IH; intros j HJ; apply H; now right].
Qed.

Lemma sum_on_add indices h k :
  sum_on indices (fun i => h i + k i) = sum_on indices h + sum_on indices k.
Proof.
  unfold sum_on. induction indices; cbn [fold_right] in *;
    [ring | rewrite IHindices; ring].
Qed.

Lemma sum_on_mul indices h c :
  sum_on indices (fun i => h i * c) = sum_on indices h * c.
Proof.
  unfold sum_on. induction indices; cbn [fold_right] in *;
    [ring | rewrite IHindices; ring].
Qed.

Lemma sum_on_const indices c : sum_on indices (fun _ => c) = INR (length indices) * c.
Proof.
  unfold sum_on. induction indices; cbn [fold_right length]; [simpl; ring |].
  rewrite IHindices, S_INR. ring.
Qed.

Lemma sum_on_abs_sub indices h k :
  Rabs (sum_on indices h - sum_on indices k) <=
    sum_on indices (fun i => Rabs (h i - k i)).
Proof.
  induction indices as [|i is IH]; cbn [sum_on fold_right] in *.
  - rewrite Rminus_diag, Rabs_R0. lra.
  - replace (h i + fold_right (fun i acc => h i + acc) 0 is -
      (k i + fold_right (fun i acc => k i + acc) 0 is)) with
      ((h i - k i) + (sum_on is h - sum_on is k)) by (unfold sum_on; ring).
    eapply Rle_trans; [apply Rabs_triang |]. unfold sum_on in *. lra.
Qed.

Lemma product_mass_as_sum f r :
  product_mass f (rule_terms r) = sum_on (seq 0 (rule_size r))
    (fun i => Rabs (real (rule_weight r i) * real (f (rule_node r i)))).
Proof.
  unfold product_mass, rule_terms, sum_on.
  induction (seq 0 (rule_size r)); cbn [map fold_right fst snd];
    [reflexivity | now rewrite IHl].
Qed.

Lemma exact_sum_as_sum f r :
  exact_sum f (rule_terms r) = sum_on (seq 0 (rule_size r))
    (fun i => real (rule_weight r i) * real (f (rule_node r i))).
Proof.
  unfold exact_sum, rule_terms, sum_on.
  induction (seq 0 (rule_size r)); cbn [map fold_right fst snd];
    [reflexivity | now rewrite IHl].
Qed.

(** The callback is finite and approximates g at every finite input in
    [-1,1]. The execution contract for the C callback is supplied separately. *)
Definition callback_accuracy (f : Floats.float -> Floats.float) (g : R -> R) error :=
  forall x, finite x -> -1 <= real x <= 1 ->
    finite (f x) /\ Rabs (real (f x) - g (real x)) <= error.

Definition lipschitz_on_interval (g : R -> R) constant :=
  forall x y, -1 <= x <= 1 -> -1 <= y <= 1 ->
    Rabs (g x - g y) <= constant * Rabs (x-y).

(** The first-derivative bound used by the paper supplies the Lipschitz
    hypothesis of the accuracy theorem, by the mean value theorem. *)
Lemma lipschitz_of_derivative_bound g g' constant :
  (forall x, -1 <= x <= 1 -> derivable_pt_lim g x (g' x)) ->
  (forall x, -1 <= x <= 1 -> Rabs (g' x) <= constant) ->
  lipschitz_on_interval g constant.
Proof.
  intros HD HB.
  assert (HORDER : forall a b, -1 <= a <= 1 -> -1 <= b <= 1 -> a < b ->
    Rabs (g b - g a) <= constant * Rabs (b-a)).
  { intros a b HA HB' HAB.
    destruct (MVT_cor2 g g' a b HAB (fun c HC => HD c (ltac:(lra)))) as [c [HE HC]].
    rewrite HE, Rabs_mult. apply Rmult_le_compat_r; [apply Rabs_pos | apply HB; lra]. }
  intros x y HX HY. destruct (Rtotal_order x y) as [HXY | [HXY | HXY]].
  - rewrite (Rabs_minus_sym (g x) (g y)), (Rabs_minus_sym x y).
    exact (HORDER x y HX HY HXY).
  - subst y. rewrite !Rminus_diag, Rabs_R0. lra.
  - exact (HORDER y x HY HX HXY).
Qed.

(** Positivity and total mass two of the exact weights give a bound on
    the absolute mass of the stored weights. *)
Lemma stored_weight_mass r :
  sum_on (seq 0 (rule_size r)) (fun i => Rabs (real (rule_weight r i))) <=
    2 + INR (rule_size r) * weight_tolerance.
Proof.
  eapply Rle_trans with (r2 := sum_on (seq 0 (rule_size r))
    (fun i => ideal_weight r i + weight_tolerance)).
  - apply sum_on_le. intros i HI. apply in_seq in HI.
    assert (HIB : (i < rule_size r)%nat) by lia.
    pose proof (rule_weight_error r i HIB) as HE.
    pose proof (ideal_weight_positive r i HIB) as HP.
    pose proof (Rabs_triang_inv (real (rule_weight r i)) (ideal_weight r i)).
    rewrite (Rabs_right (ideal_weight r i)) in H by lra. lra.
  - rewrite sum_on_add, sum_on_const, length_seq.
    unfold sum_on. rewrite ideal_weights_sum. lra.
Qed.

Lemma callback_at_node f g error constant r i :
  callback_accuracy f g error -> 0 <= constant -> lipschitz_on_interval g constant ->
  (i < rule_size r)%nat ->
  finite (f (rule_node r i)) /\
  Rabs (real (f (rule_node r i)) - g (ideal_node r i)) <=
    error + constant * node_tolerance.
Proof.
  intros HC HL HG HI.
  destruct (HC _ (rule_node_finite r i HI) (rule_node_interval r i HI)) as [HF HE].
  split; [exact HF |].
  pose proof (HG _ _ (rule_node_interval r i HI) (ideal_node_interval r i HI)) as HN.
  pose proof (Rmult_le_compat_l constant _ _ HL (rule_node_error r i HI)) as HD.
  replace (real (f (rule_node r i)) - g (ideal_node r i)) with
    ((real (f (rule_node r i)) - g (real (rule_node r i))) +
      (g (real (rule_node r i)) - g (ideal_node r i))) by ring.
  eapply Rle_trans; [apply Rabs_triang |]. lra.
Qed.

Lemma callback_magnitude f g error bound r i :
  callback_accuracy f g error ->
  (forall x, -1 <= x <= 1 -> Rabs (g x) <= bound) ->
  (i < rule_size r)%nat -> Rabs (real (f (rule_node r i))) <= bound + error.
Proof.
  intros HC HB HI.
  destruct (HC _ (rule_node_finite r i HI) (rule_node_interval r i HI)) as [_ HE].
  pose proof (HB _ (rule_node_interval r i HI)).
  pose proof (Rabs_triang_inv (real (f (rule_node r i))) (g (real (rule_node r i)))).
  lra.
Qed.

Lemma product_mass_bound f g error bound r :
  callback_accuracy f g error -> 0 <= error -> 0 <= bound ->
  (forall x, -1 <= x <= 1 -> Rabs (g x) <= bound) ->
  product_mass f (rule_terms r) <=
    (2 + INR (rule_size r) * weight_tolerance) * (bound + error).
Proof.
  intros HC HE HB HG. rewrite product_mass_as_sum.
  eapply Rle_trans with (r2 := sum_on (seq 0 (rule_size r))
    (fun i => Rabs (real (rule_weight r i)) * (bound + error))).
  - apply sum_on_le. intros i HI. apply in_seq in HI. rewrite Rabs_mult.
    apply Rmult_le_compat_l; [apply Rabs_pos |].
    apply (callback_magnitude f g error bound r i HC HG). lia.
  - rewrite sum_on_mul. apply Rmult_le_compat_r; [lra | apply stored_weight_mass].
Qed.

Lemma weighted_sample_error w v y z weight_error sample_error bound :
  Rabs (w-v) <= weight_error -> Rabs (y-z) <= sample_error -> Rabs z <= bound ->
  Rabs (w*y-v*z) <= Rabs w * sample_error + weight_error * bound.
Proof.
  intros HW HY HZ. replace (w*y-v*z) with (w*(y-z)+(w-v)*z) by ring.
  eapply Rle_trans; [apply Rabs_triang |]. rewrite !Rabs_mult.
  apply Rplus_le_compat.
  - apply Rmult_le_compat_l; [apply Rabs_pos | exact HY].
  - apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact HW | exact HZ].
Qed.

(** Error of the exact sum of stored samples, before arithmetic rounding.
    Each callback error is enlarged by the displacement of its stored node. *)
Theorem samples_error f g error bound constant r :
  callback_accuracy f g error -> 0 <= error -> 0 <= constant ->
  (forall x, -1 <= x <= 1 -> Rabs (g x) <= bound) ->
  lipschitz_on_interval g constant ->
  Rabs (exact_sum f (rule_terms r) - ideal_value g r) <=
    (2 + INR (rule_size r) * weight_tolerance) * (error + constant * node_tolerance) +
      INR (rule_size r) * weight_tolerance * bound.
Proof.
  intros HC HE HL HB HG. rewrite exact_sum_as_sum.
  change (Rabs (sum_on (seq 0 (rule_size r))
    (fun i => real (rule_weight r i) * real (f (rule_node r i))) -
    sum_on (seq 0 (rule_size r)) (fun i => ideal_weight r i * g (ideal_node r i))) <=
    (2 + INR (rule_size r) * weight_tolerance) * (error + constant * node_tolerance) +
      INR (rule_size r) * weight_tolerance * bound).
  eapply Rle_trans; [apply sum_on_abs_sub |].
  eapply Rle_trans with (r2 := sum_on (seq 0 (rule_size r))
    (fun i => Rabs (real (rule_weight r i)) * (error + constant * node_tolerance) +
      weight_tolerance * bound)).
  - apply sum_on_le. intros i HI. apply in_seq in HI.
    assert (HIB : (i < rule_size r)%nat) by lia.
    apply weighted_sample_error.
    + exact (rule_weight_error r i HIB).
    + exact (proj2 (callback_at_node f g error constant r i HC HL HG HIB)).
    + exact (HB _ (ideal_node_interval r i HIB)).
  - rewrite sum_on_add, sum_on_mul, sum_on_const, length_seq.
    replace (INR (rule_size r) * (weight_tolerance * bound)) with
      (INR (rule_size r) * weight_tolerance * bound) by ring.
    apply Rplus_le_compat_r. apply Rmult_le_compat_r.
    + unfold node_tolerance. nra.
    + apply stored_weight_mass.
Qed.

(** A numerical range budget proves operation finiteness and the final
    error bound. No assumption asserts that an intermediate rounded result
    is finite, or that the computed quadrature is already accurate. The
    remaining analytic error is the difference between ideal_value and the
    integral; it is not part of this theorem. *)
Theorem rule_value_accuracy f g error bound constant radius r :
  callback_accuracy f g error -> 0 <= error -> 0 <= bound -> 0 <= constant ->
  (forall x, -1 <= x <= 1 -> Rabs (g x) <= bound) ->
  lipschitz_on_interval g constant ->
  radius <= max_value ->
  (2 + INR (rule_size r) * weight_tolerance) * (bound + error) +
    2 * INR (rule_size r) * epsilon radius <= radius ->
  finite (rule_value f r) /\
  Rabs (real (rule_value f r) - ideal_value g r) <=
    2 * INR (rule_size r) * epsilon radius +
    (2 + INR (rule_size r) * weight_tolerance) * (error + constant * node_tolerance) +
      INR (rule_size r) * weight_tolerance * bound.
Proof.
  intros HC HE HB HL HG HGL HM HR.
  assert (HF : forall i, (i < rule_size r)%nat -> finite (f (rule_node r i))).
  { intros i HI. exact (proj1 (HC _ (rule_node_finite r i HI) (rule_node_interval r i HI))). }
  pose proof (product_mass_bound f g error bound r HC HE HB HG) as HP.
  destruct (rule_value_bounded radius f r HM HF (ltac:(lra))) as [_ [HFIN [_ HROUND]]].
  split; [exact HFIN |].
  pose proof (samples_error f g error bound constant r HC HE HL HG HGL) as HS.
  replace (real (rule_value f r) - ideal_value g r) with
    ((real (rule_value f r) - exact_sum f (rule_terms r)) +
      (exact_sum f (rule_terms r) - ideal_value g r)) by ring.
  eapply Rle_trans; [apply Rabs_triang |]. lra.
Qed.

End Binary64CallbackAccuracy.
