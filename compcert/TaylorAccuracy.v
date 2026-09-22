From Coq Require Import Reals Lia Psatz.
From Coquelicot Require Import Coquelicot.
From QuadratureC Require Import ClightRules TableAccuracy PolynomialAccuracy.

Import GaussianPolynomialAccuracy.
Local Open Scope R_scope.

Module GaussianTaylorAccuracy.

Definition moving_taylor (f : R -> R) n target center :=
  sum_f_R0 (fun k => (target - center) ^ k / INR (fact k) *
    Derive_n f k center) n.

Lemma real_derive_ext (f g : R -> R) x l :
  (forall t, f t = g t) -> is_derive f x l -> is_derive g x l.
Proof. exact (@is_derive_ext R_AbsRing R_NormedModule f g x l). Qed.

Lemma factorial_positive n : 0 < INR (fact n).
Proof. apply lt_0_INR, lt_O_fact. Qed.

Lemma scaled_power_derivative n target center :
  is_derive (fun t => (target - t) ^ S n / INR (fact (S n))) center
    (- ((target - center) ^ n / INR (fact n))).
Proof.
  assert (HB : is_derive (fun t => target - t) center (-1)).
  { replace (-1) with (0 - 1) by ring.
    apply (@is_derive_minus R_AbsRing R_NormedModule);
      [exact (@is_derive_const R_AbsRing R_NormedModule target center) |
       exact (@is_derive_id R_AbsRing center)]. }
  pose proof (is_derive_pow (fun t => target - t) (S n) center (-1) HB) as HP.
  pose proof (is_derive_scal (fun t => (target - t) ^ S n) center
    (/ INR (fact (S n))) (INR (S n) * (-1) * (target - center) ^ n) HP) as HS.
  replace (- ((target - center) ^ n / INR (fact n))) with
    (/ INR (fact (S n)) * (INR (S n) * (-1) * (target - center) ^ n)).
  - eapply real_derive_ext with
      (f := fun t => / INR (fact (S n)) * (target - t) ^ S n).
    + intros t. unfold Rdiv. ring.
    + exact HS.
  - change (fact (S n)) with (S n * fact n)%nat. rewrite mult_INR.
    field. split; [apply INR_fact_neq_0 | apply not_0_INR; lia].
Qed.

Lemma moving_taylor_derivative f n target center :
  (forall k, (k <= S n)%nat -> ex_derive_n f k center) ->
  is_derive (fun t => moving_taylor f n target t) center
    ((target - center) ^ n / INR (fact n) * Derive_n f (S n) center).
Proof.
  induction n; intros HD.
  - change (is_derive (fun t => 1 / 1 * f t) center
      (1 / 1 * Derive f center)).
    apply is_derive_scal, Derive_correct. exact (HD 1%nat (le_n _)).
  - assert (HI := IHn (fun k HK => HD k (ltac:(lia)))).
    assert (HN : is_derive (Derive_n f (S n)) center (Derive_n f (S (S n)) center)).
    { apply Derive_correct. exact (HD (S (S n)) (le_n _)). }
    pose proof (Derive.is_derive_mult
      (fun t => (target - t) ^ S n / INR (fact (S n)))
      (Derive_n f (S n)) center
      (- ((target - center) ^ n / INR (fact n)))
      (Derive_n f (S (S n)) center)
      (scaled_power_derivative n target center) HN) as HP.
    pose proof (@is_derive_plus R_AbsRing R_NormedModule
      (fun t => moving_taylor f n target t)
      (fun t => (target - t) ^ S n / INR (fact (S n)) * Derive_n f (S n) t)
      center _ _ HI HP) as HS.
    change (is_derive (fun t => moving_taylor f n target t +
      (target - t) ^ S n / INR (fact (S n)) * Derive_n f (S n) t) center
      ((target - center) ^ S n / INR (fact (S n)) * Derive_n f (S (S n)) center)).
    replace ((target - center) ^ S n / INR (fact (S n)) * Derive_n f (S (S n)) center)
      with ((target - center) ^ n / INR (fact n) * Derive_n f (S n) center +
        (- ((target - center) ^ n / INR (fact n)) * Derive_n f (S n) center +
        (target - center) ^ S n / INR (fact (S n)) * Derive_n f (S (S n)) center)) by ring.
    exact HS.
Qed.

Lemma moving_taylor_at_target f n target : moving_taylor f n target target = f target.
Proof.
  induction n.
  - unfold moving_taylor. cbn [sum_f_R0 pow fact INR Derive_n]. field.
  - change (moving_taylor f n target target +
      (target - target) ^ S n / INR (fact (S n)) * Derive_n f (S n) target = f target).
    rewrite IHn. replace (target - target) with 0 by ring. cbn [pow]. unfold Rdiv. ring.
Qed.

(** A Taylor formula in either direction, using derivatives only at points
    of the closed segment.  The moving expansion makes the lower derivative
    terms cancel before applying the mean value theorem. *)
Theorem taylor_segment f n x y :
  x <> y ->
  (forall t, Rmin x y <= t <= Rmax x y ->
    forall k, (k <= S n)%nat -> ex_derive_n f k t) ->
  exists z, Rmin x y < z < Rmax x y /\
    f y = moving_taylor f n y x +
      (y - x) ^ S n / INR (fact (S n)) * Derive_n f (S n) z.
Proof.
  intros HXY HD.
  assert (HPOW : (y - x) ^ S n <> 0) by (apply pow_nonzero; lra).
  set (c := (f y - moving_taylor f n y x) * INR (fact (S n)) / (y - x) ^ S n).
  set (g := fun t => moving_taylor f n y t + c * ((y - t) ^ S n / INR (fact (S n)))).
  set (dg := fun t => (y - t) ^ n / INR (fact n) * (Derive_n f (S n) t - c)).
  assert (HDG : forall t, Rmin x y <= t <= Rmax x y -> derivable_pt_lim g t (dg t)).
  { intros t HT. apply is_derive_Reals.
    pose proof (moving_taylor_derivative f n y t (HD t HT)) as H1.
    pose proof (is_derive_scal _ t c _ (scaled_power_derivative n y t)) as H2.
    pose proof (@is_derive_plus R_AbsRing R_NormedModule _ _ t _ _ H1 H2) as HS.
    unfold g, dg.
    replace ((y - t) ^ n / INR (fact n) * (Derive_n f (S n) t - c)) with
      ((y - t) ^ n / INR (fact n) * Derive_n f (S n) t +
        c * (- ((y - t) ^ n / INR (fact n)))) by ring.
    exact HS. }
  assert (HGX : g x = f y).
  { unfold g, c. field. split; [apply INR_fact_neq_0 | exact HPOW]. }
  assert (HGY : g y = f y).
  { unfold g. rewrite moving_taylor_at_target.
    replace (y - y) with 0 by ring. cbn [pow]. unfold Rdiv. ring. }
  assert (HORDER : Rmin x y < Rmax x y).
  { unfold Rmin, Rmax. destruct (Rle_dec x y); lra. }
  assert (HEND : g (Rmax x y) - g (Rmin x y) = 0).
  { unfold Rmin, Rmax. destruct (Rle_dec x y); rewrite HGX, HGY; ring. }
  destruct (MVT_cor2 g dg (Rmin x y) (Rmax x y) HORDER HDG) as [z [HE HZ]].
  assert (HDZ : dg z = 0) by (rewrite HEND in HE; nra).
  assert (HYZ : y - z <> 0).
  { unfold Rmin, Rmax in HZ. destruct (Rle_dec x y); lra. }
  assert (HFACTOR : (y - z) ^ n / INR (fact n) <> 0).
  { apply Rmult_integral_contrapositive_currified.
    - apply pow_nonzero, HYZ.
    - apply Rinv_neq_0_compat, INR_fact_neq_0. }
  unfold dg in HDZ. apply Rmult_integral in HDZ. destruct HDZ as [H0 | HC]; [contradiction |].
  exists z. split; [exact HZ |].
  replace (Derive_n f (S n) z) with c by lra.
  unfold c. field. split; [exact HPOW | apply INR_fact_neq_0].
Qed.

Definition taylor_coefficients (f : R -> R) k := Derive_n f k 0 / INR (fact k).

Lemma moving_taylor_center_zero f n x :
  moving_taylor f n x 0 = polynomial (taylor_coefficients f) n x.
Proof.
  induction n.
  - unfold moving_taylor, polynomial, taylor_coefficients.
    cbn [sum_f_R0 pow fact INR Derive_n]. field.
  - change (moving_taylor f n x 0 +
      (x - 0) ^ S n / INR (fact (S n)) * Derive_n f (S n) 0 =
      polynomial (taylor_coefficients f) n x + taylor_coefficients f (S n) * x ^ S n).
    rewrite IHn, Rminus_0_r. unfold taylor_coefficients, Rdiv. ring.
Qed.

Lemma abs_power_le_one x n : -1 <= x <= 1 -> Rabs (x ^ n) <= 1.
Proof.
  intros HX. induction n.
  - cbn [pow]. rewrite Rabs_R1. lra.
  - cbn [pow]. rewrite Rabs_mult.
    assert (HA : Rabs x <= 1) by (apply Rabs_le; lra).
    pose proof (Rabs_pos x). pose proof (Rabs_pos (x ^ n)). nra.
Qed.

Theorem centered_taylor_error f n bound :
  0 <= bound ->
  (forall t, -1 <= t <= 1 -> forall k, (k <= S n)%nat -> ex_derive_n f k t) ->
  (forall t, -1 <= t <= 1 -> Rabs (Derive_n f (S n) t) <= bound) ->
  forall x, -1 <= x <= 1 ->
    Rabs (f x - polynomial (taylor_coefficients f) n x) <= bound / INR (fact (S n)).
Proof.
  intros HB HD HM x HX.
  rewrite <- (moving_taylor_center_zero f n x).
  pose proof (factorial_positive (S n)) as HF.
  destruct (Req_dec x 0) as [H0 | H0].
  - subst x. rewrite moving_taylor_at_target, Rminus_diag, Rabs_R0.
    apply Rdiv_le_0_compat; lra.
  - destruct (taylor_segment f n 0 x (ltac:(lra))) as [z [HZ HE]].
    + intros t HT k HK. apply HD; [|exact HK].
      unfold Rmin, Rmax in HT. destruct (Rle_dec 0 x); lra.
    + assert (HZI : -1 <= z <= 1).
      { unfold Rmin, Rmax in HZ. destruct (Rle_dec 0 x); lra. }
      pose proof (HM z HZI) as HMD.
      pose proof (abs_power_le_one x (S n) HX) as HP.
      replace (f x - moving_taylor f n x 0) with
        (x ^ S n / INR (fact (S n)) * Derive_n f (S n) z) by
        (rewrite Rminus_0_r in HE; lra).
      rewrite Rabs_mult, Rabs_div, (Rabs_pos_eq (INR (fact (S n)))) by lra.
      unfold Rdiv. replace (Rabs (x ^ S n) * / INR (fact (S n)) * Rabs (Derive_n f (S n) z))
        with ((Rabs (x ^ S n) * Rabs (Derive_n f (S n) z)) * / INR (fact (S n))) by ring.
      apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; exact HF |].
      pose proof (Rabs_pos (Derive_n f (S n) z)). nra.
Qed.

Lemma derivative_integrable f n :
  (forall t, -1 <= t <= 1 -> forall k, (k <= S n)%nat -> ex_derive_n f k t) ->
  ex_RInt f (-1) 1.
Proof.
  intros HD. apply (@ex_RInt_continuous R_CompleteNormedModule).
  intros t HT. apply (@ex_derive_continuous R_AbsRing R_NormedModule).
  exact (HD t (ltac:(rewrite Rmin_left, Rmax_right in HT by lra; exact HT))
    1%nat (ltac:(lia))).
Qed.

(** This Taylor-based constant is deliberately weaker than the sharp
    Gaussian remainder constant.  It still supplies a derivative-based
    integral error for every supported C table. *)
Theorem ideal_rule_taylor_accuracy f r bound :
  0 <= bound ->
  (forall t, -1 <= t <= 1 -> forall k,
    (k <= 2 * rule_size r)%nat -> ex_derive_n f k t) ->
  (forall t, -1 <= t <= 1 -> Rabs (Derive_n f (2 * rule_size r) t) <= bound) ->
  Rabs (RInt f (-1) 1 - Binary64TableAccuracy.ideal_value f r) <=
    4 * (bound / INR (fact (2 * rule_size r))).
Proof.
  intros HB HD HM.
  assert (HN : (S (2 * rule_size r - 1) = 2 * rule_size r)%nat)
    by (destruct r; reflexivity).
  apply (polynomial_comparison f r (taylor_coefficients f) (2 * rule_size r - 1)).
  - lia.
  - apply (derivative_integrable f (2 * rule_size r - 1)). rewrite HN. exact HD.
  - pose proof (centered_taylor_error f (2 * rule_size r - 1) bound HB) as HT.
    rewrite HN in HT. exact (HT HD HM).
Qed.

End GaussianTaylorAccuracy.
