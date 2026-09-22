From Coq Require Import Reals List Sorting.Sorted Lia Psatz.
From Coquelicot Require Import Coquelicot.
From QuadratureC Require Import ClightRules TableAccuracy PolynomialAccuracy
  TaylorAccuracy RealPolynomials HermiteInterpolation HermiteRemainder.

Import ListNotations Binary64TableAccuracy GaussianPolynomialAccuracy
  GaussianTaylorAccuracy RealPolynomials HermiteInterpolation HermiteRemainder.
Local Open Scope R_scope.

Module GaussianSharpAccuracy.

Lemma ideal_nodes_length r : length (ideal_nodes r) = rule_size r.
Proof. destruct r; reflexivity. Qed.

Lemma ideal_nodes_sorted r : StronglySorted Rlt (ideal_nodes r).
Proof.
  pose proof two_node_spec. pose proof three_node_spec.
  pose proof four_inner_spec. pose proof four_outer_spec.
  pose proof four_radical_spec. pose proof four_radical_bounds.
  assert (HT : 0 < two_node) by nra.
  assert (HH : 0 < three_node) by nra.
  assert (HI : 0 < four_inner) by nra.
  assert (HO : four_inner < four_outer) by nra.
  destruct r; cbn [ideal_nodes]; repeat constructor; lra.
Qed.

Lemma ideal_nodes_interval r :
  List.Forall (fun t => -1 <= t <= 1) (ideal_nodes r).
Proof.
  rewrite List.Forall_forall. intros x HX.
  apply In_nth with (d := 0) in HX. destruct HX as [i [HI HE]].
  subst x. apply ideal_node_interval. rewrite ideal_nodes_length in HI. exact HI.
Qed.

Lemma ideal_node_member r i :
  (i < rule_size r)%nat -> In (ideal_node r i) (ideal_nodes r).
Proof. intros HI. apply nth_In. rewrite ideal_nodes_length. exact HI. Qed.

Lemma ideal_value_ext_nodes g h r :
  (forall x, In x (ideal_nodes r) -> g x = h x) ->
  ideal_value g r = ideal_value h r.
Proof.
  intros HE. unfold ideal_value.
  assert (HF : forall indices,
    (forall i, In i indices -> (i < rule_size r)%nat) ->
    fold_right (fun i acc => ideal_weight r i * g (ideal_node r i) + acc) 0 indices =
    fold_right (fun i acc => ideal_weight r i * h (ideal_node r i) + acc) 0 indices).
  { induction indices as [|i indices IH]; intros HB; [reflexivity |].
    cbn [fold_right]. rewrite HE by (apply ideal_node_member, HB; now left).
    rewrite IH; [reflexivity |]. intros j HJ. apply HB. now right. }
  apply HF. intros i HI. apply in_seq in HI. lia.
Qed.

(** Polynomial exactness also holds for the coefficient-list representation.
    The existing Taylor theorem has zero remainder above the polynomial's
    degree, so its earlier weaker constant disappears here. *)
Lemma ideal_eval_integral r p :
  (length p <= 2 * rule_size r)%nat ->
  ideal_value (eval p) r = RInt (eval p) (-1) 1.
Proof.
  intros HL.
  pose proof (ideal_rule_taylor_accuracy (eval p) r 0 (ltac:(lra))
    (fun t HT k HK => eval_smooth p k t)) as HE.
  assert (HM : forall t, -1 <= t <= 1 ->
    Rabs (Derive_n (eval p) (2 * rule_size r) t) <= 0).
  { intros t _. rewrite eval_high_derivative by exact HL. rewrite Rabs_R0. lra. }
  specialize (HE HM). replace (4 * (0 / INR (fact (2 * rule_size r)))) with 0 in HE by
    (unfold Rdiv; ring).
  assert (HZ : Rabs (RInt (eval p) (-1) 1 - ideal_value (eval p) r) = 0) by
    (pose proof (Rabs_pos (RInt (eval p) (-1) 1 - ideal_value (eval p) r)); lra).
  apply Rabs_eq_0 in HZ. lra.
Qed.

Lemma ideal_interpolant_integral f r :
  ideal_value f r =
    RInt (eval (interpolate f (Derive f) (ideal_nodes r))) (-1) 1.
Proof.
  rewrite <- (ideal_eval_integral r (interpolate f (Derive f) (ideal_nodes r))) by
    (pose proof (length_interpolate f (Derive f) (ideal_nodes r));
     rewrite ideal_nodes_length in H; exact H).
  apply ideal_value_ext_nodes. intros x HX.
  symmetry. apply (interpolate_matches f (Derive f) (ideal_nodes r));
    [apply sorted_nodes_nodup, ideal_nodes_sorted |exact HX].
Qed.

Theorem ideal_rule_nodal_accuracy f r bound :
  0 <= bound ->
  (forall t, -1 <= t <= 1 -> forall k,
    (k <= 2 * rule_size r)%nat -> ex_derive_n f k t) ->
  (forall t, -1 <= t <= 1 ->
    Rabs (Derive_n f (2 * rule_size r) t) <= bound) ->
  Rabs (RInt f (-1) 1 - ideal_value f r) <=
    bound / INR (fact (2 * rule_size r)) *
      RInt (eval (nodal_square (ideal_nodes r))) (-1) 1.
Proof.
  intros HB HD HM.
  set (p := interpolate f (Derive f) (ideal_nodes r)).
  set (q := nodal_square (ideal_nodes r)).
  set (c := bound / INR (fact (2 * rule_size r))).
  assert (HF : ex_RInt f (-1) 1).
  { apply (derivative_integrable f (2 * rule_size r - 1)).
    intros t HT k HK. apply HD; [exact HT |].
    destruct r; cbn [rule_size] in HK |- *; lia. }
  pose proof (eval_integrable p (-1) 1) as HP.
  pose proof (eval_integrable q (-1) 1) as HQ.
  assert (HBOUND : forall x, -1 <= x <= 1 ->
    Rabs (f x - eval p x) <= c * eval q x).
  { pose proof (hermite_remainder_bound f (ideal_nodes r) (-1) 1 bound
      (ideal_nodes_sorted r) (ideal_nodes_interval r) HB) as Hrem.
    rewrite ideal_nodes_length in Hrem. apply Hrem.
    - intros k t HK HT. exact (HD t HT k HK).
    - intros t HT. exact (HM t HT). }
  pose proof (@norm_RInt_le R_NormedModule
    (fun x => f x - eval p x) (fun x => c * eval q x)
    (-1) 1 (RInt (fun x => f x - eval p x) (-1) 1)
    (RInt (fun x => c * eval q x) (-1) 1) (ltac:(lra))
    HBOUND
    (RInt_correct _ _ _ (@ex_RInt_minus R_NormedModule f (eval p) (-1) 1 HF HP))
    (RInt_correct _ _ _ (@ex_RInt_scal R_NormedModule (eval q) (-1) 1 c HQ))) as HI.
  change (Rabs (RInt (fun x => f x - eval p x) (-1) 1) <=
    RInt (fun x => c * eval q x) (-1) 1) in HI.
  rewrite (real_integral_minus f (eval p) (-1) 1 HF HP),
    (real_integral_scal c (eval q) (-1) 1 HQ) in HI.
  rewrite ideal_interpolant_integral. exact HI.
Qed.

Definition monic_rule r x :=
  match r with
  | One => x
  | Two => x ^ 2 - 1/3
  | Three => x ^ 3 - 3/5 * x
  | Four => x ^ 4 - 6/7 * x ^ 2 + 3/35
  end.

Lemma nodal_square_formula r x :
  eval (nodal_square (ideal_nodes r)) x = (monic_rule r x) ^ 2.
Proof.
  pose proof two_node_spec as [_ HT]. pose proof three_node_spec as [_ HH].
  pose proof four_inner_spec as [_ HI]. pose proof four_outer_spec as [_ HO].
  pose proof four_radical_spec as [_ HR].
  assert (HS : four_inner ^ 2 + four_outer ^ 2 = 6/7) by lra.
  assert (HP : four_inner ^ 2 * four_outer ^ 2 = 3/35).
  { rewrite HI, HO. nra. }
  destruct r; cbn [ideal_nodes monic_rule];
    repeat rewrite eval_nodal_square_cons; change (nodal_square []) with [1];
    cbn [eval].
  - ring.
  - replace ((x - -two_node) ^ 2 * ((x - two_node) ^ 2 * (1 + x * 0))) with
      ((x ^ 2 - two_node ^ 2) ^ 2) by ring.
    rewrite HT. reflexivity.
  - replace ((x - -three_node) ^ 2 *
      ((x - 0) ^ 2 * ((x - three_node) ^ 2 * (1 + x * 0)))) with
      ((x ^ 3 - three_node ^ 2 * x) ^ 2) by ring.
    rewrite HH. reflexivity.
  - replace ((x - -four_outer) ^ 2 * ((x - -four_inner) ^ 2 *
      ((x - four_inner) ^ 2 * ((x - four_outer) ^ 2 * (1 + x * 0))))) with
      ((x ^ 4 - (four_inner ^ 2 + four_outer ^ 2) * x ^ 2 +
        four_inner ^ 2 * four_outer ^ 2) ^ 2) by ring.
    rewrite HS, HP. reflexivity.
Qed.

Definition nodal_coefficients r : list R :=
  match r with
  | One => [0; 0; 1]
  | Two => [1/9; 0; -2/3; 0; 1]
  | Three => [0; 0; 9/25; 0; -6/5; 0; 1]
  | Four => [9/1225; 0; -36/245; 0; 222/245; 0; -12/7; 0; 1]
  end.

Lemma nodal_square_polynomial r x :
  eval (nodal_square (ideal_nodes r)) x =
    polynomial (fun k => nth k (nodal_coefficients r) 0) 8 x.
Proof.
  rewrite nodal_square_formula. destruct r;
    cbn [monic_rule polynomial sum_f_R0 nodal_coefficients nth pow]; field.
Qed.

Lemma polynomial_integral_coefficients c n a b :
  RInt (polynomial c n) a b =
    sum_f_R0 (fun k => c k * (b ^ S k / INR (S k) - a ^ S k / INR (S k))) n.
Proof.
  induction n.
  - change (RInt (fun x => c O * x ^ O) a b =
      c O * (b ^ 1 / INR 1 - a ^ 1 / INR 1)).
    rewrite real_integral_scal by apply power_integrable.
    rewrite power_integral. reflexivity.
  - change (RInt (fun x => polynomial c n x + c (S n) * x ^ S n) a b =
      sum_f_R0 (fun k => c k * (b ^ S k / INR (S k) - a ^ S k / INR (S k))) n +
        c (S n) * (b ^ S (S n) / INR (S (S n)) - a ^ S (S n) / INR (S (S n)))).
    rewrite (real_integral_plus (polynomial c n) (fun x => c (S n) * x ^ S n) a b
      (polynomial_integrable c n a b)
      (@ex_RInt_scal R_NormedModule (fun x => x ^ S n) a b (c (S n))
        (power_integrable (S n) a b))).
    rewrite (real_integral_scal (c (S n)) (fun x => x ^ S n) a b
      (power_integrable (S n) a b)).
    rewrite IHn, power_integral. reflexivity.
Qed.

Definition nodal_integral r : R :=
  match r with One => 2/3 | Two => 8/45 | Three => 8/175 | Four => 128/11025 end.

Lemma nodal_square_integral r :
  RInt (eval (nodal_square (ideal_nodes r))) (-1) 1 = nodal_integral r.
Proof.
  rewrite (RInt_ext _ (polynomial (fun k => nth k (nodal_coefficients r) 0) 8))
    by (intros x _; apply nodal_square_polynomial).
  rewrite polynomial_integral_coefficients.
  destruct r; cbn [nodal_integral sum_f_R0 nodal_coefficients nth pow INR];
    field_simplify; lra.
Qed.

Definition sharp_constant r : R :=
  match r with One => 1/3 | Two => 1/135 | Three => 1/15750 | Four => 1/3472875 end.

Lemma factorial_real_succ n :
  INR (fact (S n)) = INR (S n) * INR (fact n).
Proof. change (INR (S n * fact n) = INR (S n) * INR (fact n)). apply mult_INR. Qed.

Lemma sharp_constant_formula r :
  nodal_integral r / INR (fact (2 * rule_size r)) = sharp_constant r.
Proof.
  destruct r; cbn [nodal_integral sharp_constant rule_size Nat.mul Nat.add];
    repeat rewrite factorial_real_succ; cbn [fact INR]; field_simplify; lra.
Qed.

Theorem ideal_rule_sharp_accuracy f r bound :
  0 <= bound ->
  (forall t, -1 <= t <= 1 -> forall k,
    (k <= 2 * rule_size r)%nat -> ex_derive_n f k t) ->
  (forall t, -1 <= t <= 1 ->
    Rabs (Derive_n f (2 * rule_size r) t) <= bound) ->
  Rabs (RInt f (-1) 1 - ideal_value f r) <= sharp_constant r * bound.
Proof.
  intros HB HD HM.
  pose proof (ideal_rule_nodal_accuracy f r bound HB HD HM) as HE.
  rewrite nodal_square_integral in HE.
  rewrite <- sharp_constant_formula. unfold Rdiv in HE |- *. nra.
Qed.

End GaussianSharpAccuracy.
