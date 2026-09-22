From Coq Require Import Reals List Lia Psatz.
From Coquelicot Require Import Coquelicot.
From QuadratureC Require Import RealPolynomials.

Import ListNotations RealPolynomials.
Local Open Scope R_scope.

Module HermiteInterpolation.

Fixpoint nodal_square (nodes : list R) : list R :=
  match nodes with
  | [] => [1]
  | a :: rest => linear_mul (-a) 1 (linear_mul (-a) 1 (nodal_square rest))
  end.

Lemma eval_nodal_square_cons a nodes x :
  eval (nodal_square (a :: nodes)) x = (x - a) ^ 2 * eval (nodal_square nodes) x.
Proof. cbn [nodal_square]. rewrite !eval_linear_mul. ring. Qed.

Lemma derivative_nodal_square_cons a nodes x :
  eval (derivative (nodal_square (a :: nodes))) x =
    2 * (x - a) * eval (nodal_square nodes) x +
    (x - a) ^ 2 * eval (derivative (nodal_square nodes)) x.
Proof.
  cbn [nodal_square]. rewrite !eval_derivative_linear_mul, eval_linear_mul. ring.
Qed.

Lemma length_nodal_square nodes :
  (length (nodal_square nodes) <= S (2 * length nodes))%nat.
Proof.
  induction nodes as [|a nodes IH]; [reflexivity |].
  cbn [nodal_square length].
  pose proof (length_linear_mul (-a) 1 (nodal_square nodes)).
  pose proof (length_linear_mul (-a) 1 (linear_mul (-a) 1 (nodal_square nodes))).
  lia.
Qed.

Lemma nodal_square_nonnegative nodes x : 0 <= eval (nodal_square nodes) x.
Proof.
  induction nodes as [|a nodes IH].
  - cbn [nodal_square eval]. lra.
  - rewrite eval_nodal_square_cons. apply Rmult_le_pos; [apply pow2_ge_0 |exact IH].
Qed.

Lemma nodal_square_positive nodes x :
  ~ In x nodes -> 0 < eval (nodal_square nodes) x.
Proof.
  induction nodes as [|a nodes IH]; intros HN.
  - cbn [nodal_square eval]. lra.
  - rewrite eval_nodal_square_cons. apply Rmult_lt_0_compat.
    + assert (x <> a) by (intros ->; apply HN; now left).
      assert ((x - a) ^ 2 <> 0) by (apply pow_nonzero; lra).
      pose proof (pow2_ge_0 (x - a)). lra.
    + apply IH. intros HI. apply HN. now right.
Qed.

Lemma nodal_square_zero nodes x :
  In x nodes -> eval (nodal_square nodes) x = 0 /\
    eval (derivative (nodal_square nodes)) x = 0.
Proof.
  induction nodes as [|a nodes IH]; [contradiction |].
  intros [HE |HI].
  - subst x. rewrite eval_nodal_square_cons, derivative_nodal_square_cons. split; ring.
  - destruct (IH HI) as [HZ HDZ].
    rewrite eval_nodal_square_cons, derivative_nodal_square_cons, HZ, HDZ. split; ring.
Qed.

Lemma nodal_square_monic nodes :
  nth (2 * length nodes) (nodal_square nodes) 0 = 1.
Proof.
  induction nodes as [|a nodes IH]; [reflexivity |].
  replace (2 * length (a :: nodes))%nat with (S (S (2 * length nodes))) by (cbn; lia).
  cbn [nodal_square]. rewrite coefficient_linear_mul.
  rewrite (nth_overflow (linear_mul (-a) 1 (nodal_square nodes))) by
    (pose proof (length_linear_mul (-a) 1 (nodal_square nodes));
     pose proof (length_nodal_square nodes); lia).
  rewrite coefficient_linear_mul.
  rewrite (nth_overflow (nodal_square nodes)) by
    (pose proof (length_nodal_square nodes); lia).
  rewrite IH. ring.
Qed.

Lemma nodal_square_top_derivative nodes x :
  Derive_n (eval (nodal_square nodes)) (2 * length nodes) x =
    INR (fact (2 * length nodes)).
Proof.
  rewrite eval_top_derivative by apply length_nodal_square.
  rewrite nodal_square_monic. ring.
Qed.

(** Add the unique linear multiple of the old nodal square that matches
    the new value and derivative.  Its double zeros preserve all earlier data. *)
Fixpoint interpolate (f df : R -> R) (nodes : list R) : list R :=
  match nodes with
  | [] => []
  | a :: rest =>
      let p := interpolate f df rest in
      let q := nodal_square rest in
      let A := (f a - eval p a) / eval q a in
      let B := (df a - eval (derivative p) a -
        A * eval (derivative q) a) / eval q a in
      add p (linear_mul (A - B * a) B q)
  end.

Lemma length_interpolate f df nodes :
  (length (interpolate f df nodes) <= 2 * length nodes)%nat.
Proof.
  induction nodes as [|a nodes IH]; [reflexivity |].
  cbn [interpolate].
  eapply Nat.le_trans; [apply length_add |].
  apply Nat.max_lub.
  - cbn [length]. lia.
  - eapply Nat.le_trans; [apply length_linear_mul |].
    pose proof (length_nodal_square nodes). cbn [length]. lia.
Qed.

Theorem interpolate_matches f df nodes :
  NoDup nodes ->
  forall x, In x nodes ->
    eval (interpolate f df nodes) x = f x /\
    eval (derivative (interpolate f df nodes)) x = df x.
Proof.
  intros HN. induction HN as [|a nodes HNA HND IH]; intros x HX; [contradiction |].
  cbn [interpolate]. set (p := interpolate f df nodes).
  set (q := nodal_square nodes).
  set (A := (f a - eval p a) / eval q a).
  set (B := (df a - eval (derivative p) a - A * eval (derivative q) a) / eval q a).
  rewrite eval_add, eval_linear_mul, eval_derivative_add, eval_derivative_linear_mul.
  destruct HX as [HX |HX].
  - subst x. assert (HQ : eval q a <> 0).
    { pose proof (nodal_square_positive nodes a HNA). unfold q. lra. }
    unfold B, A. split; field; exact HQ.
  - destruct (IH x HX) as [HP HDP].
    destruct (nodal_square_zero nodes x HX) as [HQ HDQ].
    change (eval p x = f x) in HP.
    change (eval (derivative p) x = df x) in HDP.
    change (eval q x = 0) in HQ.
    change (eval (derivative q) x = 0) in HDQ.
    rewrite HP, HDP, HQ, HDQ. split; ring.
Qed.

End HermiteInterpolation.
