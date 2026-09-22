From Coq Require Import Reals List Sorting.Sorted Lia Psatz.
From Coquelicot Require Import Coquelicot.
From QuadratureC Require Import RealPolynomials HermiteInterpolation HermiteRolle.

Import ListNotations RealPolynomials HermiteInterpolation HermiteRolle.
Local Open Scope R_scope.

Module HermiteRemainder.

Lemma sorted_nodes_nodup nodes :
  StronglySorted Rlt nodes -> NoDup nodes.
Proof.
  intros HS. induction HS; constructor; [|assumption].
  intros HI. rewrite List.Forall_forall in H. specialize (H _ HI). lra.
Qed.

(** The remainder is derived from the constructed interpolant and repeated
    Rolle.  No continuity of the highest derivative is needed for this
    pointwise statement. *)
Theorem hermite_remainder f nodes a b x :
  StronglySorted Rlt nodes ->
  List.Forall (fun t => a <= t <= b) nodes ->
  a <= x <= b ->
  (forall k t, (k <= 2 * length nodes)%nat -> a <= t <= b ->
    ex_derive_n f k t) ->
  exists z, a <= z <= b /\
    f x - eval (interpolate f (Derive f) nodes) x =
      eval (nodal_square nodes) x / INR (fact (2 * length nodes)) *
        Derive_n f (2 * length nodes) z.
Proof.
  intros HS HN HX HD.
  pose proof (sorted_nodes_nodup nodes HS) as HND.
  destruct (in_dec Req_EM_T x nodes) as [HIN |HOUT].
  - exists x. split; [exact HX |].
    destruct (interpolate_matches f (Derive f) nodes HND x HIN) as [HP _].
    destruct (nodal_square_zero nodes x HIN) as [HQ _].
    rewrite HP, HQ. unfold Rdiv. ring.
  - set (p := interpolate f (Derive f) nodes).
    set (q := nodal_square nodes).
    set (c := (f x - eval p x) / eval q x).
    assert (HQ : eval q x <> 0).
    { pose proof (nodal_square_positive nodes x HOUT). unfold q. lra. }
    set (d := fun k t => Derive_n f k t -
      eval (iter_derivative k p) t - c * eval (iter_derivative k q) t).
    destruct (double_zeros_rolle d a b nodes x HS HOUT HX) as [z [HZ HDZ]].
    + unfold d, c. cbn [Derive_n iter_derivative]. field. exact HQ.
    + rewrite List.Forall_forall in HN |- *. intros t HT.
      split; [apply HN; exact HT |].
      destruct (interpolate_matches f (Derive f) nodes HND t HT) as [HP HDP].
      destruct (nodal_square_zero nodes t HT) as [HQ0 HDQ].
      unfold d. cbn [Derive_n iter_derivative]. unfold p, q.
      rewrite HP, HDP, HQ0, HDQ. split; [ring |].
      rewrite (Derive_ext (fun t => f t) f t (fun _ => eq_refl)). ring.
    + intros k t HK HT. unfold d.
      apply (@is_derive_minus R_AbsRing R_NormedModule).
      * apply (@is_derive_minus R_AbsRing R_NormedModule).
        -- apply Derive_correct. exact (HD (S k) t (ltac:(lia)) HT).
        -- apply eval_derivative.
      * apply is_derive_scal, eval_derivative.
    + unfold d in HDZ. rewrite <- !eval_iter_derivative in HDZ.
      rewrite (eval_high_derivative p (2 * length nodes) z) in HDZ by
        (unfold p; apply length_interpolate).
      unfold q in HDZ. rewrite nodal_square_top_derivative in HDZ.
      exists z. split; [exact HZ |].
      change (f x - eval p x = eval q x / INR (fact (2 * length nodes)) *
        Derive_n f (2 * length nodes) z).
      replace (Derive_n f (2 * length nodes) z) with
        (c * INR (fact (2 * length nodes))) by lra.
      unfold c. field. split; [exact HQ |apply INR_fact_neq_0].
Qed.

Theorem hermite_remainder_bound f nodes a b bound :
  StronglySorted Rlt nodes ->
  List.Forall (fun t => a <= t <= b) nodes ->
  0 <= bound ->
  (forall k t, (k <= 2 * length nodes)%nat -> a <= t <= b ->
    ex_derive_n f k t) ->
  (forall t, a <= t <= b ->
    Rabs (Derive_n f (2 * length nodes) t) <= bound) ->
  forall x, a <= x <= b ->
    Rabs (f x - eval (interpolate f (Derive f) nodes) x) <=
      bound / INR (fact (2 * length nodes)) * eval (nodal_square nodes) x.
Proof.
  intros HS HN HB HD HM x HX.
  destruct (hermite_remainder f nodes a b x HS HN HX HD) as [z [HZ HE]].
  rewrite HE, Rabs_mult.
  assert (HF : 0 < INR (fact (2 * length nodes))) by (apply lt_0_INR, lt_O_fact).
  pose proof (nodal_square_nonnegative nodes x) as HQ.
  rewrite Rabs_pos_eq by (apply Rdiv_le_0_compat; lra).
  replace (bound / INR (fact (2 * length nodes)) * eval (nodal_square nodes) x) with
    (eval (nodal_square nodes) x / INR (fact (2 * length nodes)) * bound) by
    (unfold Rdiv; ring).
  apply Rmult_le_compat_l; [apply Rdiv_le_0_compat; lra |apply HM; exact HZ].
Qed.

End HermiteRemainder.
