From Coq Require Import Reals List Lia Psatz.
From Coquelicot Require Import Coquelicot.

Import ListNotations.
Local Open Scope R_scope.

Module RealPolynomials.

(** Coefficients are stored in increasing order.  These small operations
    provide the interpolation polynomials without an external algebra oracle. *)
Fixpoint eval (p : list R) (x : R) : R :=
  match p with [] => 0 | c :: q => c + x * eval q x end.

Fixpoint add (p q : list R) : list R :=
  match p, q with
  | [], _ => q
  | _, [] => p
  | a :: p, b :: q => (a + b) :: add p q
  end.

Definition scale (c : R) (p : list R) := map (Rmult c) p.
Definition linear_mul a b p := add (scale a p) (0 :: scale b p).

Fixpoint derivative_aux (k : nat) (p : list R) : list R :=
  match p with
  | [] => []
  | c :: q => (INR k * c) :: derivative_aux (S k) q
  end.

Definition derivative (p : list R) :=
  match p with [] => [] | _ :: q => derivative_aux 1 q end.

Lemma eval_add p q x : eval (add p q) x = eval p x + eval q x.
Proof.
  revert q. induction p as [|a p IH]; intros [|b q]; cbn [add eval]; try ring.
  rewrite IH. ring.
Qed.

Lemma eval_scale c p x : eval (scale c p) x = c * eval p x.
Proof.
  induction p as [|a p IH]; [change (0 = c * 0); ring |].
  change (c * a + x * eval (scale c p) x = c * (a + x * eval p x)).
  rewrite IH. ring.
Qed.

Lemma eval_linear_mul a b p x :
  eval (linear_mul a b p) x = (a + b * x) * eval p x.
Proof. unfold linear_mul. rewrite eval_add. cbn [eval]. rewrite !eval_scale. ring. Qed.

Lemma length_add p q : (length (add p q) <= Nat.max (length p) (length q))%nat.
Proof.
  revert q. induction p as [|a p IH]; intros [|b q]; cbn [add length Nat.max]; try lia.
  specialize (IH q). lia.
Qed.

Lemma length_scale c p : length (scale c p) = length p.
Proof. apply length_map. Qed.

Lemma length_linear_mul a b p :
  (length (linear_mul a b p) <= S (length p))%nat.
Proof.
  unfold linear_mul. pose proof (length_add (scale a p) (0 :: scale b p)).
  cbn [length] in H. rewrite !length_scale in H. lia.
Qed.

Lemma length_derivative_aux k p : length (derivative_aux k p) = length p.
Proof. revert k. induction p; intros k; cbn; [reflexivity |now rewrite IHp]. Qed.

Lemma length_derivative p : length (derivative p) = Nat.pred (length p).
Proof. destruct p; cbn [derivative length Nat.pred]; [reflexivity |apply length_derivative_aux]. Qed.

Lemma eval_derivative_aux_succ k p x :
  eval (derivative_aux (S k) p) x =
    eval p x + eval (derivative_aux k p) x.
Proof.
  revert k. induction p as [|a p IH]; intros k; cbn [derivative_aux eval]; [ring |].
  rewrite IH, S_INR. ring.
Qed.

Lemma eval_derivative_cons a p x :
  eval (derivative (a :: p)) x = eval p x + x * eval (derivative p) x.
Proof.
  destruct p as [|b p]; cbn [derivative derivative_aux eval]; [ring |].
  rewrite eval_derivative_aux_succ. cbn [INR]. ring.
Qed.

Lemma eval_derivative p x :
  is_derive (eval p) x (eval (derivative p) x).
Proof.
  induction p as [|a p IH].
  - exact (@is_derive_const R_AbsRing R_NormedModule 0 x).
  - rewrite eval_derivative_cons.
    replace (eval p x + x * eval (derivative p) x) with
      (0 + (1 * eval p x + x * eval (derivative p) x)) by ring.
    change (is_derive (fun t => a + t * eval p t) x
      (0 + (1 * eval p x + x * eval (derivative p) x))).
    apply (@is_derive_plus R_AbsRing R_NormedModule).
    + apply (@is_derive_const R_AbsRing R_NormedModule).
    + apply Derive.is_derive_mult; [apply (@is_derive_id R_AbsRing) |exact IH].
Qed.

Lemma eval_derivative_add p q x :
  eval (derivative (add p q)) x =
    eval (derivative p) x + eval (derivative q) x.
Proof.
  rewrite <- (is_derive_unique _ _ _ (eval_derivative (add p q) x)).
  apply is_derive_unique.
  eapply (@is_derive_ext R_AbsRing R_NormedModule
    (fun t => eval p t + eval q t)).
  - intros t. symmetry. apply eval_add.
  - apply (@is_derive_plus R_AbsRing R_NormedModule); apply eval_derivative.
Qed.

Lemma eval_derivative_linear_mul a b p x :
  eval (derivative (linear_mul a b p)) x =
    b * eval p x + (a + b * x) * eval (derivative p) x.
Proof.
  rewrite <- (is_derive_unique _ _ _ (eval_derivative (linear_mul a b p) x)).
  apply is_derive_unique.
  eapply (@is_derive_ext R_AbsRing R_NormedModule
    (fun t => (a + b * t) * eval p t)).
  - intros t. symmetry. apply eval_linear_mul.
  - apply (Derive.is_derive_mult (fun t => a + b * t) (eval p) x
      b (eval (derivative p) x)); [|apply eval_derivative].
    assert (HD : is_derive (fun t => a + b * t) x (0 + b * 1)).
    { apply (@is_derive_plus R_AbsRing R_NormedModule).
      - apply (@is_derive_const R_AbsRing R_NormedModule).
      - apply is_derive_scal, (@is_derive_id R_AbsRing). }
    replace (0 + b * 1) with b in HD by ring. exact HD.
Qed.

Fixpoint iter_derivative (n : nat) (p : list R) :=
  match n with O => p | S k => derivative (iter_derivative k p) end.

Lemma eval_iter_derivative n p x :
  Derive_n (eval p) n x = eval (iter_derivative n p) x.
Proof.
  revert x. induction n; intros x; [reflexivity |].
  cbn [Derive_n iter_derivative].
  rewrite (Derive_ext _ _ _ IHn). apply is_derive_unique, eval_derivative.
Qed.

Lemma eval_smooth p n x : ex_derive_n (eval p) n x.
Proof.
  destruct n; [exact I |].
  change (ex_derive (Derive_n (eval p) n) x).
  apply (ex_derive_ext (eval (iter_derivative n p))).
  - intros t. symmetry. apply eval_iter_derivative.
  - exists (eval (derivative (iter_derivative n p)) x). apply eval_derivative.
Qed.

Lemma length_iter_derivative n p :
  length (iter_derivative n p) = (length p - n)%nat.
Proof.
  induction n; cbn [iter_derivative]; [lia |].
  rewrite length_derivative, IHn. lia.
Qed.

Lemma eval_high_derivative p n x :
  (length p <= n)%nat -> Derive_n (eval p) n x = 0.
Proof.
  intros HL. rewrite eval_iter_derivative.
  assert (HE : iter_derivative n p = []).
  { apply length_zero_iff_nil. rewrite length_iter_derivative. lia. }
  now rewrite HE.
Qed.

Lemma nth_nil k : nth k ([] : list R) 0 = 0.
Proof. destruct k; reflexivity. Qed.

Lemma coefficient_add p q k :
  nth k (add p q) 0 = nth k p 0 + nth k q 0.
Proof.
  revert p q. induction k; intros [|a p] [|b q]; cbn [add nth]; try ring.
  apply IHk.
Qed.

Lemma coefficient_scale c p k :
  nth k (scale c p) 0 = c * nth k p 0.
Proof.
  revert p. induction k; intros [|a p]; cbn [scale map nth]; try ring.
  apply IHk.
Qed.

Lemma coefficient_linear_mul a b p k :
  nth (S k) (linear_mul a b p) 0 =
    a * nth (S k) p 0 + b * nth k p 0.
Proof.
  unfold linear_mul. rewrite coefficient_add. cbn [nth].
  rewrite !coefficient_scale. reflexivity.
Qed.

Lemma coefficient_derivative_aux k p j :
  nth j (derivative_aux k p) 0 = INR (k + j) * nth j p 0.
Proof.
  revert k p. induction j; intros k [|a p]; cbn [derivative_aux nth]; try ring.
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite IHj. replace (S k + j)%nat with (k + S j)%nat by lia. reflexivity.
Qed.

Lemma coefficient_derivative p k :
  nth k (derivative p) 0 = INR (S k) * nth (S k) p 0.
Proof.
  destruct p.
  - change (nth k [] 0 = INR (S k) * 0). rewrite nth_nil. ring.
  - cbn [derivative nth]. rewrite coefficient_derivative_aux. reflexivity.
Qed.

Lemma coefficient_iter_derivative n p k :
  nth k (iter_derivative n p) 0 =
    (INR (fact (k + n)) / INR (fact k)) * nth (k + n) p 0.
Proof.
  revert k. induction n; intros k.
  - cbn [iter_derivative]. rewrite Nat.add_0_r. field. apply INR_fact_neq_0.
  - cbn [iter_derivative]. rewrite coefficient_derivative, IHn.
    replace (S k + n)%nat with (k + S n)%nat by lia.
    change (fact (S k)) with (S k * fact k)%nat. rewrite mult_INR.
    field. split; [apply INR_fact_neq_0 |apply not_0_INR; lia].
Qed.

Lemma eval_top_derivative p n x :
  (length p <= S n)%nat ->
  Derive_n (eval p) n x = INR (fact n) * nth n p 0.
Proof.
  intros HL. rewrite eval_iter_derivative.
  assert (HSHORT : (length (iter_derivative n p) <= 1)%nat).
  { rewrite length_iter_derivative. lia. }
  assert (HE : eval (iter_derivative n p) x = nth O (iter_derivative n p) 0).
  { destruct (iter_derivative n p) as [|a [|b p']]; cbn [length] in HSHORT;
      cbn [eval nth]; try ring; lia. }
  rewrite HE, coefficient_iter_derivative. cbn [Nat.add fact INR]. field.
Qed.

Lemma eval_integrable p a b : ex_RInt (eval p) a b.
Proof.
  apply (@ex_RInt_continuous R_CompleteNormedModule).
  intros x _. apply (@ex_derive_continuous R_AbsRing R_NormedModule).
  exact (eval_smooth p 1 x).
Qed.

End RealPolynomials.
