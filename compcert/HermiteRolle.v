From Coq Require Import Reals List Sorting.Sorted Sorting.Permutation Lia Psatz.
From Coquelicot Require Import Coquelicot.

Import ListNotations.
Local Open Scope R_scope.

Module HermiteRolle.

(** Rolle's theorem between each consecutive pair of distinct zeros. *)
Lemma derivative_zeros_above f a b x xs :
  StronglySorted Rlt (x :: xs) ->
  List.Forall (fun t => a <= t <= b) (x :: xs) ->
  List.Forall (fun t => f t = 0) (x :: xs) ->
  (forall t, a <= t <= b -> ex_derive f t) ->
  exists ys,
    length ys = length xs /\
    StronglySorted Rlt ys /\
    List.Forall (fun t => x < t /\ a <= t <= b /\ Derive f t = 0) ys.
Proof.
  revert x. induction xs as [|y xs IH]; intros x HS HB HZ HD.
  - exists []. repeat split; constructor.
  - inversion HS as [|? ? HS' HXY]; subst.
    inversion HB as [|? ? HX HB']; subst.
    inversion HZ as [|? ? HFX HZ']; subst.
    inversion HXY as [|? ? Hxy Hxs]; subst.
    inversion HB' as [|? ? HY HBY]; subst.
    inversion HZ' as [|? ? HFY HZY]; subst.
    destruct (MVT_cor2 f (Derive f) x y Hxy) as [z [HE HZB]].
    + intros t HT. apply is_derive_Reals, Derive_correct, HD. lra.
    + assert (HDZ : Derive f z = 0) by (rewrite HFX, HFY in HE; nra).
      destruct (IH y HS' HB' HZ' HD) as [ys [HL [HSY HFY']]].
      exists (z :: ys). split; [cbn; now rewrite HL |]. split.
      * constructor; [exact HSY |].
        eapply List.Forall_impl; [|exact HFY']. intros t [HYT _]. lra.
      * constructor; [repeat split; lra |].
        eapply List.Forall_impl; [|exact HFY']. intros t [HYT HT].
        split; [lra | exact HT].
Qed.

(** A derivative tower avoids any implicit smoothness assumptions at the
    interval endpoints.  Each derivative used by Rolle is required on the
    closed interval explicitly. *)
Theorem repeated_rolle d n a b xs :
  length xs = S n ->
  StronglySorted Rlt xs ->
  List.Forall (fun t => a <= t <= b /\ d O t = 0) xs ->
  (forall k t, (k < n)%nat -> a <= t <= b ->
    is_derive (d k) t (d (S k) t)) ->
  exists z, a <= z <= b /\ d n z = 0.
Proof.
  revert d xs. induction n as [|n IH]; intros d xs HL HS HZ HD.
  - destruct xs as [|x xs]; [discriminate |].
    inversion HZ; subst. exists x. assumption.
  - destruct xs as [|x xs]; [discriminate |].
    destruct (derivative_zeros_above (d O) a b x xs HS) as [ys [HLY [HSY HZY]]].
    + eapply List.Forall_impl; [|exact HZ]. intros t [HT _]. exact HT.
    + eapply List.Forall_impl; [|exact HZ]. intros t [_ HT]. exact HT.
    + intros t HT. exists (d 1%nat t). apply HD; [lia | exact HT].
    + apply (IH (fun k => d (S k)) ys).
      * cbn in HL. lia.
      * exact HSY.
      * eapply List.Forall_impl; [|exact HZY]. intros t [_ [HT HZERO]].
        split; [exact HT |].
        rewrite <- (is_derive_unique _ _ _ (HD O t (ltac:(lia)) HT)).
        exact HZERO.
      * intros k t HK HT. apply HD; [lia |exact HT].
Qed.

Corollary repeated_rolle_Derive_n f n a b xs :
  length xs = S n ->
  StronglySorted Rlt xs ->
  List.Forall (fun t => a <= t <= b /\ f t = 0) xs ->
  (forall k t, (k <= n)%nat -> a <= t <= b -> ex_derive_n f k t) ->
  exists z, a <= z <= b /\ Derive_n f n z = 0.
Proof.
  intros HL HS HZ HD.
  apply (repeated_rolle (Derive_n f) n a b xs HL HS HZ).
  intros k t HK HT. apply Derive_correct. apply (HD (S k)); [lia |exact HT].
Qed.

(** The first Rolle step retains zeros at which the derivative is already
    known to vanish.  Hermite interpolation uses exactly these double zeros. *)
Lemma derivative_zeros_retained f keep a b x xs :
  StronglySorted Rlt (x :: xs) ->
  List.Forall (fun t => a <= t <= b /\ f t = 0 /\
    (keep t = true -> Derive f t = 0)) (x :: xs) ->
  (forall t, a <= t <= b -> ex_derive f t) ->
  exists ys,
    length ys = (length xs + length (filter keep (x :: xs)))%nat /\
    StronglySorted Rlt ys /\
    List.Forall (fun t => x <= t /\ a <= t <= b /\ Derive f t = 0) ys.
Proof.
  revert x. induction xs as [|y xs IH]; intros x HS HZ HD.
  - inversion HZ as [|? ? [HX [HFX HDX]] HREST]; subst.
    destruct (keep x) eqn:HK.
    + exists [x]. cbn [filter]. rewrite HK. cbn. split; [reflexivity |].
      split; [repeat constructor |]. constructor; [repeat split; try lra; auto |constructor].
    + exists []. cbn [filter]. rewrite HK. cbn. repeat split; constructor.
  - inversion HS as [|? ? HS' HXY]; subst.
    inversion HXY as [|? ? Hxy Hxs]; subst.
    inversion HZ as [|? ? [HX [HFX HDX]] HZ']; subst.
    inversion HZ' as [|? ? [HY [HFY HDY]] HZS]; subst.
    destruct (MVT_cor2 f (Derive f) x y Hxy) as [z [HE HZB]].
    + intros t HT. apply is_derive_Reals, Derive_correct, HD. lra.
    + assert (HDZ : Derive f z = 0) by (rewrite HFX, HFY in HE; nra).
      destruct (IH y HS' HZ' HD) as [ys [HL [HSY HZY]]].
      assert (HSZY : StronglySorted Rlt (z :: ys)).
      { constructor; [exact HSY |].
        eapply List.Forall_impl; [|exact HZY]. intros t [HYT _]. lra. }
      assert (HZYS : List.Forall
        (fun t => x <= t /\ a <= t <= b /\ Derive f t = 0) (z :: ys)).
      { constructor; [repeat split; lra |].
        eapply List.Forall_impl; [|exact HZY]. intros t [HYT HT].
        split; [lra |exact HT]. }
      destruct (keep x) eqn:HK.
      * exists (x :: z :: ys). split.
        -- change (S (S (length ys)) = S (length xs) +
             length (if keep x then x :: filter keep (y :: xs)
               else filter keep (y :: xs)))%nat.
           rewrite HK. cbn [length]. lia.
        -- split.
           ++ constructor; [exact HSZY |]. constructor; [lra |].
              eapply List.Forall_impl; [|exact HZY]. intros t [HYT _]. lra.
           ++ constructor; [repeat split; try lra; auto |exact HZYS].
      * exists (z :: ys). split.
        -- change (S (length ys) = S (length xs) +
             length (if keep x then x :: filter keep (y :: xs)
               else filter keep (y :: xs)))%nat.
           rewrite HK. cbn [length]. lia.
        -- split; assumption.
Qed.

Fixpoint insert_point (x : R) (xs : list R) :=
  match xs with
  | [] => [x]
  | y :: ys => if Rlt_dec x y then x :: xs else y :: insert_point x ys
  end.

Lemma insert_point_permutation x xs :
  Permutation (insert_point x xs) (x :: xs).
Proof.
  induction xs as [|y ys IH]; [reflexivity |].
  cbn [insert_point]. destruct (Rlt_dec x y); [reflexivity |].
  eapply Permutation_trans; [apply perm_skip, IH |apply perm_swap].
Qed.

Lemma insert_point_sorted x xs :
  StronglySorted Rlt xs -> ~ In x xs ->
  StronglySorted Rlt (insert_point x xs).
Proof.
  intros HS. induction HS as [|y ys HS IH HY]; intros HN.
  - cbn. repeat constructor.
  - cbn [insert_point]. destruct (Rlt_dec x y) as [HXY |HXY].
    + constructor; [constructor; assumption |]. constructor; [exact HXY |].
      eapply List.Forall_impl; [|exact HY]. intros t HYT. lra.
    + constructor.
      * apply IH. intros HI. apply HN. now right.
      * apply (Permutation_Forall (Permutation_sym (insert_point_permutation x ys))).
        constructor; [|exact HY]. assert (x <> y) by (intros ->; apply HN; now left).
        lra.
Qed.

Lemma filter_permutation {A} (keep : A -> bool) xs ys :
  Permutation xs ys -> Permutation (filter keep xs) (filter keep ys).
Proof.
  intros HP. induction HP; cbn [filter].
  - reflexivity.
  - destruct (keep x); [apply perm_skip |]; assumption.
  - destruct (keep x), (keep y); try reflexivity. apply perm_swap.
  - eapply Permutation_trans; eassumption.
Qed.

Lemma filter_all {A} (keep : A -> bool) xs :
  (forall x, In x xs -> keep x = true) -> filter keep xs = xs.
Proof.
  induction xs as [|x xs IH]; intros HK; [reflexivity |].
  cbn [filter]. rewrite HK by now left.
  rewrite IH; [reflexivity |]. intros y HY. apply HK. now right.
Qed.

(** A function with n double zeros and one further zero has a zero of its
    derivative of order 2n.  The extra zero may occur anywhere in the interval. *)
Theorem double_zeros_rolle d a b nodes x :
  StronglySorted Rlt nodes ->
  ~ In x nodes ->
  a <= x <= b ->
  d O x = 0 ->
  List.Forall (fun t => a <= t <= b /\ d O t = 0 /\ d 1%nat t = 0) nodes ->
  (forall k t, (k < 2 * length nodes)%nat -> a <= t <= b ->
    is_derive (d k) t (d (S k) t)) ->
  exists z, a <= z <= b /\ d (2 * length nodes)%nat z = 0.
Proof.
  intros HS HNX HX HFX HN HD.
  destruct nodes as [|first nodes].
  - exists x. exact (conj HX HFX).
  - set (keep := fun t => if Req_EM_T t x then false else true).
    set (roots := insert_point x (first :: nodes)).
    assert (HP : Permutation roots (x :: first :: nodes)) by apply insert_point_permutation.
    assert (HL : length roots = S (length (first :: nodes))).
    { rewrite (Permutation_length HP). reflexivity. }
    assert (HFILTER : length (filter keep roots) = length (first :: nodes)).
    { rewrite (Permutation_length (filter_permutation keep _ _ HP)).
      change (length (if keep x then x :: filter keep (first :: nodes)
        else filter keep (first :: nodes)) = length (first :: nodes)).
      unfold keep at 1. destruct (Req_EM_T x x); [|contradiction].
      rewrite filter_all; [reflexivity |].
      intros t HT. unfold keep. destruct (Req_EM_T t x); [subst; contradiction |reflexivity]. }
    assert (HROOTS : StronglySorted Rlt roots) by (apply insert_point_sorted; assumption).
    assert (HROOTZ : List.Forall (fun t => a <= t <= b /\ d O t = 0 /\
      (keep t = true -> Derive (d O) t = 0)) roots).
    { apply (Permutation_Forall (Permutation_sym HP)). constructor.
      - split; [exact HX |]. split; [exact HFX |].
        unfold keep. destruct (Req_EM_T x x); [discriminate |contradiction].
      - eapply List.Forall_impl; [|exact HN]. intros t [HT [HZ HDZ]].
        split; [exact HT |]. split; [exact HZ |]. intros _.
        rewrite (is_derive_unique _ _ _ (HD O t (ltac:(cbn; lia)) HT)). exact HDZ. }
    destruct roots as [|r rs]; [discriminate |].
    destruct (derivative_zeros_retained (d O) keep a b r rs HROOTS HROOTZ)
      as [ys [HLY [HSY HZY]]].
    + intros t HT. exists (d 1%nat t). apply HD; [cbn; lia |exact HT].
    + assert (HCOUNT : (length ys = 2 * length (first :: nodes))%nat).
      { rewrite HFILTER in HLY. cbn [length] in HL, HLY |- *. lia. }
      destruct (repeated_rolle (fun k => d (S k))
        (2 * length (first :: nodes) - 1) a b ys) as [z [HZ HZERO]].
      * cbn in HCOUNT |- *. lia.
      * exact HSY.
      * eapply List.Forall_impl; [|exact HZY]. intros t [_ [HT HZERO]].
        split; [exact HT |].
        rewrite <- (is_derive_unique _ _ _ (HD O t (ltac:(cbn; lia)) HT)).
        exact HZERO.
      * intros k t HK HT. apply HD; [cbn in HK |- *; lia |exact HT].
      * exists z. split; [exact HZ |].
        replace (2 * length (first :: nodes))%nat with
          (S (2 * length (first :: nodes) - 1)) by (cbn; lia).
        exact HZERO.
Qed.

End HermiteRolle.
