From Coq Require Import Reals List Lia Psatz.
From compcert Require Import Integers Floats.
From Flocq Require Import Core Binary.

Import ListNotations.
Local Open Scope R_scope.
Local Transparent Float.zero Float.add Float.mul.

(** Range and rounding guarantees for the actual CompCert binary64 operations.
    No result-finiteness or per-operation error bound is assumed. *)
Module Binary64Roundoff.

Definition real (x : Floats.float) : R := B2R 53 1024 x.
Definition finite (x : Floats.float) : Prop := is_finite 53 1024 x = true.
Definition nearest : R -> R := round radix2 (SpecFloat.fexp 53 1024) ZnearestE.
Definition epsilon (radius : R) : R :=
  / 2 * ulp radix2 (SpecFloat.fexp 53 1024) radius.
Definition max_value : R := real (Binary.Bmax_float 53 1024 eq_refl eq_refl).

Local Instance valid_exponent : Valid_exp (SpecFloat.fexp 53 1024).
Proof. apply FLT_exp_valid. now compute. Qed.

Local Instance monotone_exponent : Monotone_exp (SpecFloat.fexp 53 1024).
Proof. apply FLT_exp_monotone. Qed.

Lemma epsilon_nonnegative radius : 0 <= epsilon radius.
Proof.
  unfold epsilon. apply Rmult_le_pos; [lra | apply ulp_ge_0].
Qed.

Lemma round_bounded radius x :
  Rabs x <= radius -> Rabs (nearest x - x) <= epsilon radius.
Proof.
  intros HB.
  eapply Rle_trans;
    [exact (@error_le_half_ulp radix2 _ valid_exponent
      (fun z => negb (Z.even z)) x) |].
  unfold epsilon. apply Rmult_le_compat_l; [lra |].
  apply (@ulp_le radix2 _ valid_exponent monotone_exponent).
  eapply Rle_trans; [exact HB | apply Rle_abs].
Qed.

Lemma round_no_overflow radius x :
  radius <= max_value -> Rabs x <= radius ->
  Rlt_bool (Rabs (nearest x)) (bpow radix2 1024) = true.
Proof.
  intros HM HB. apply Rlt_bool_true.
  eapply Rle_lt_trans with (r2 := max_value).
  - apply (@abs_round_le_generic radix2 _ valid_exponent ZnearestE
      (valid_rnd_N (fun z => negb (Z.even z))));
      [apply generic_format_B2R | lra].
  - eapply Rle_lt_trans; [apply Rle_abs | apply abs_B2R_lt_emax].
Qed.

Theorem add_bounded radius x y :
  radius <= max_value -> finite x -> finite y ->
  Rabs (real x + real y) <= radius ->
  finite (Float.add x y) /\
  real (Float.add x y) = nearest (real x + real y) /\
  Rabs (real (Float.add x y) - (real x + real y)) <= epsilon radius.
Proof.
  intros HM HX HY HB.
  pose proof (Bplus_correct 53 1024 eq_refl eq_refl
    Float.binop_nan BinarySingleNaN.mode_NE x y HX HY) as H.
  change (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) with ZnearestE in H.
  change (B2R 53 1024 x) with (real x) in H.
  change (B2R 53 1024 y) with (real y) in H.
  fold nearest in H.
  rewrite (round_no_overflow radius _ HM HB) in H.
  destruct H as [HE [HF HS]]. split; [exact HF |].
  change (real (Float.add x y) = nearest (real x + real y)) in HE.
  split; [exact HE |]. rewrite HE. exact (round_bounded radius _ HB).
Qed.

Theorem mul_bounded radius x y :
  radius <= max_value -> finite x -> finite y ->
  Rabs (real x * real y) <= radius ->
  finite (Float.mul x y) /\
  real (Float.mul x y) = nearest (real x * real y) /\
  Rabs (real (Float.mul x y) - real x * real y) <= epsilon radius.
Proof.
  intros HM HX HY HB.
  pose proof (Bmult_correct 53 1024 eq_refl eq_refl
    Float.binop_nan BinarySingleNaN.mode_NE x y) as H.
  change (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) with ZnearestE in H.
  change (B2R 53 1024 x) with (real x) in H.
  change (B2R 53 1024 y) with (real y) in H.
  fold nearest in H.
  rewrite (round_no_overflow radius _ HM HB) in H.
  destruct H as [HE [HF HS]]. split.
  - change (is_finite 53 1024 (Float.mul x y) =
      andb (is_finite 53 1024 x) (is_finite 53 1024 y)) in HF.
    unfold finite in *. rewrite HF, HX, HY. reflexivity.
  - change (real (Float.mul x y) = nearest (real x * real y)) in HE.
    split; [exact HE |]. rewrite HE. exact (round_bounded radius _ HB).
Qed.

(** The order of operations agrees with the C loop: round a product, then add
    it to the current accumulator. *)
Definition integrate (f : Floats.float -> Floats.float)
    (terms : list (Floats.float * Floats.float)) (initial : Floats.float) :=
  fold_left (fun acc t => Float.add acc (Float.mul (fst t) (f (snd t))))
    terms initial.

Definition exact_sum (f : Floats.float -> Floats.float)
    (terms : list (Floats.float * Floats.float)) :=
  fold_right (fun t acc => real (fst t) * real (f (snd t)) + acc) 0 terms.

Definition product_mass (f : Floats.float -> Floats.float)
    (terms : list (Floats.float * Floats.float)) :=
  fold_right (fun t acc => Rabs (real (fst t) * real (f (snd t))) + acc) 0 terms.

Fixpoint rounded_sum (f : Floats.float -> Floats.float)
    (terms : list (Floats.float * Floats.float)) (initial : R) : R :=
  match terms with
  | [] => initial
  | t :: ts =>
      rounded_sum f ts (nearest (initial + nearest (real (fst t) * real (f (snd t)))))
  end.

(** Finiteness of the initial accumulator, every product, and every subsequent
    accumulator; this is an output of the range proof. *)
Fixpoint finite_steps (f : Floats.float -> Floats.float)
    (terms : list (Floats.float * Floats.float)) (initial : Floats.float) : Prop :=
  finite initial /\
  match terms with
  | [] => True
  | t :: ts =>
      finite (Float.mul (fst t) (f (snd t))) /\
      finite_steps f ts (Float.add initial (Float.mul (fst t) (f (snd t))))
  end.

Lemma product_mass_nonnegative f terms : 0 <= product_mass f terms.
Proof.
  induction terms as [| t ts IH]; cbn [product_mass fold_right] in *.
  - lra.
  - change (0 <= Rabs (real (fst t) * real (f (snd t))) + product_mass f ts).
    pose proof (Rabs_pos (real (fst t) * real (f (snd t)))). lra.
Qed.

Theorem integrate_bounded radius f terms initial :
  radius <= max_value ->
  finite initial ->
  (forall t, In t terms -> finite (fst t) /\ finite (f (snd t))) ->
  Rabs (real initial) + product_mass f terms +
    2 * INR (length terms) * epsilon radius <= radius ->
  finite_steps f terms initial /\
  finite (integrate f terms initial) /\
  real (integrate f terms initial) = rounded_sum f terms (real initial) /\
  Rabs (real (integrate f terms initial) -
    (real initial + exact_sum f terms)) <= 2 * INR (length terms) * epsilon radius.
Proof.
  intros HM. revert initial.
  induction terms as [| t ts IH]; intros initial HI HF HB.
  - cbn [finite_steps integrate fold_left rounded_sum exact_sum fold_right length].
    split; [auto |]. split; [exact HI |]. split; [reflexivity |].
    rewrite Rplus_0_r, Rminus_diag, Rabs_R0. simpl. lra.
  - pose proof (epsilon_nonnegative radius) as HE.
    pose proof (product_mass_nonnegative f ts) as HT.
    pose proof (pos_INR (length ts)) as HN.
    pose proof (Rabs_pos (real initial)) as HA.
    change (Rabs (real initial) +
      (Rabs (real (fst t) * real (f (snd t))) + product_mass f ts) +
      2 * INR (S (length ts)) * epsilon radius <= radius) in HB.
    rewrite S_INR in HB.
    destruct (HF t (or_introl eq_refl)) as [HW HY].
    assert (HP : Rabs (real (fst t) * real (f (snd t))) <= radius) by nra.
    destruct (mul_bounded radius _ _ HM HW HY HP) as [HMF [HME HMB]].
    set (p := Float.mul (fst t) (f (snd t))) in *.
    assert (HPM : Rabs (real p) <=
        Rabs (real (fst t) * real (f (snd t))) + epsilon radius).
    { pose proof (Rabs_triang_inv (real p) (real (fst t) * real (f (snd t)))).
      lra. }
    assert (HS : Rabs (real initial + real p) <= radius).
    { pose proof (Rabs_triang (real initial) (real p)). nra. }
    destruct (add_bounded radius _ _ HM HI HMF HS) as [HAF [HAE HAB]].
    set (next := Float.add initial p) in *.
    assert (HNEXT : Rabs (real next) <= Rabs (real initial) +
        Rabs (real (fst t) * real (f (snd t))) + 2 * epsilon radius).
    { pose proof (Rabs_triang_inv (real next) (real initial + real p)).
      pose proof (Rabs_triang (real initial) (real p)). lra. }
    assert (HREST : Rabs (real next) + product_mass f ts +
        2 * INR (length ts) * epsilon radius <= radius) by nra.
    destruct (IH next HAF (fun u HU => HF u (or_intror HU)) HREST)
      as [HSTEPS [HFIN [HREAL HERR]]].
    cbn [finite_steps integrate fold_left rounded_sum exact_sum fold_right length].
    fold p. fold next. split; [auto |]. split; [exact HFIN |]. split.
    + change (real (integrate f ts next) =
        rounded_sum f ts
          (nearest (real initial + nearest (real (fst t) * real (f (snd t)))))).
      rewrite HREAL, HAE, HME. reflexivity.
    + change (Rabs (real (integrate f ts next) -
        (real initial + (real (fst t) * real (f (snd t)) + exact_sum f ts))) <=
        2 * INR (S (length ts)) * epsilon radius).
      rewrite S_INR.
      replace (real (integrate f ts next) -
        (real initial + (real (fst t) * real (f (snd t)) + exact_sum f ts)))
        with ((real (integrate f ts next) - (real next + exact_sum f ts)) +
          ((real next - (real initial + real p)) +
            (real p - real (fst t) * real (f (snd t))))) by ring.
      eapply Rle_trans; [apply Rabs_triang |].
      pose proof (Rabs_triang (real next - (real initial + real p))
        (real p - real (fst t) * real (f (snd t)))).
      nra.
Qed.

End Binary64Roundoff.
