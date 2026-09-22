(** Integer arithmetic for the nearest-even rounding used by CompCert.

    A quotient, remainder, and parity test specify the result without real
    comparison or an abstract rounding operator. *)

From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core.

Local Open Scope R_scope.

Module IntegerRounding.

Definition round_quotient_even (numerator denominator : Z) : Z :=
  let quotient := (numerator / denominator)%Z in
  let remainder := (numerator mod denominator)%Z in
  if (2 * remainder <? denominator)%Z then quotient
  else if (denominator <? 2 * remainder)%Z then (quotient + 1)%Z
  else if Z.even quotient then quotient else (quotient + 1)%Z.

Theorem nearest_even_quotient numerator denominator :
  (0 < denominator)%Z ->
  ZnearestE (IZR numerator / IZR denominator) =
    round_quotient_even numerator denominator.
Proof.
  intros HD.
  assert (HD0 : denominator <> 0%Z) by lia.
  assert (HDR : 0 < IZR denominator) by now apply IZR_lt.
  assert (HDR0 : IZR denominator <> 0) by lra.
  pose proof (Z.div_mod numerator denominator HD0) as Hdivision.
  assert (Hfraction :
    (IZR numerator / IZR denominator - IZR (numerator / denominator)) *
      IZR denominator = IZR (numerator mod denominator)).
  { apply (f_equal IZR) in Hdivision.
    rewrite plus_IZR, mult_IZR in Hdivision.
    field_simplify; nra. }
  assert (Hceil :
    (0 < numerator mod denominator)%Z ->
    Zceil (IZR numerator / IZR denominator) =
      (numerator / denominator + 1)%Z).
  { intros HR.
    assert (Hneq : IZR (Zfloor (IZR numerator / IZR denominator)) <>
      IZR numerator / IZR denominator).
    { rewrite Zfloor_div by auto.
      intros HE. rewrite <- HE in Hfraction.
      pose proof (IZR_lt _ _ HR). nra. }
    rewrite Zceil_floor_neq by exact Hneq.
    now rewrite Zfloor_div by auto. }
  unfold Znearest, round_quotient_even.
  rewrite Zfloor_div by auto.
  destruct (Z.ltb_spec (2 * (numerator mod denominator)) denominator) as [HL | HL].
  - rewrite Rcompare_Lt. reflexivity.
    apply IZR_lt in HL. rewrite mult_IZR in HL. cbn in HL. nra.
  - destruct (Z.ltb_spec denominator (2 * (numerator mod denominator))) as [HG | HG].
    + rewrite Rcompare_Gt.
      * apply Hceil. lia.
      * apply IZR_lt in HG. rewrite mult_IZR in HG. cbn in HG. nra.
    + assert (HE : (2 * (numerator mod denominator) = denominator)%Z) by lia.
      rewrite Rcompare_Eq.
      * destruct (Z.even (numerator / denominator)); cbn.
        -- reflexivity.
        -- apply Hceil. lia.
      * apply (f_equal IZR) in HE. rewrite mult_IZR in HE. cbn in HE. nra.
Qed.

(** Move a binary scale into an integer numerator or positive denominator. *)
Definition scale (mantissa shift : Z) : Z * Z :=
  if (0 <=? shift)%Z then ((mantissa * 2 ^ shift)%Z, 1%Z)
  else (mantissa, (2 ^ (- shift))%Z).

Lemma scale_denominator_positive mantissa shift :
  (0 < snd (scale mantissa shift))%Z.
Proof.
  unfold scale. destruct (Z.leb_spec 0 shift); cbn.
  - lia.
  - apply Z.pow_pos_nonneg; lia.
Qed.

Lemma scale_real mantissa shift :
  IZR (fst (scale mantissa shift)) / IZR (snd (scale mantissa shift)) =
    IZR mantissa * bpow radix2 shift.
Proof.
  unfold scale. destruct (Z.leb_spec 0 shift) as [HS | HS]; cbn [fst snd].
  - change (IZR (mantissa * Zpower radix2 shift) / 1 =
      IZR mantissa * bpow radix2 shift).
    rewrite mult_IZR, (IZR_Zpower radix2 shift HS). field.
  - change (IZR mantissa / IZR (Zpower radix2 (-shift)) =
      IZR mantissa * bpow radix2 shift).
    rewrite (IZR_Zpower radix2 (-shift)) by lia.
    rewrite bpow_opp. unfold Rdiv.
    now rewrite Rinv_inv.
Qed.

Lemma digits_log2 mantissa :
  (0 < mantissa)%Z ->
  Zdigits radix2 mantissa = (Z.log2 mantissa + 1)%Z.
Proof.
  intros HM. apply Zdigits_unique.
  rewrite Z.abs_eq by lia.
  replace (Z.log2 mantissa + 1 - 1)%Z with (Z.log2 mantissa) by lia.
  exact (Z.log2_spec mantissa HM).
Qed.

(** The coefficient and exponent use only integer operations. *)
Definition round_dyadic (fexp : Z -> Z) (mantissa exponent : Z) : Z * Z :=
  let target := fexp (Z.log2 mantissa + exponent + 1)%Z in
  let scaled := scale mantissa (exponent - target)%Z in
  (round_quotient_even (fst scaled) (snd scaled), target).

Theorem round_dyadic_real fexp mantissa exponent :
  (0 < mantissa)%Z ->
  round radix2 fexp ZnearestE (IZR mantissa * bpow radix2 exponent) =
    IZR (fst (round_dyadic fexp mantissa exponent)) *
      bpow radix2 (snd (round_dyadic fexp mantissa exponent)).
Proof.
  intros HM.
  assert (HC : cexp radix2 fexp (IZR mantissa * bpow radix2 exponent) =
    fexp (Z.log2 mantissa + exponent + 1)%Z).
  { unfold cexp.
    change (fexp (mag radix2 (F2R (Float radix2 mantissa exponent))) =
      fexp (Z.log2 mantissa + exponent + 1)%Z).
    rewrite mag_F2R_Zdigits by lia.
    rewrite digits_log2 by exact HM.
    f_equal. lia. }
  unfold round, F2R. cbn [Fnum Fexp].
  unfold scaled_mantissa. rewrite HC.
  rewrite Rmult_assoc, <- bpow_plus.
  change (exponent + - fexp (Z.log2 mantissa + exponent + 1))%Z
    with (exponent - fexp (Z.log2 mantissa + exponent + 1))%Z.
  rewrite <- (scale_real mantissa
    (exponent - fexp (Z.log2 mantissa + exponent + 1))%Z).
  rewrite nearest_even_quotient by apply scale_denominator_positive.
  reflexivity.
Qed.

Definition dyadic_real (value : Z * Z) : R :=
  IZR (fst value) * bpow radix2 (snd value).

Lemma dyadic_real_zero value : dyadic_real value = 0 <-> fst value = 0%Z.
Proof.
  unfold dyadic_real. pose proof (bpow_gt_0 radix2 (snd value)) as HP.
  split.
  - intros HE. apply eq_IZR. nra.
  - intros ->. cbn. ring.
Qed.

Lemma dyadic_real_negative value : dyadic_real value < 0 <-> (fst value < 0)%Z.
Proof.
  unfold dyadic_real. pose proof (bpow_gt_0 radix2 (snd value)) as HP.
  split.
  - intros HE. apply lt_IZR. nra.
  - intros HE. apply IZR_lt in HE. nra.
Qed.

(** A signed coefficient is rounded by rounding its absolute magnitude. The
    separate sign of a floating-point zero is handled by the operation rules. *)
Definition round_signed (fexp : Z -> Z) (value : Z * Z) : Z * Z :=
  match fst value with
  | Z0 => (0%Z, 0%Z)
  | Zpos p => round_dyadic fexp (Zpos p) (snd value)
  | Zneg p =>
      let result := round_dyadic fexp (Zpos p) (snd value) in
      ((- fst result)%Z, snd result)
  end.

Theorem round_signed_real fexp value :
  round radix2 fexp ZnearestE (dyadic_real value) =
    dyadic_real (round_signed fexp value).
Proof.
  destruct value as [[| p | p] exponent].
  - change (round radix2 fexp ZnearestE (0 * bpow radix2 exponent) =
      0 * bpow radix2 0).
    rewrite Rmult_0_l, round_0 by apply valid_rnd_N. ring.
  - exact (round_dyadic_real fexp (Zpos p) exponent ltac:(lia)).
  - change (round radix2 fexp ZnearestE
      (IZR (- Zpos p) * bpow radix2 exponent) =
      IZR (- fst (round_dyadic fexp (Zpos p) exponent)) *
        bpow radix2 (snd (round_dyadic fexp (Zpos p) exponent))).
    rewrite !opp_IZR, !Ropp_mult_distr_l_reverse, round_NE_opp.
    rewrite round_dyadic_real by lia. reflexivity.
Qed.

Definition align (mantissa exponent target : Z) : Z :=
  (mantissa * 2 ^ (exponent - target))%Z.

Lemma align_real mantissa exponent target :
  (target <= exponent)%Z ->
  IZR (align mantissa exponent target) * bpow radix2 target =
    IZR mantissa * bpow radix2 exponent.
Proof.
  intros HT. unfold align.
  change (IZR (mantissa * Zpower radix2 (exponent - target)) *
    bpow radix2 target = IZR mantissa * bpow radix2 exponent).
  rewrite mult_IZR, IZR_Zpower by lia.
  rewrite Rmult_assoc, <- bpow_plus.
  replace (exponent - target + target)%Z with exponent by lia. reflexivity.
Qed.

Definition add (x y : Z * Z) : Z * Z :=
  let exponent := Z.min (snd x) (snd y) in
  ((align (fst x) (snd x) exponent + align (fst y) (snd y) exponent)%Z,
    exponent).

Definition mul (x y : Z * Z) : Z * Z :=
  ((fst x * fst y)%Z, (snd x + snd y)%Z).

Lemma add_real x y : dyadic_real (add x y) = dyadic_real x + dyadic_real y.
Proof.
  unfold add, dyadic_real. cbn [fst snd].
  rewrite plus_IZR, Rmult_plus_distr_r.
  rewrite !align_real by lia. reflexivity.
Qed.

Lemma mul_real x y : dyadic_real (mul x y) = dyadic_real x * dyadic_real y.
Proof.
  unfold mul, dyadic_real. cbn [fst snd].
  rewrite mult_IZR, bpow_plus. ring.
Qed.

(** Equality of dyadic real values can be decided entirely with integers. *)
Definition equal (x y : Z * Z) : Prop :=
  let exponent := Z.min (snd x) (snd y) in
  align (fst x) (snd x) exponent = align (fst y) (snd y) exponent.

Theorem equal_iff_real x y : equal x y <-> dyadic_real x = dyadic_real y.
Proof.
  unfold equal, dyadic_real.
  pose proof (align_real (fst x) (snd x) (Z.min (snd x) (snd y))
    (Z.le_min_l _ _)) as HX.
  pose proof (align_real (fst y) (snd y) (Z.min (snd x) (snd y))
    (Z.le_min_r _ _)) as HY.
  split.
  - intros HE. rewrite <- HX, <- HY, HE. reflexivity.
  - intros HE. apply eq_IZR.
    apply Rmult_eq_reg_r with (bpow radix2 (Z.min (snd x) (snd y))).
    + now rewrite HX, HY.
    + apply Rgt_not_eq, bpow_gt_0.
Qed.

End IntegerRounding.
