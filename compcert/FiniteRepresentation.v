(** Complete observations of finite CompCert binary64 values.

    Real decoding and the sign bit jointly determine a finite encoding. Flocq's
    operation theorems give the corresponding signed rounding specifications.
    The range budget in FiniteArithmetic discharges finiteness for the loop, so
    its signed recurrence characterizes the complete result. No Lean theorem or
    correspondence between Lean and Rocq representations is assumed here. *)

From Coq Require Import Reals List Lra.
From compcert Require Import Floats.
From Flocq Require Import Core Binary.
From QuadratureC Require Import FiniteArithmetic.

Import ListNotations Binary64Roundoff.
Local Open Scope R_scope.
Local Transparent Float.add Float.mul.

Module Binary64Representation.

Definition sign (x : Floats.float) : bool := Bsign 53 1024 x.
Definition observe (x : Floats.float) : R * bool := (real x, sign x).

Definition addition_sign (sx sy : bool) (sum : R) : bool :=
  if Req_EM_T sum 0 then andb sx sy else Rlt_bool sum 0.

Definition rounded_add (x y : R * bool) : R * bool :=
  (nearest (fst x + fst y), addition_sign (snd x) (snd y) (fst x + fst y)).
Definition rounded_mul (x y : R * bool) : R * bool :=
  (nearest (fst x * fst y), xorb (snd x) (snd y)).

Theorem observe_injective x y :
  finite x -> finite y -> observe x = observe y -> x = y.
Proof.
  intros HX HY HE.
  apply (B2R_Bsign_inj 53 1024 x y HX HY).
  - exact (f_equal (@fst R bool) HE).
  - exact (f_equal (@snd R bool) HE).
Qed.

Lemma addition_sign_compare sx sy sum :
  addition_sign sx sy sum =
  match Rcompare sum 0 with Eq => andb sx sy | Lt => true | Gt => false end.
Proof.
  unfold addition_sign. destruct (Req_EM_T sum 0) as [HZ | HZ].
  - rewrite (Rcompare_Eq _ _ HZ). reflexivity.
  - destruct (Rlt_dec sum 0) as [HN | HN].
    + rewrite (Rcompare_Lt _ _ HN), (Rlt_bool_true _ _ HN). reflexivity.
    + assert (HP : 0 < sum) by lra.
      rewrite (Rcompare_Gt _ _ HP), (Rlt_bool_false _ _ (Rlt_le _ _ HP)). reflexivity.
Qed.

Theorem observe_add x y :
  finite x -> finite y -> finite (Float.add x y) ->
  observe (Float.add x y) = rounded_add (observe x) (observe y).
Proof.
  intros HX HY HF.
  pose proof (Bplus_correct 53 1024 eq_refl eq_refl
    Float.binop_nan BinarySingleNaN.mode_NE x y HX HY) as H.
  change (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) with ZnearestE in H.
  change (B2R 53 1024 x) with (real x) in H.
  change (B2R 53 1024 y) with (real y) in H.
  fold nearest in H.
  destruct (Rlt_bool (Rabs (nearest (real x + real y))) (bpow radix2 1024)).
  - destruct H as [HE [_ HS]].
    unfold observe, rounded_add. cbn [fst snd].
    rewrite addition_sign_compare.
    f_equal; assumption.
  - destruct H as [HO _].
    change (B2FF 53 1024 (Float.add x y) =
      Binary.binary_overflow 53 1024 BinarySingleNaN.mode_NE
        (sign x)) in HO.
    unfold finite in HF.
    destruct (Float.add x y); cbn in HF, HO; discriminate.
Qed.

Theorem observe_mul x y :
  finite x -> finite y -> finite (Float.mul x y) ->
  observe (Float.mul x y) = rounded_mul (observe x) (observe y).
Proof.
  intros HX HY HF.
  pose proof (Bmult_correct 53 1024 eq_refl eq_refl
    Float.binop_nan BinarySingleNaN.mode_NE x y) as H.
  change (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) with ZnearestE in H.
  change (B2R 53 1024 x) with (real x) in H.
  change (B2R 53 1024 y) with (real y) in H.
  fold nearest in H.
  destruct (Rlt_bool (Rabs (nearest (real x * real y))) (bpow radix2 1024)).
  - destruct H as [HE [_ HS]].
    assert (HN : is_nan 53 1024 (Float.mul x y) = false).
    { unfold finite in HF. destruct (Float.mul x y); cbn in *; congruence. }
    specialize (HS HN).
    unfold observe, rounded_mul. cbn [fst snd]. f_equal; assumption.
  - change (B2FF 53 1024 (Float.mul x y) =
      Binary.binary_overflow 53 1024 BinarySingleNaN.mode_NE
        (xorb (sign x) (sign y))) in H.
    unfold finite in HF.
    destruct (Float.mul x y); cbn in HF, H; discriminate.
Qed.

(** These specifications contain no executable addition or multiplication on
    their right-hand sides. The magnitude bound proves the result finite. *)
Theorem add_eq_iff radius x y z :
  radius <= max_value -> finite x -> finite y ->
  Rabs (real x + real y) <= radius ->
  (Float.add x y = z <->
    finite z /\ observe z = rounded_add (observe x) (observe y)).
Proof.
  intros HM HX HY HB.
  pose proof (proj1 (add_bounded radius x y HM HX HY HB)) as HF.
  pose proof (observe_add x y HX HY HF) as HO.
  split.
  - intros <-. auto.
  - intros [HZ HE]. apply (observe_injective _ _ HF HZ).
    rewrite HO. symmetry. exact HE.
Qed.

Theorem mul_eq_iff radius x y z :
  radius <= max_value -> finite x -> finite y ->
  Rabs (real x * real y) <= radius ->
  (Float.mul x y = z <->
    finite z /\ observe z = rounded_mul (observe x) (observe y)).
Proof.
  intros HM HX HY HB.
  pose proof (proj1 (mul_bounded radius x y HM HX HY HB)) as HF.
  pose proof (observe_mul x y HX HY HF) as HO.
  split.
  - intros <-. auto.
  - intros [HZ HE]. apply (observe_injective _ _ HF HZ).
    rewrite HO. symmetry. exact HE.
Qed.

(** Every operation retains its sign, including a product that underflows. *)
Fixpoint signed_sum (f : Floats.float -> Floats.float)
    (terms : list (Floats.float * Floats.float)) (initial : R * bool) : R * bool :=
  match terms with
  | [] => initial
  | t :: ts => signed_sum f ts
      (rounded_add initial (rounded_mul (observe (fst t)) (observe (f (snd t)))))
  end.

Theorem observe_integrate_finite f terms initial :
  finite_steps f terms initial ->
  (forall t, In t terms -> finite (fst t) /\ finite (f (snd t))) ->
  observe (integrate f terms initial) = signed_sum f terms (observe initial).
Proof.
  revert initial. induction terms as [| t ts IH]; intros initial HS HF.
  - reflexivity.
  - destruct HS as [HI [HP HR]].
    destruct (HF t (or_introl eq_refl)) as [HW HY].
    assert (HN : finite (Float.add initial (Float.mul (fst t) (f (snd t))))).
    { destruct ts; exact (proj1 HR). }
    change (observe (integrate f ts (Float.add initial (Float.mul (fst t) (f (snd t))))) =
      signed_sum f ts
        (rounded_add (observe initial) (rounded_mul (observe (fst t)) (observe (f (snd t)))))).
    rewrite (IH _ HR (fun u HU => HF u (or_intror HU))).
    rewrite (observe_add _ _ HI HP HN), (observe_mul _ _ HW HY HP).
    reflexivity.
Qed.

Theorem observe_integrate_bounded radius f terms initial :
  radius <= max_value ->
  finite initial ->
  (forall t, In t terms -> finite (fst t) /\ finite (f (snd t))) ->
  Rabs (real initial) + product_mass f terms +
    2 * INR (length terms) * epsilon radius <= radius ->
  finite (integrate f terms initial) /\
  observe (integrate f terms initial) = signed_sum f terms (observe initial).
Proof.
  intros HM HI HF HB.
  destruct (integrate_bounded radius f terms initial HM HI HF HB)
    as [HS [HFIN _]].
  split; [exact HFIN | exact (observe_integrate_finite f terms initial HS HF)].
Qed.

Theorem integrate_eq_iff radius f terms initial z :
  radius <= max_value ->
  finite initial ->
  (forall t, In t terms -> finite (fst t) /\ finite (f (snd t))) ->
  Rabs (real initial) + product_mass f terms +
    2 * INR (length terms) * epsilon radius <= radius ->
  (integrate f terms initial = z <->
    finite z /\ observe z = signed_sum f terms (observe initial)).
Proof.
  intros HM HI HF HB.
  destruct (observe_integrate_bounded radius f terms initial HM HI HF HB) as [HN HO].
  split.
  - intros <-. auto.
  - intros [HZ HE]. apply (observe_injective _ _ HN HZ).
    rewrite HO. symmetry. exact HE.
Qed.

End Binary64Representation.
