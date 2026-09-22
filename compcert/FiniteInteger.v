(** A finite CompCert execution has a complete integer specification.

    The specification uses signed dyadics and a separate zero sign. It contains
    no real comparisons, abstract real rounding, or floating-point operations.
    Its correspondence with CompCert is proved here in Rocq. *)

From Coq Require Import Reals List ZArith Lia Lra.
From compcert Require Import Floats.
From Flocq Require Import Core Binary.
From QuadratureC Require Import FiniteArithmetic FiniteRepresentation IntegerRounding.

Import ListNotations Binary64Roundoff Binary64Representation.
Local Open Scope R_scope.
Module D := IntegerRounding.IntegerRounding.

Module Binary64Integer.

Definition exponent (magnitude : Z) : Z := Z.max (magnitude - 53) (-1074).

Lemma exponent_compcert : exponent = SpecFloat.fexp 53 1024.
Proof. reflexivity. Qed.

Definition decode (x : Floats.float) : Z * Z :=
  match x with
  | B754_finite _ _ negative mantissa exponent _ =>
      ((if negative then Zneg mantissa else Zpos mantissa), exponent)
  | _ => (0%Z, 0%Z)
  end.

Lemma decode_real x : D.dyadic_real (decode x) = real x.
Proof.
  destruct x as [s | s | s p h | s m e h];
    unfold decode, D.dyadic_real, real; cbn.
  - ring.
  - ring.
  - ring.
  - destruct s; reflexivity.
Qed.

Definition state := ((Z * Z) * bool)%type.
Definition encode (x : Floats.float) : state := (decode x, sign x).
Definition state_real (x : state) : R * bool := (D.dyadic_real (fst x), snd x).

Lemma encode_real x : state_real (encode x) = observe x.
Proof. unfold state_real, encode, observe. cbn [fst snd]. now rewrite decode_real. Qed.

Definition add_sign (sx sy : bool) (sum : Z * Z) : bool :=
  if (fst sum =? 0)%Z then andb sx sy else (fst sum <? 0)%Z.

Lemma add_sign_real sx sy sum :
  add_sign sx sy sum = addition_sign sx sy (D.dyadic_real sum).
Proof.
  unfold add_sign, addition_sign.
  destruct (Z.eqb_spec (fst sum) 0) as [HZ | HZ].
  - apply D.dyadic_real_zero in HZ. rewrite HZ.
    destruct (Req_EM_T 0 0); congruence.
  - assert (HR : D.dyadic_real sum <> 0).
    { intros HE. apply HZ. now apply D.dyadic_real_zero. }
    destruct (Req_EM_T (D.dyadic_real sum) 0); [contradiction |].
    destruct (Z.ltb_spec (fst sum) 0) as [HN | HN].
    + symmetry. apply Rlt_bool_true. now apply D.dyadic_real_negative.
    + symmetry. apply Rlt_bool_false.
      destruct (Rlt_dec (D.dyadic_real sum) 0) as [HL | HL]; [| lra].
      apply D.dyadic_real_negative in HL. lia.
Qed.

Definition add (x y : state) : state :=
  let exact := D.add (fst x) (fst y) in
  (D.round_signed exponent exact, add_sign (snd x) (snd y) exact).

Definition mul (x y : state) : state :=
  (D.round_signed exponent (D.mul (fst x) (fst y)), xorb (snd x) (snd y)).

Lemma add_real x y :
  state_real (add x y) = rounded_add (state_real x) (state_real y).
Proof.
  unfold state_real, add, rounded_add. cbn [fst snd].
  rewrite <- D.round_signed_real, add_sign_real, D.add_real.
  reflexivity.
Qed.

Lemma mul_real x y :
  state_real (mul x y) = rounded_mul (state_real x) (state_real y).
Proof.
  unfold state_real, mul, rounded_mul. cbn [fst snd].
  rewrite <- D.round_signed_real, D.mul_real. reflexivity.
Qed.

(** The proposition on the right contains only finite encodings and integers. *)
Definition represents (x : Floats.float) (value : state) : Prop :=
  finite x /\ sign x = snd value /\ D.equal (decode x) (fst value).

Lemma represents_iff_observe x value :
  represents x value <-> finite x /\ observe x = state_real value.
Proof.
  unfold represents, observe, state_real.
  rewrite D.equal_iff_real, decode_real.
  split.
  - intros [HF [HS HR]]. split; [exact HF | now rewrite HS, HR].
  - intros [HF HE]. inversion HE. auto.
Qed.

Theorem add_represents x y :
  finite x -> finite y -> finite (Float.add x y) ->
  represents (Float.add x y) (add (encode x) (encode y)).
Proof.
  intros HX HY HF. apply represents_iff_observe. split; [exact HF |].
  rewrite add_real, !encode_real. exact (observe_add x y HX HY HF).
Qed.

Theorem mul_represents x y :
  finite x -> finite y -> finite (Float.mul x y) ->
  represents (Float.mul x y) (mul (encode x) (encode y)).
Proof.
  intros HX HY HF. apply represents_iff_observe. split; [exact HF |].
  rewrite mul_real, !encode_real. exact (observe_mul x y HX HY HF).
Qed.

Theorem represents_unique x y value :
  represents x value -> represents y value -> x = y.
Proof.
  rewrite !represents_iff_observe. intros [HX HE] [HY HF].
  apply (observe_injective x y HX HY). now rewrite HE, HF.
Qed.

Theorem add_eq_iff radius x y z :
  radius <= max_value -> finite x -> finite y ->
  Rabs (real x + real y) <= radius ->
  (Float.add x y = z <-> represents z (add (encode x) (encode y))).
Proof.
  intros HM HX HY HB.
  pose proof (proj1 (add_bounded radius x y HM HX HY HB)) as HF.
  pose proof (add_represents x y HX HY HF) as HR.
  split; [intros <-; exact HR | intros HZ; eapply represents_unique; eauto].
Qed.

Theorem mul_eq_iff radius x y z :
  radius <= max_value -> finite x -> finite y ->
  Rabs (real x * real y) <= radius ->
  (Float.mul x y = z <-> represents z (mul (encode x) (encode y))).
Proof.
  intros HM HX HY HB.
  pose proof (proj1 (mul_bounded radius x y HM HX HY HB)) as HF.
  pose proof (mul_represents x y HX HY HF) as HR.
  split; [intros <-; exact HR | intros HZ; eapply represents_unique; eauto].
Qed.

Fixpoint sum (f : Floats.float -> Floats.float)
    (terms : list (Floats.float * Floats.float)) (initial : state) : state :=
  match terms with
  | [] => initial
  | t :: ts => sum f ts (add initial (mul (encode (fst t)) (encode (f (snd t)))))
  end.

Lemma sum_real f terms initial :
  state_real (sum f terms initial) = signed_sum f terms (state_real initial).
Proof.
  revert initial. induction terms as [| t ts IH]; intros initial.
  - reflexivity.
  - cbn [sum signed_sum]. rewrite IH, add_real, mul_real, !encode_real.
    reflexivity.
Qed.

Theorem integrate_represents radius f terms initial :
  radius <= max_value -> finite initial ->
  (forall t, In t terms -> finite (fst t) /\ finite (f (snd t))) ->
  Rabs (real initial) + product_mass f terms +
    2 * INR (length terms) * epsilon radius <= radius ->
  represents (integrate f terms initial) (sum f terms (encode initial)).
Proof.
  intros HM HI HT HB.
  apply represents_iff_observe.
  rewrite sum_real, encode_real.
  exact (observe_integrate_bounded radius f terms initial HM HI HT HB).
Qed.

Theorem integrate_eq_iff radius f terms initial z :
  radius <= max_value -> finite initial ->
  (forall t, In t terms -> finite (fst t) /\ finite (f (snd t))) ->
  Rabs (real initial) + product_mass f terms +
    2 * INR (length terms) * epsilon radius <= radius ->
  (integrate f terms initial = z <->
    represents z (sum f terms (encode initial))).
Proof.
  intros HM HI HT HB.
  pose proof (integrate_represents radius f terms initial HM HI HT HB) as HR.
  split; [intros <-; exact HR | intros HZ; eapply represents_unique; eauto].
Qed.

End Binary64Integer.
