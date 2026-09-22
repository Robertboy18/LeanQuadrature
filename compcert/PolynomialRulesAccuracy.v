From Coq Require Import Reals Lra List ZArith String.
From Flocq Require Import Core.Zaux Core.Raux IEEE754.Binary.
From compcert Require Import Integers Floats Values Events Smallstep Behaviors Clight.
From QuadratureC Require Import ClightRules PolynomialRules FiniteArithmetic
  ValueAccuracy ExampleIntegral.

Import ListNotations Binary64Roundoff.
Local Open Scope R_scope.
Module App := PolynomialRules.

Definition result_bits r : Z :=
  match r with
  | One => 4607182418800017408
  | Two => 4605722458335229421
  | Three => 4605754793695682580
  | Four => 4605754515107373863
  end.
Definition result_real r : R :=
  match r with
  | One => 4503599627370496 / 4503599627370496
  | Two => 7547238789953005 / 9007199254740992
  | Three => 7579574150406164 / 9007199254740992
  | Four => 7579295562097447 / 9007199254740992
  end.
Definition error_bound r : R :=
  match r with
  | One => 159 / 1000
  | Two => 356 / 100000
  | Three => 31 / 1000000
  | Four => 15 / 100000000
  end.

Theorem result_value_bits r :
  Float.to_bits (App.result_value r) = Int64.repr (result_bits r).
Proof. destruct r; vm_compute; reflexivity. Qed.

Theorem result_value_real r : real (App.result_value r) = result_real r.
Proof.
  rewrite <- (Float.of_to_bits (App.result_value r)), result_value_bits.
  destruct r.
  - change (4503599627370496 * /4503599627370496 =
      4503599627370496 / 4503599627370496). reflexivity.
  - change (7547238789953005 * /9007199254740992 =
      7547238789953005 / 9007199254740992). reflexivity.
  - change (7579574150406164 * /9007199254740992 =
      7579574150406164 / 9007199254740992). reflexivity.
  - change (7579295562097447 * /9007199254740992 =
      7579295562097447 / 9007199254740992). reflexivity.
Qed.

Theorem result_value_finite r : finite (App.result_value r).
Proof.
  rewrite <- (Float.of_to_bits (App.result_value r)), result_value_bits.
  destruct r; reflexivity.
Qed.

(** This sharper enclosure resolves the four-point error, which is smaller
    than the width of the earlier two-point certificate's sine enclosure. *)
Lemma sin_one_tight_enclosure :
  1100370038249 / 1307674368000 <= sin 1 <=
  23023126954133 / 27360571392000.
Proof.
  assert (H0 : 0 <= 1) by lra.
  assert (H4 : 1 <= 4) by lra.
  pose proof (pre_sin_bound 1 3 H0 H4) as H.
  change (sin_approx 1 7 <= sin 1 <= sin_approx 1 8) in H.
  replace (sin_approx 1 7) with (1100370038249 / 1307674368000) in H.
  2: {
    unfold sin_approx, sin_term.
    cbn [sum_f_R0 Nat.mul Nat.add].
    rewrite !factorial_real_step.
    cbn [fact pow INR]. field.
  }
  replace (sin_approx 1 8) with (23023126954133 / 27360571392000) in H.
  2: {
    unfold sin_approx, sin_term.
    cbn [sum_f_R0 Nat.mul Nat.add].
    rewrite !factorial_real_step.
    cbn [fact pow INR]. field.
  }
  exact H.
Qed.

Theorem result_value_accuracy r :
  Rabs (real (App.result_value r) - sin 1) <= error_bound r.
Proof.
  rewrite result_value_real. pose proof sin_one_tight_enclosure.
  destruct r; cbn [result_real error_bound]; apply Rabs_le; lra.
Qed.

Theorem result_integral_accuracy r
    (pr : Riemann_integrable integrand (-1) 1) :
  Rabs (real (App.result_value r) - RiemannInt pr) <= error_bound r.
Proof. rewrite integral_value. apply result_value_accuracy. Qed.

Definition accurate_behavior r beh : Prop :=
  exists value : Floats.float,
    beh = Terminates [Event_annot "quadrature-result" [EVfloat value]] Int.zero /\
    finite value /\
    forall pr : Riemann_integrable integrand (-1) 1,
      Rabs (real value - RiemannInt pr) <= error_bound r.

Theorem result_behavior_accurate r :
  accurate_behavior r (Terminates (App.result_trace r) Int.zero).
Proof.
  exists (App.result_value r). split; [reflexivity |].
  split; [apply result_value_finite | apply result_integral_accuracy].
Qed.

Theorem source_application_accuracy r beh :
  program_behaves (Clight.semantics2 (App.application r)) beh ->
  accurate_behavior r beh.
Proof.
  intro H. rewrite (App.application_all_behaviors r beh H).
  apply result_behavior_accurate.
Qed.
