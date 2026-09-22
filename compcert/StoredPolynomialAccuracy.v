From Coq Require Import Reals Lra List ZArith Lia String.
From Flocq Require Import Core.Zaux Core.Raux IEEE754.Binary.
From compcert Require Import Integers Floats Values Events Smallstep Behaviors Clight.
From QuadratureC Require Import StoredPolynomialRules FiniteArithmetic
  ValueAccuracy ExampleIntegral PolynomialRulesAccuracy.

Import ListNotations Binary64Roundoff.
Local Open Scope R_scope.
Module App := StoredPolynomialRules.

Definition result_bits (n : nat) : Z :=
  match n with
  | 1%nat => 4607182418800017408
  | 2%nat => 4605722458335229421
  | 3%nat => 4605754793695682580
  | 4%nat => 4605754515107373863
  | 5%nat => 4605754516376088390
  | 6%nat => 4605754516372517428
  | 7%nat => 4605754516372524257
  | 8%nat => 4605754516372524238
  | 9%nat => 4605754516372524239
  | 10%nat => 4605754516372524244
  | _ => 0
  end.
Definition result_real (n : nat) : R :=
  match n with
  | 1%nat => 4503599627370496 / 4503599627370496
  | 2%nat => 7547238789953005 / 9007199254740992
  | 3%nat => 7579574150406164 / 9007199254740992
  | 4%nat => 7579295562097447 / 9007199254740992
  | 5%nat => 7579296830811974 / 9007199254740992
  | 6%nat => 7579296827241012 / 9007199254740992
  | 7%nat => 7579296827247841 / 9007199254740992
  | 8%nat => 7579296827247822 / 9007199254740992
  | 9%nat => 7579296827247823 / 9007199254740992
  | 10%nat => 7579296827247828 / 9007199254740992
  | _ => 0
  end.
Definition error_bound (n : nat) : R :=
  match n with
  | 1%nat => 159 / 1000
  | 2%nat => 89 / 25000
  | 3%nat => 31 / 1000000
  | 4%nat => 3 / 20000000
  | 5%nat => 1 / 2500000000
  | 6%nat => 1 / 1250000000000
  | 7%nat => 1 / 500000000000000
  | 8%nat => 1 / 250000000000000
  | 9%nat => 1 / 250000000000000
  | 10%nat => 3 / 1000000000000000
  | _ => 0
  end.

Ltac positive_stored_cases n :=
  let Hcases := fresh "Hcases" in
  assert (Hcases : n = 1%nat \/ n = 2%nat \/ n = 3%nat \/ n = 4%nat \/ n = 5%nat \/ n = 6%nat \/ n = 7%nat \/ n = 8%nat \/ n = 9%nat \/ n = 10%nat) by lia;
  repeat match type of Hcases with
  | _ \/ _ => destruct Hcases as [Hcases | Hcases]
  end; subst n.

Theorem result_value_bits n (hlo : (1 <= n)%nat) (hhi : (n <= 10)%nat) :
  Float.to_bits (App.result_value n) = Int64.repr (result_bits n).
Proof. positive_stored_cases n; vm_compute; reflexivity. Qed.

Theorem result_value_real n (hlo : (1 <= n)%nat) (hhi : (n <= 10)%nat) :
  real (App.result_value n) = result_real n.
Proof.
  rewrite <- (Float.of_to_bits (App.result_value n)), (result_value_bits n hlo hhi).
  positive_stored_cases n; reflexivity.
Qed.

Theorem result_value_finite n (hlo : (1 <= n)%nat) (hhi : (n <= 10)%nat) :
  finite (App.result_value n).
Proof.
  rewrite <- (Float.of_to_bits (App.result_value n)), (result_value_bits n hlo hhi).
  positive_stored_cases n; reflexivity.
Qed.

(** An independent rational enclosure fine enough for every stored application. *)
Lemma sin_one_decimal_enclosure :
  8414709848078965 / 10000000000000000 <= sin 1 <=
  8414709848078966 / 10000000000000000.
Proof.
  assert (H0 : 0 <= 1) by lra.
  assert (H4 : 1 <= 4) by lra.
  pose proof (pre_sin_bound 1 4 H0 H4) as H.
  change (sin_approx 1 9 <= sin 1 <= sin_approx 1 10) in H.
  replace (sin_approx 1 9) with (102360822438075317 / 121645100408832000) in H.
  2: {
    unfold sin_approx, sin_term.
    cbn [sum_f_R0 Nat.mul Nat.add].
    rewrite !factorial_real_step.
    cbn [fact pow INR]. field.
  }
  replace (sin_approx 1 10) with (42991545423991633141 / 51090942171709440000) in H.
  2: {
    unfold sin_approx, sin_term.
    cbn [sum_f_R0 Nat.mul Nat.add].
    rewrite !factorial_real_step.
    cbn [fact pow INR]. field.
  }
  lra.
Qed.

Theorem result_value_accuracy n (hlo : (1 <= n)%nat) (hhi : (n <= 10)%nat) :
  Rabs (real (App.result_value n) - sin 1) <= error_bound n.
Proof.
  rewrite (result_value_real n hlo hhi). pose proof sin_one_decimal_enclosure.
  positive_stored_cases n; cbn [result_real error_bound]; apply Rabs_le; lra.
Qed.

Theorem result_integral_accuracy n (hlo : (1 <= n)%nat) (hhi : (n <= 10)%nat)
    (pr : Riemann_integrable integrand (-1) 1) :
  Rabs (real (App.result_value n) - RiemannInt pr) <= error_bound n.
Proof. rewrite integral_value. exact (result_value_accuracy n hlo hhi). Qed.

Definition accurate_behavior n beh : Prop :=
  exists value : Floats.float,
    beh = Terminates [Event_annot "quadrature-result" [EVfloat value]] Int.zero /\
    finite value /\
    forall pr : Riemann_integrable integrand (-1) 1,
      Rabs (real value - RiemannInt pr) <= error_bound n.

Theorem result_behavior_accurate n (hlo : (1 <= n)%nat) (hhi : (n <= 10)%nat) :
  accurate_behavior n (Terminates (App.result_trace n) Int.zero).
Proof.
  exists (App.result_value n). split; [reflexivity |].
  split; [exact (result_value_finite n hlo hhi) | exact (result_integral_accuracy n hlo hhi)].
Qed.

Theorem source_application_accuracy n (hlo : (1 <= n)%nat) (hhi : (n <= 10)%nat) beh :
  program_behaves (Clight.semantics2 (App.application n)) beh ->
  accurate_behavior n beh.
Proof.
  intro H. rewrite (App.application_all_behaviors n hhi beh H).
  exact (result_behavior_accurate n hlo hhi).
Qed.
