From Coq Require Import Reals Lra.
From Flocq Require Import Core.Zaux Core.Raux IEEE754.Binary.
From compcert Require Import Floats.
From QuadratureC Require Import ClightExample.

Local Open Scope R_scope.

(** Decode the actual CompCert result independently of the Lean certificate. *)
Lemma cosine_value_real :
  B2R 53 1024 cosine_value = 7547238789953005 / 9007199254740992.
Proof.
  change (IZR 7547238789953005 * bpow radix2 (-53) =
    7547238789953005 / 9007199254740992).
  change (7547238789953005 * / 9007199254740992 =
    7547238789953005 / 9007199254740992).
  reflexivity.
Qed.

Lemma factorial_real_step n :
  INR (fact (S n)) = INR (S n) * INR (fact n).
Proof.
  change (INR (S n * fact n) = INR (S n) * INR (fact n)).
  apply mult_INR.
Qed.

Lemma sin_one_enclosure :
  4241 / 5040 <= sin 1 <= 305353 / 362880.
Proof.
  assert (H0 : 0 <= 1) by lra.
  assert (H4 : 1 <= 4) by lra.
  pose proof (pre_sin_bound 1 1 H0 H4) as H.
  change (sin_approx 1 3 <= sin 1 <= sin_approx 1 4) in H.
  replace (sin_approx 1 3) with (4241 / 5040) in H.
  2: {
    unfold sin_approx, sin_term.
    cbn [sum_f_R0 Nat.mul Nat.add].
    rewrite !factorial_real_step.
    cbn [fact pow INR].
    field.
  }
  replace (sin_approx 1 4) with (305353 / 362880) in H.
  2: {
    unfold sin_approx, sin_term.
    cbn [sum_f_R0 Nat.mul Nat.add].
    rewrite !factorial_real_step.
    cbn [fact pow INR].
    field.
  }
  exact H.
Qed.

Theorem cosine_value_accuracy :
  Rabs (B2R 53 1024 cosine_value - sin 1) <= 356 / 100000.
Proof.
  rewrite cosine_value_real.
  pose proof sin_one_enclosure.
  apply Rabs_le. lra.
Qed.

Theorem cosine_value_draft_bound_false :
  ~ Rabs (B2R 53 1024 cosine_value - sin 1) <= 224 / 100000.
Proof.
  rewrite cosine_value_real.
  pose proof sin_one_enclosure as HS.
  intros H. apply Rabs_le_inv in H. lra.
Qed.

Print Assumptions cosine_value_real.
Print Assumptions sin_one_enclosure.
Print Assumptions cosine_value_accuracy.
Print Assumptions cosine_value_draft_bound_false.
