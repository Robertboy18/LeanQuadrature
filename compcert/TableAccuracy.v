From Coq Require Import Reals List Lia Psatz.
From Flocq Require Import Core Binary.
From compcert Require Import Floats.
From QuadratureC Require Import ClightRules FiniteArithmetic.

Import ListNotations Binary64Roundoff.
Local Open Scope R_scope.

(** Real reference rules and certified errors of the actual C initializers.
    The reference rules have positive weights and the required moments. The
    decoded lists below are proved equal to CompCert's values read from the
    pinned AST; they are not replacements for those initializers. *)
Module Binary64TableAccuracy.

Definition two_node := sqrt (1 / 3).
Definition three_node := sqrt (3 / 5).
Definition four_radical := sqrt 30.
Definition four_inner := sqrt ((15 - 2 * four_radical) / 35).
Definition four_outer := sqrt ((15 + 2 * four_radical) / 35).

Definition ideal_nodes r : list R :=
  match r with
  | One => [0]
  | Two => [-two_node; two_node]
  | Three => [-three_node; 0; three_node]
  | Four => [-four_outer; -four_inner; four_inner; four_outer]
  end.
Definition ideal_weights r : list R :=
  match r with
  | One => [2]
  | Two => [1; 1]
  | Three => [5/9; 8/9; 5/9]
  | Four => [(18-four_radical)/36; (18+four_radical)/36;
      (18+four_radical)/36; (18-four_radical)/36]
  end.
Definition ideal_node r i := nth i (ideal_nodes r) 0.
Definition ideal_weight r i := nth i (ideal_weights r) 0.
Definition ideal_value g r :=
  fold_right (fun i acc => ideal_weight r i * g (ideal_node r i) + acc)
    0 (seq 0 (rule_size r)).
(** Uniform absolute tolerances for orders one through four. The weight
    tolerance includes the C three-point literal, which differs from the
    functional model in the draft. *)
Definition node_tolerance : R := 1 / 10000000000000000.
Definition weight_tolerance : R := 5 / 10000000000000000.

Definition decoded_nodes r : list R :=
  match r with
  | One => [0]
  | Two => [-1300077228592327/2251799813685248; 1300077228592327/2251799813685248]
  | Three => [-872118317739593/1125899906842624; 0; 872118317739593/1125899906842624]
  | Four => [-7756426344020357/9007199254740992; -1531138501201791/4503599627370496;
      1531138501201791/4503599627370496; 7756426344020357/9007199254740992]
  end.
Definition decoded_weights r : list R :=
  match r with
  | One => [2]
  | Two => [1; 1]
  | Three => [2501999792983611/4503599627370496; 8006399337547549/9007199254740992;
      2501999792983611/4503599627370496]
  | Four => [6266395803760235/18014398509481984; 5874001352860875/9007199254740992;
      5874001352860875/9007199254740992; 6266395803760235/18014398509481984]
  end.

(** Reduce the binary64 representation, then interpret the resulting finite
    dyadic as an exact rational. All reduction is checked by Rocq. *)
Ltac decode_table_real :=
  unfold real;
  match goal with |- B2R _ _ ?v = ?rhs =>
    let w := eval vm_compute in v in change (B2R 53 1024 w = rhs) end;
  cbn [B2R]; try reflexivity;
  unfold Defs.F2R; cbn [Fnum Fexp SpecFloat.cond_Zopp];
  try change (bpow radix2 (-51)) with (/ 2251799813685248);
  try change (bpow radix2 (-52)) with (/ 4503599627370496);
  try change (bpow radix2 (-53)) with (/ 9007199254740992);
  try change (bpow radix2 (-54)) with (/ 18014398509481984);
  rewrite ?opp_IZR; field.

Lemma rule_node_real r i (HI : (i < rule_size r)%nat) :
  real (rule_node r i) = nth i (decoded_nodes r) 0.
Proof.
  destruct r; cbn [rule_size] in HI; enumerate_index i.
  all: cbn [decoded_nodes nth]; decode_table_real.
Qed.

Lemma rule_weight_real r i (HI : (i < rule_size r)%nat) :
  real (rule_weight r i) = nth i (decoded_weights r) 0.
Proof.
  destruct r; cbn [rule_size] in HI; enumerate_index i.
  all: cbn [decoded_weights nth]; decode_table_real.
Qed.

Lemma two_node_spec : 0 <= two_node /\ two_node ^ 2 = 1/3.
Proof.
  unfold two_node. split; [apply sqrt_pos |].
  pose proof (sqrt_def (1/3) (ltac:(lra))). nra.
Qed.

Lemma three_node_spec : 0 <= three_node /\ three_node ^ 2 = 3/5.
Proof.
  unfold three_node. split; [apply sqrt_pos |].
  pose proof (sqrt_def (3/5) (ltac:(lra))). nra.
Qed.

Lemma four_radical_spec : 0 <= four_radical /\ four_radical ^ 2 = 30.
Proof.
  unfold four_radical. split; [apply sqrt_pos |].
  pose proof (sqrt_def 30 (ltac:(lra))). nra.
Qed.

Lemma four_radical_bounds : 0 <= four_radical <= 6.
Proof. pose proof four_radical_spec. nra. Qed.

Lemma four_inner_spec : 0 <= four_inner /\ four_inner ^ 2 = (15-2*four_radical)/35.
Proof.
  pose proof four_radical_bounds as HR.
  unfold four_inner. split; [apply sqrt_pos |].
  pose proof (sqrt_def ((15-2*four_radical)/35) (ltac:(lra))). nra.
Qed.

Lemma four_outer_spec : 0 <= four_outer /\ four_outer ^ 2 = (15+2*four_radical)/35.
Proof.
  pose proof four_radical_bounds as HR.
  unfold four_outer. split; [apply sqrt_pos |].
  pose proof (sqrt_def ((15+2*four_radical)/35) (ltac:(lra))). nra.
Qed.

(** A rational enclosure of sqrt(30) sufficient for all four-point entries. *)
Lemma four_radical_tight :
  5477225575051661134/1000000000000000000 <= four_radical <=
  5477225575051661135/1000000000000000000.
Proof. pose proof four_radical_spec. nra. Qed.

Lemma rule_node_finite r i (HI : (i < rule_size r)%nat) : finite (rule_node r i).
Proof.
  destruct r; cbn [rule_size] in HI; enumerate_index i.
  all: vm_compute; reflexivity.
Qed.

Lemma rule_node_interval r i (HI : (i < rule_size r)%nat) :
  -1 <= real (rule_node r i) <= 1.
Proof.
  rewrite (rule_node_real r i HI).
  destruct r; cbn [rule_size] in HI; enumerate_index i.
  all: cbn [decoded_nodes nth]; lra.
Qed.

Lemma ideal_node_interval r i (HI : (i < rule_size r)%nat) :
  -1 <= ideal_node r i <= 1.
Proof.
  pose proof two_node_spec. pose proof three_node_spec.
  pose proof four_inner_spec. pose proof four_outer_spec.
  pose proof four_radical_bounds.
  destruct r; cbn [rule_size] in HI; enumerate_index i.
  all: cbn [ideal_node ideal_nodes nth]; nra.
Qed.

Lemma rule_node_error r i (HI : (i < rule_size r)%nat) :
  Rabs (real (rule_node r i) - ideal_node r i) <= node_tolerance.
Proof.
  rewrite (rule_node_real r i HI).
  pose proof two_node_spec. pose proof three_node_spec.
  pose proof four_inner_spec. pose proof four_outer_spec.
  pose proof four_radical_tight.
  destruct r; cbn [rule_size] in HI; enumerate_index i.
  all: cbn [decoded_nodes ideal_node ideal_nodes nth]; unfold node_tolerance;
    apply Rabs_le; nra.
Qed.

Lemma rule_weight_error r i (HI : (i < rule_size r)%nat) :
  Rabs (real (rule_weight r i) - ideal_weight r i) <= weight_tolerance.
Proof.
  rewrite (rule_weight_real r i HI). pose proof four_radical_tight.
  destruct r; cbn [rule_size] in HI; enumerate_index i.
  all: cbn [decoded_weights ideal_weight ideal_weights nth]; unfold weight_tolerance;
    apply Rabs_le; lra.
Qed.

Lemma ideal_weight_positive r i (HI : (i < rule_size r)%nat) :
  0 < ideal_weight r i.
Proof.
  pose proof four_radical_bounds.
  destruct r; cbn [rule_size] in HI; enumerate_index i.
  all: cbn [ideal_weight ideal_weights nth]; lra.
Qed.

Lemma ideal_weights_sum r :
  fold_right (fun i acc => ideal_weight r i + acc) 0 (seq 0 (rule_size r)) = 2.
Proof.
  destruct r; cbn [rule_size seq fold_right ideal_weight ideal_weights nth]; field.
Qed.

(** Each n-point real rule has the moments of integration over [-1,1]
    through degree 2*n-1. The higher-power identities make the four-point
    calculation a polynomial consequence of the defining square roots. *)
Lemma ideal_moment r k (HK : (k < 2 * rule_size r)%nat) :
  ideal_value (fun x => x ^ k) r =
    if Nat.even k then 2 / INR (S k) else 0.
Proof.
  pose proof two_node_spec as [_ HT]. pose proof three_node_spec as [_ HH].
  pose proof four_inner_spec as [_ HI]. pose proof four_outer_spec as [_ HO].
  pose proof four_radical_spec as [_ HR].
  assert (HI4 : four_inner ^ 4 = ((15-2*four_radical)/35)^2).
  { replace (four_inner ^ 4) with ((four_inner ^ 2)^2) by ring. now rewrite HI. }
  assert (HO4 : four_outer ^ 4 = ((15+2*four_radical)/35)^2).
  { replace (four_outer ^ 4) with ((four_outer ^ 2)^2) by ring. now rewrite HO. }
  assert (HI6 : four_inner ^ 6 = ((15-2*four_radical)/35)^3).
  { replace (four_inner ^ 6) with ((four_inner ^ 2)^3) by ring. now rewrite HI. }
  assert (HO6 : four_outer ^ 6 = ((15+2*four_radical)/35)^3).
  { replace (four_outer ^ 6) with ((four_outer ^ 2)^3) by ring. now rewrite HO. }
  assert (HR4 : four_radical ^ 4 = 900).
  { replace (four_radical ^ 4) with ((four_radical ^ 2)^2) by ring. rewrite HR. ring. }
  destruct r; cbn [rule_size] in HK; enumerate_index k.
  all: cbn [ideal_value rule_size seq fold_right ideal_node ideal_nodes
    ideal_weight ideal_weights nth Nat.even pow INR].
  all: nra.
Qed.

(** The paper's absolute 2^(-53) tolerance is false for the pinned C weight.
    This statement uses the initialized value, not the draft's model literal. *)
Theorem three_weight_exceeds_draft_tolerance :
  ~ Rabs (real (rule_weight Three 0) - 5/9) <= 1 / 9007199254740992.
Proof.
  rewrite (rule_weight_real Three 0 (ltac:(cbn [rule_size]; lia))).
  cbn [decoded_weights nth]. intros H. apply Rabs_le_inv in H. lra.
Qed.

End Binary64TableAccuracy.
