(* The first theorem checks the counterexample using MathComp-Analysis alone.
   The second deliberately invokes the original admitted lemma to exhibit its
   inconsistency. Neither theorem is imported by our program certificates. *)
From mathcomp Require Import all_boot ssralg ssrnum archimedean finfun order.
From mathcomp Require Import all_algebra all_field all_analysis all_reals.
From CFEM Require Import quadrature.

Import Order.TTheory GRing.Theory Num.Theory GRing classical_sets.
Import numFieldNormedType.Exports.
Local Open Scope ring_scope.

Lemma singleton_interval_positivity_counterexample (R : realType) :
  {in `[0, 0]%classic, continuous (fun _ : R => (1 : R))} /\
  {in `[0, 0]%classic, forall _ : R, is_true (0 <= (1 : R))} /\
  (~ {in `[0, 0]%classic, forall _ : R, is_true ((1 : R) == 0)}) /\
  ~ (0 < \int[lebesgue_measure]_(x in `[0, 0]) (1 : R)).
Proof.
  split; first by move=> x _; exact: cst_continuous.
  split; first by move=> x _; exact: ler01.
  split.
  - move=> h.
    have h0 : (0 : R) \in `[0, 0]%classic by rewrite set_itv1 inE.
    by move: (h 0 h0); rewrite oner_eq0.
  - by rewrite set_itv1 Rintegral_set1 ltxx.
Qed.

(* This is a diagnostic of the original assumption, not an independent proof
   of False. Its assumption report must retain exactly that admitted lemma
   and the logical axioms already present in its statement. *)
Lemma admitted_positivity_is_inconsistent (R : realType) : Logic.False.
Proof.
  have [hc [hn [hne hz]]] := singleton_interval_positivity_counterexample R.
  exact: (hz (@quadrature.Rintegral_gt_0 R 0 0 (fun _ : R => (1 : R)) hc hn hne)).
Qed.

Print Assumptions singleton_interval_positivity_counterexample.
Print Assumptions admitted_positivity_is_inconsistent.
