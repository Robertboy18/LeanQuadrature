From Coq Require Import List Arith.
From compcert Require Import Floats.
From QuadratureC Require Import ClightRules.

Import ListNotations.

(** All stored slices of the original tables. The execution theorems separately
    require at most ten nodes; these functional definitions also describe zero. *)
Definition stored_table_index (n i : nat) : nat := n * (n - 1) / 2 + i.
Definition stored_node n i := nth (stored_table_index n i) nodes Float.zero.
Definition stored_weight n i := nth (stored_table_index n i) weights Float.zero.
Definition stored_terms n : list (float * float) :=
  map (fun i => (stored_weight n i, stored_node n i)) (seq 0 n).
Definition stored_value (f : float -> float) n :=
  fold_left (fun acc term => Float.add acc (Float.mul (fst term) (f (snd term))))
    (stored_terms n) Float.zero.

Lemma stored_terms_length n : length (stored_terms n) = n.
Proof. unfold stored_terms. rewrite map_length, seq_length. reflexivity. Qed.

Lemma stored_terms_rule_order r : stored_terms (rule_size r) = rule_terms r.
Proof. reflexivity. Qed.

Lemma stored_value_rule_order f r : stored_value f (rule_size r) = rule_value f r.
Proof. reflexivity. Qed.
