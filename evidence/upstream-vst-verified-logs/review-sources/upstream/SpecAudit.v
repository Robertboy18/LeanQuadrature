(* Checks against the unchanged simple_cfem specifications and VST body proofs.
   This file is built by check-upstream-vst.py in a separate Rocq environment. *)
From CFEM.C Require Import quadrules spec_quadrules spec_quadrules_highlevel verif_quadrules.

Import ListNotations.

Lemma hughes_weight_identifier_mismatch :
  fst hughes_weight_spec <> _hughes_weight.
Proof. discriminate. Qed.

Lemma gauss2d_weight_identifier_duplicated :
  List.count_occ Pos.eq_dec (List.map fst quadrules_ASI) _gauss2d_weight = 2%nat.
Proof. reflexivity. Qed.

Lemma hughes_weight_identifier_missing :
  List.count_occ Pos.eq_dec (List.map fst quadrules_ASI) _hughes_weight = 0%nat.
Proof. reflexivity. Qed.

(* A body proof checks the function and the specification's second component.
   Matching the identifier to the program is a separate assembly obligation. *)
Lemma semax_body_ignores_identifier
    (V : varspecs) (G : funspecs) (C : compspecs)
    (f : function) (i j : ident) (s : funspec) :
  @semax_body V G C f (i, s) <-> @semax_body V G C f (j, s).
Proof. destruct s; reflexivity. Qed.

Definition corrected_hughes_weight_spec : ident * funspec :=
  (_hughes_weight, snd hughes_weight_spec).

Lemma hughes_weight_corrected_identifier :
  fst corrected_hughes_weight_spec = _hughes_weight.
Proof. reflexivity. Qed.

Lemma body_hughes_weight_corrected_identifier :
  semax_body Vprog Gprog f_hughes_weight corrected_hughes_weight_spec.
Proof. exact body_hughes_weight. Qed.

(* The initializer and the functional model contain different outer weights
   for the three-point rule. This is a comparison of their actual definitions. *)
Lemma three_point_initializer_model_mismatch :
  List.nth 3 (gvar_init v_gauss_wts) (Init_int8 Int.zero) <>
    Init_float64 (Znth 3 quadmodel.Quadmodel_F64.gauss_wts_list).
Proof. vm_compute; discriminate. Qed.

Print Assumptions hughes_weight_identifier_mismatch.
Print Assumptions gauss2d_weight_identifier_duplicated.
Print Assumptions hughes_weight_identifier_missing.
Print Assumptions semax_body_ignores_identifier.
Print Assumptions hughes_weight_corrected_identifier.
Print Assumptions body_hughes_weight_corrected_identifier.
Print Assumptions three_point_initializer_model_mismatch.
