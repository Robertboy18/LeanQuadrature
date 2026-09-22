From Coq Require Import Reals Lra FunctionalExtensionality.

Local Open Scope R_scope.

Definition integrand : R -> R :=
  (fct_cte (1 / 2) * (fct_cte 1 - id) * cos)%F.

Definition antiderivative : R -> R :=
  (fct_cte (1 / 2) * ((fct_cte 1 - id) * sin - cos))%F.

Lemma integrand_continuous : continuity integrand.
Proof.
  unfold integrand.
  apply continuity_mult.
  - apply continuity_mult.
    + apply continuity_const. intros x y. reflexivity.
    + apply continuity_minus.
      * apply continuity_const. intros x y. reflexivity.
      * apply derivable_continuous, derivable_id.
  - exact continuity_cos.
Qed.

Lemma antiderivative_derivative x :
  derivable_pt_lim antiderivative x (integrand x).
Proof.
  unfold antiderivative.
  change (derivable_pt_lim
    (fct_cte (1 / 2) * ((fct_cte 1 - id) * sin - cos))%F x
    (1 / 2 * (1 - x) * cos x)).
  replace (1 / 2 * (1 - x) * cos x) with
    (0 * ((1 - x) * sin x - cos x) +
      (1 / 2) * (((0 - 1) * sin x + (1 - x) * cos x) - (- sin x))) by ring.
  apply (derivable_pt_lim_mult (fct_cte (1 / 2))
    ((fct_cte 1 - id) * sin - cos)%F x 0
    (((0 - 1) * sin x + (1 - x) * cos x) - (- sin x))).
  - apply derivable_pt_lim_const.
  - apply (derivable_pt_lim_minus ((fct_cte 1 - id) * sin)%F cos x
      ((0 - 1) * sin x + (1 - x) * cos x) (- sin x)).
    + apply (derivable_pt_lim_mult (fct_cte 1 - id)%F sin x (0 - 1) (cos x)).
      * apply (derivable_pt_lim_minus (fct_cte 1) id x 0 1).
        -- apply derivable_pt_lim_const.
        -- apply derivable_pt_lim_id.
      * apply derivable_pt_lim_sin.
    + apply derivable_pt_lim_cos.
Qed.

Definition antiderivative_differentiable : derivable antiderivative.
Proof. intro x. exists (integrand x). apply antiderivative_derivative. Defined.

Lemma antiderivative_derive x :
  derive antiderivative antiderivative_differentiable x = integrand x.
Proof. apply derive_pt_eq_0, antiderivative_derivative. Qed.

Definition antiderivative_C1 : C1_fun.
Proof.
  refine {| c1 := antiderivative; diff0 := antiderivative_differentiable |}.
  assert (H : derive antiderivative antiderivative_differentiable = integrand).
  { apply functional_extensionality. exact antiderivative_derive. }
  rewrite H. exact integrand_continuous.
Defined.

Lemma integrand_integrable : Riemann_integrable integrand (-1) 1.
Proof.
  apply continuity_implies_RiemannInt.
  - lra.
  - intros x H. apply integrand_continuous.
Qed.

(** The real target integral is established within Rocq as well as Lean. *)
Theorem integral_value (pr : Riemann_integrable integrand (-1) 1) :
  RiemannInt pr = sin 1.
Proof.
  transitivity
    (RiemannInt (RiemannInt_P32 antiderivative_C1 (-1) 1)).
  - apply RiemannInt_P18.
    + lra.
    + intros x H. symmetry. apply antiderivative_derive.
  - rewrite FTC_Riemann.
    change (antiderivative 1 - antiderivative (-1) = sin 1).
    change ((1 / 2) * ((1 - 1) * sin 1 - cos 1) -
      (1 / 2) * ((1 - (-1)) * sin (-1) - cos (-1)) = sin 1).
    replace (-1)%R with (Ropp 1) by ring.
    rewrite sin_neg, cos_neg. field.
Qed.

Print Assumptions integrand_integrable.
Print Assumptions integral_value.
