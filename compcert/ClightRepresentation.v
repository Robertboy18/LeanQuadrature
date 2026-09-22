(** Signed observations for every return of the four actual Clight rules.

    The initialized tables and finite callback results determine the complete
    result through the independently proved CompCert signed recurrence. The
    callback execution contract is the same as in ClightSafety. *)

From Coq Require Import Reals List ZArith.
From compcert Require Import Integers Floats Values AST Memory Events
  Globalenvs Ctypes Clight ClightBigstep Smallstep.
From QuadratureC Require Import quadrules ClightExample ClightRules
  ClightDeterminism ClightSafety FiniteArithmetic ClightRoundoff FiniteRepresentation.

Import ListNotations Binary64Roundoff Binary64Representation.
Local Open Scope R_scope.
Local Transparent Float.zero.

(** The actual initialized weights and callback outputs determine both the
    real value and the sign of the result, including either zero encoding. *)
Theorem rule_value_observe radius f r :
  radius <= max_value ->
  (forall i, (i < rule_size r)%nat -> finite (f (rule_node r i))) ->
  product_mass f (rule_terms r) + 2 * INR (rule_size r) * epsilon radius <= radius ->
  finite (rule_value f r) /\
  observe (rule_value f r) = signed_sum f (rule_terms r) (0, false).
Proof.
  intros HM HF HB.
  destruct (rule_value_bounded radius f r HM HF HB) as [HS [HFIN _]].
  split; [exact HFIN |].
  exact (observe_integrate_finite f (rule_terms r) Float.zero HS
    (rule_terms_finite f r HF)).
Qed.

Theorem rule_value_eq_iff radius f r z :
  radius <= max_value ->
  (forall i, (i < rule_size r)%nat -> finite (f (rule_node r i))) ->
  product_mass f (rule_terms r) + 2 * INR (rule_size r) * epsilon radius <= radius ->
  (rule_value f r = z <->
    finite z /\ observe z = signed_sum f (rule_terms r) (0, false)).
Proof.
  intros HM HF HB.
  destruct (rule_value_observe radius f r HM HF HB) as [HN HO].
  split.
  - intros <-. auto.
  - intros [HZ HE]. apply (observe_injective _ _ HN HZ).
    rewrite HO. symmetry. exact HE.
Qed.

Section Callback.

Variable r : rule_order.
Variable f : Floats.float -> Floats.float.
Variable b : block.
Variable fd : Clight.fundef.

Hypothesis callback_found : Genv.find_funct ge (Vptr b Ptrofs.zero) = Some fd.
Hypothesis callback_type :
  type_of_fundef fd = Tfunction [Tfloat F64 noattr] (Tfloat F64 noattr) cc_default.
Hypothesis callback_contract :
  forall i, (i < rule_size r)%nat ->
    ClightBigstep.Clight2.eval_funcall ge initial_memory fd
      [Vfloat (rule_node r i)] E0 initial_memory (Vfloat (f (rule_node r i))).

Theorem integrate_rule_all_returns_observation radius t value m :
  radius <= max_value ->
  (forall i, (i < rule_size r)%nat -> finite (f (rule_node r i))) ->
  product_mass f (rule_terms r) + 2 * INR (rule_size r) * epsilon radius <= radius ->
  star Clight.step2 ge
    (Callstate (Internal f_integrate)
      [Vptr b Ptrofs.zero; Vint (Int.repr (Z.of_nat (rule_size r)))]
      Kstop initial_memory)
    t (Returnstate (Vfloat value) Kstop m) ->
  t = E0 /\ m = initial_memory /\ finite value /\
  observe value = signed_sum f (rule_terms r) (0, false).
Proof.
  intros HM HF HB RUN.
  pose proof (integrate_rule_total_correct r f b fd
    callback_found callback_type callback_contract) as HTOTAL.
  destruct (rule_value_observe radius f r HM HF HB) as [HFIN HOBS].
  destruct (call_unique_return _ _ _ _ HTOTAL _ _ _ RUN) as [HT [HV HMEM]].
  inversion HV; subst. auto.
Qed.

End Callback.
