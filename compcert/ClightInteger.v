(** Integer specifications for every return of the actual Clight rules.

    The same callback contract and range budget give a complete result
    characterization by integer coefficients, exponents, and signs. *)

From Coq Require Import Reals List ZArith.
From compcert Require Import Integers Floats Values AST Memory Events
  Globalenvs Ctypes Clight ClightBigstep Smallstep.
From QuadratureC Require Import quadrules ClightExample ClightRules
  ClightDeterminism ClightSafety FiniteArithmetic ClightRoundoff
  FiniteRepresentation ClightRepresentation FiniteInteger.

Import ListNotations Binary64Roundoff.
Local Open Scope R_scope.

Theorem rule_value_integer radius f r :
  radius <= max_value ->
  (forall i, (i < rule_size r)%nat -> finite (f (rule_node r i))) ->
  product_mass f (rule_terms r) + 2 * INR (rule_size r) * epsilon radius <= radius ->
  Binary64Integer.represents (rule_value f r)
    (Binary64Integer.sum f (rule_terms r) ((0%Z, 0%Z), false)).
Proof.
  intros HM HF HB.
  rewrite Binary64Integer.represents_iff_observe, Binary64Integer.sum_real.
  assert (HI : Binary64Integer.state_real ((0%Z, 0%Z), false) = (0, false)).
  { unfold Binary64Integer.state_real, D.dyadic_real. cbn. f_equal. ring. }
  rewrite HI. exact (rule_value_observe radius f r HM HF HB).
Qed.

Theorem rule_value_integer_eq_iff radius f r z :
  radius <= max_value ->
  (forall i, (i < rule_size r)%nat -> finite (f (rule_node r i))) ->
  product_mass f (rule_terms r) + 2 * INR (rule_size r) * epsilon radius <= radius ->
  (rule_value f r = z <->
    Binary64Integer.represents z
      (Binary64Integer.sum f (rule_terms r) ((0%Z, 0%Z), false))).
Proof.
  intros HM HF HB.
  pose proof (rule_value_integer radius f r HM HF HB) as HR.
  split; [intros <-; exact HR |].
  intros HZ. eapply Binary64Integer.represents_unique; eauto.
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

Theorem integrate_rule_all_returns_integer radius t value m :
  radius <= max_value ->
  (forall i, (i < rule_size r)%nat -> finite (f (rule_node r i))) ->
  product_mass f (rule_terms r) + 2 * INR (rule_size r) * epsilon radius <= radius ->
  star Clight.step2 ge
    (Callstate (Internal f_integrate)
      [Vptr b Ptrofs.zero; Vint (Int.repr (Z.of_nat (rule_size r)))]
      Kstop initial_memory)
    t (Returnstate (Vfloat value) Kstop m) ->
  t = E0 /\ m = initial_memory /\
  Binary64Integer.represents value
    (Binary64Integer.sum f (rule_terms r) ((0%Z, 0%Z), false)).
Proof.
  intros HM HF HB RUN.
  pose proof (integrate_rule_total_correct r f b fd
    callback_found callback_type callback_contract) as HTOTAL.
  pose proof (rule_value_integer radius f r HM HF HB) as HINTEGER.
  destruct (call_unique_return _ _ _ _ HTOTAL _ _ _ RUN) as [HT [HV HMEM]].
  inversion HV; subst. auto.
Qed.

End Callback.
