From Coq Require Import Reals List ZArith.
From compcert Require Import Integers Floats Values AST Memory Events
  Globalenvs Ctypes Clight ClightBigstep Smallstep.
From QuadratureC Require Import quadrules ClightExample ClightRules
  ClightDeterminism ClightSafety FiniteArithmetic TableAccuracy CallbackAccuracy.

Import ListNotations Binary64Roundoff Binary64TableAccuracy Binary64CallbackAccuracy.
Local Open Scope R_scope.

(** Attach the numerical theorem to the actual initialized Clight program.
    The callback contract supplies silent execution at the stored nodes;
    callback_accuracy describes its numerical approximation independently. *)
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

Theorem integrate_rule_total_accuracy g error bound constant radius :
  callback_accuracy f g error -> 0 <= error -> 0 <= bound -> 0 <= constant ->
  (forall x, -1 <= x <= 1 -> Rabs (g x) <= bound) ->
  lipschitz_on_interval g constant ->
  radius <= max_value ->
  (2 + INR (rule_size r) * weight_tolerance) * (bound + error) +
    2 * INR (rule_size r) * epsilon radius <= radius ->
  total_call_correct ge
    (Callstate (Internal f_integrate)
      [Vptr b Ptrofs.zero; Vint (Int.repr (Z.of_nat (rule_size r)))]
      Kstop initial_memory)
    (Vfloat (rule_value f r)) initial_memory /\
  finite (rule_value f r) /\
  Rabs (real (rule_value f r) - ideal_value g r) <=
    2 * INR (rule_size r) * epsilon radius +
    (2 + INR (rule_size r) * weight_tolerance) * (error + constant * node_tolerance) +
      INR (rule_size r) * weight_tolerance * bound.
Proof.
  intros HC HE HB HL HG HGL HM HR. split.
  - exact (integrate_rule_total_correct r f b fd
      callback_found callback_type callback_contract).
  - exact (rule_value_accuracy f g error bound constant radius r HC HE HB HL HG HGL HM HR).
Qed.

(** Every returning small-step execution has the certified value, error,
    empty trace, and unchanged memory. *)
Theorem integrate_rule_all_returns_accuracy g error bound constant radius t value m :
  callback_accuracy f g error -> 0 <= error -> 0 <= bound -> 0 <= constant ->
  (forall x, -1 <= x <= 1 -> Rabs (g x) <= bound) ->
  lipschitz_on_interval g constant ->
  radius <= max_value ->
  (2 + INR (rule_size r) * weight_tolerance) * (bound + error) +
    2 * INR (rule_size r) * epsilon radius <= radius ->
  star Clight.step2 ge
    (Callstate (Internal f_integrate)
      [Vptr b Ptrofs.zero; Vint (Int.repr (Z.of_nat (rule_size r)))]
      Kstop initial_memory)
    t (Returnstate (Vfloat value) Kstop m) ->
  t = E0 /\ m = initial_memory /\ finite value /\
  Rabs (real value - ideal_value g r) <=
    2 * INR (rule_size r) * epsilon radius +
    (2 + INR (rule_size r) * weight_tolerance) * (error + constant * node_tolerance) +
      INR (rule_size r) * weight_tolerance * bound.
Proof.
  intros HC HE HB HL HG HGL HM HR RUN.
  destruct (integrate_rule_total_accuracy g error bound constant radius
    HC HE HB HL HG HGL HM HR) as [HTOTAL [HFIN HERR]].
  destruct (call_unique_return _ _ _ _ HTOTAL _ _ _ RUN) as [HT [HV HMEM]].
  inversion HV; subst. auto.
Qed.

End Callback.
