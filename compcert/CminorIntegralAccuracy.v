From Coq Require Import Reals List ZArith.
From Coquelicot Require Import Coquelicot.
From compcert Require Import Integers Floats Values AST Memory Events
  Globalenvs Ctypes Clight ClightBigstep Smallstep Cminor.
From QuadratureC Require Import quadrules ClightExample ClightRules
  FiniteArithmetic TableAccuracy CallbackAccuracy ClightIntegralAccuracy
  CsharpminorExample CminorExample CminorSafety.

Import ListNotations Binary64Roundoff Binary64TableAccuracy Binary64CallbackAccuracy.
Local Open Scope R_scope.
Module CM := CminorExample.
Module CS := CsharpminorExample.
Module CT := CminorSafety.CminorTotalCorrectness.

(** The same derivative-based error budget holds at the actual Cminor entry
    produced by the two checked lowering passes.  The hypotheses concern the
    source callback and its approximation; compiler success is already proved. *)
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

Variables (g : R -> R) (error bound constant radius derivative_bound : R).
Hypothesis callback_error : callback_accuracy f g error.
Hypothesis error_nonnegative : 0 <= error.
Hypothesis bound_nonnegative : 0 <= bound.
Hypothesis constant_nonnegative : 0 <= constant.
Hypothesis derivative_bound_nonnegative : 0 <= derivative_bound.
Hypothesis integrand_bound : forall x, -1 <= x <= 1 -> Rabs (g x) <= bound.
Hypothesis derivatives_exist : forall x, -1 <= x <= 1 -> forall k,
  (k <= 2 * rule_size r)%nat -> ex_derive_n g k x.
Hypothesis first_derivative_bound :
  forall x, -1 <= x <= 1 -> Rabs (Derive g x) <= constant.
Hypothesis highest_derivative_bound : forall x, -1 <= x <= 1 ->
  Rabs (Derive_n g (2 * rule_size r) x) <= derivative_bound.
Hypothesis finite_radius : radius <= max_value.
Hypothesis arithmetic_range :
  (2 + INR (rule_size r) * weight_tolerance) * (bound + error) +
    2 * INR (rule_size r) * epsilon radius <= radius.

Theorem integrate_rule_total_integral_accuracy :
  exists tfd tm inj,
    Genv.find_symbol (Genv.globalenv CM.tprog) _integrate = Some CS.integrate_block /\
    Genv.find_funct_ptr (Genv.globalenv CM.tprog) CS.integrate_block = Some tfd /\
    CT.total_call_correct CM.tprog
      (Cminor.Callstate tfd
        [Vptr b Ptrofs.zero; Vint (Int.repr (Z.of_nat (rule_size r)))]
        Cminor.Kstop initial_memory)
      (Vfloat (rule_value f r)) tm /\
    Mem.inject inj initial_memory tm /\
    ex_RInt g (-1) 1 /\ finite (rule_value f r) /\
    Rabs (real (rule_value f r) - RInt g (-1) 1) <=
      integral_error_budget r error bound constant radius derivative_bound.
Proof.
  destruct (CT.integrate_rule_total_correct r f b fd
    callback_found callback_type callback_contract)
    as [tfd [tm [inj [HS [HF [HT HI]]]]]].
  exists tfd, tm, inj. split; [exact HS |]. split; [exact HF |].
  split; [exact HT |]. split; [exact HI |].
  exact (rule_value_integral_accuracy f g error bound constant radius derivative_bound r
    callback_error error_nonnegative bound_nonnegative constant_nonnegative
    derivative_bound_nonnegative integrand_bound derivatives_exist
    first_derivative_bound highest_derivative_bound finite_radius arithmetic_range).
Qed.

Theorem integrate_rule_all_returns_integral_accuracy tfd t value m :
  Genv.find_funct_ptr (Genv.globalenv CM.tprog) CS.integrate_block = Some tfd ->
  star Cminor.step (Genv.globalenv CM.tprog)
    (Cminor.Callstate tfd
      [Vptr b Ptrofs.zero; Vint (Int.repr (Z.of_nat (rule_size r)))]
      Cminor.Kstop initial_memory)
    t (Cminor.Returnstate (Vfloat value) Cminor.Kstop m) ->
  t = E0 /\ (exists inj, Mem.inject inj initial_memory m) /\
  ex_RInt g (-1) 1 /\ finite value /\
  Rabs (real value - RInt g (-1) 1) <=
    integral_error_budget r error bound constant radius derivative_bound.
Proof.
  intros FOUND RUN.
  destruct integrate_rule_total_integral_accuracy
    as [tfd' [tm [inj [HS [HF [HT [HI HNUM]]]]]]].
  assert (tfd' = tfd) by congruence. subst tfd'.
  destruct (CT.call_unique_return _ _ _ _ HT _ _ _ RUN) as [HTR [HV HM]].
  inversion HV; subst. split; [reflexivity |]. split; [eauto | exact HNUM].
Qed.
End Callback.
