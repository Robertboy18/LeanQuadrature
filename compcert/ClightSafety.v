From Coq Require Import List ZArith.
From compcert Require Import Integers Floats Values AST Memory Events
  Globalenvs Ctypes Clight ClightBigstep Smallstep.
From QuadratureC Require Import quadrules ClightExample ClightRules ClightDeterminism.

Import ListNotations.

(** Total correctness of the four supported library calls, using the actual
    pinned tables.  The hypotheses specify only the supplied callback. *)
Section Callback.

Variable r : rule_order.
Variable f : float -> float.
Variable b : block.
Variable fd : Clight.fundef.

Hypothesis callback_found : Genv.find_funct ge (Vptr b Ptrofs.zero) = Some fd.
Hypothesis callback_type :
  type_of_fundef fd = Tfunction [Tfloat F64 noattr] (Tfloat F64 noattr) cc_default.
Hypothesis callback_contract :
  forall i, (i < rule_size r)%nat ->
    ClightBigstep.Clight2.eval_funcall ge initial_memory fd
      [Vfloat (rule_node r i)] E0 initial_memory (Vfloat (f (rule_node r i))).

Theorem integrate_rule_total_correct :
  total_call_correct ge
    (Callstate (Internal f_integrate)
      [Vptr b Ptrofs.zero; Vint (Int.repr (Z.of_nat (rule_size r)))]
      Kstop initial_memory)
    (Vfloat (rule_value f r)) initial_memory.
Proof.
  apply silent_total_call_correct.
  eapply integrate_rule_steps.
  - exact callback_found.
  - exact callback_type.
  - exact callback_contract.
  - exact I.
Qed.

End Callback.

(** The original example still depends on its two external cosine contracts. *)
Section ExternalCosine.

Hypothesis cosine_left :
  external_call cosine_external ge [Vfloat left_node] initial_memory
    E0 (Vfloat cosine_value) initial_memory.
Hypothesis cosine_right :
  external_call cosine_external ge [Vfloat right_node] initial_memory
    E0 (Vfloat cosine_value) initial_memory.

Theorem integrate_testfun_total_correct :
  total_call_correct ge
    (Callstate (Internal f_integrate_testfun) [] Kstop initial_memory)
    (Vfloat cosine_value) initial_memory.
Proof.
  apply silent_total_call_correct.
  apply integrate_testfun_steps; [exact cosine_left | exact cosine_right | exact I].
Qed.

Theorem integrate_testfun_all_returns_bits t value m :
  star Clight.step2 ge
    (Callstate (Internal f_integrate_testfun) [] Kstop initial_memory)
    t (Returnstate (Vfloat value) Kstop m) ->
  t = E0 /\ Float.to_bits value = Int64.repr 4605722458335229421 /\
    m = initial_memory.
Proof.
  intros RUN.
  destruct (call_unique_return _ _ _ _ integrate_testfun_total_correct
    _ _ _ RUN) as [HT [HV HM]].
  inversion HV; subst. repeat split.
Qed.

End ExternalCosine.

Check integrate_rule_total_correct.
Print Assumptions integrate_rule_total_correct.
Print Assumptions integrate_testfun_total_correct.
Print Assumptions integrate_testfun_all_returns_bits.
