From Coq Require Import List ZArith.
From Flocq Require Import IEEE754.Binary.
From compcert Require Import Coqlib Maps Integers Floats Values AST Memory Events
  Globalenvs Ctypes Cop Clight ClightBigstep.
From QuadratureC Require Import ClightExample.

Import ListNotations.
Local Open Scope Z_scope.

(** A degree-14 Taylor polynomial evaluated in binary64 with Horner's rule.
    The coefficients are computed once when constructing the syntax; there is
    no division, factorial computation, or external call at runtime.
    Only the two inputs needed by the quadrature application are certified. *)
Fixpoint factorial_Z (n : nat) : Z :=
  match n with
  | O => 1
  | S k => Z.of_nat (S k) * factorial_Z k
  end.

Definition coefficient (n : nat) : float :=
  Float.div (if Nat.even n then one else Float.neg one)
    (Float.of_long (Int64.repr (factorial_Z (2 * n)))).

Definition coefficients := map (fun bits => Float.of_bits (Int64.repr bits))
  [4607182418800017408; 13826050856027422720; 4586165620538955093;
   13787419979223755799; 4537941361671905306; 13732177094651715420;
   4477122120089393304; 13666517717442657437].

(** Exact binary encodings of the rounded coefficients (-1)^n / (2n)!.
    Recording the encodings keeps arithmetic proof payloads out of the AST. *)
Theorem coefficients_rounded_taylor :
  map Float.to_bits coefficients =
    map (fun n => Float.to_bits (coefficient n)) (seq 0 8).
Proof. vm_compute. reflexivity. Qed.

Fixpoint horner_value (cs : list float) (z : float) : float :=
  match cs with
  | [] => Float.zero
  | c :: rest => Float.add c (Float.mul z (horner_value rest z))
  end.

Definition polynomial_value (x : float) : float :=
  horner_value coefficients (Float.mul x x).

Definition argument_temp : ident := 4000%positive.
Definition square_temp : ident := 4001%positive.
Definition double_type := Tfloat F64 noattr.

Fixpoint horner_expression (cs : list float) : expr :=
  match cs with
  | [] => Econst_float Float.zero double_type
  | c :: rest =>
      Ebinop Oadd (Econst_float c double_type)
        (Ebinop Omul (Etempvar square_temp double_type)
          (horner_expression rest) double_type) double_type
  end.

Definition cosine_function : Clight.function := {|
  fn_return := double_type;
  fn_callconv := cc_default;
  fn_params := [(argument_temp, double_type)];
  fn_vars := [];
  fn_temps := [(square_temp, double_type)];
  fn_body :=
    Ssequence
      (Sset square_temp
        (Ebinop Omul (Etempvar argument_temp double_type)
          (Etempvar argument_temp double_type) double_type))
      (Sreturn (Some (horner_expression coefficients)))
|}.

Lemma horner_expression_type cs :
  typeof (horner_expression cs) = double_type.
Proof. destruct cs; reflexivity. Qed.

Lemma horner_expression_evaluates ge e le m cs z :
  le ! square_temp = Some (Vfloat z) ->
  eval_expr ge e le m (horner_expression cs) (Vfloat (horner_value cs z)).
Proof.
  intro H. induction cs as [|c rest IH].
  - constructor.
  - cbn [horner_expression horner_value].
    eapply eval_Ebinop.
    + constructor.
    + eapply eval_Ebinop.
      * apply eval_Etempvar. exact H.
      * exact IH.
      * rewrite horner_expression_type. reflexivity.
    + reflexivity.
Qed.

Theorem cosine_execution ge m x :
  ClightBigstep.Clight2.eval_funcall ge m (Internal cosine_function)
    [Vfloat x] E0 m (Vfloat (polynomial_value x)).
Proof.
  unfold ClightBigstep.Clight2.eval_funcall.
  eapply eval_funcall_internal with (e := empty_env) (m1 := m) (m2 := m).
  - eapply function_entry2_intro.
    + vm_compute. repeat constructor; simpl; intuition congruence.
    + vm_compute. repeat constructor; simpl; intuition congruence.
    + vm_compute. intuition congruence.
    + change (alloc_variables ge empty_env m [] empty_env m). constructor.
    + reflexivity.
  - cbn [cosine_function fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply exec_Sset.
      eapply eval_Ebinop.
      * apply eval_Etempvar. reflexivity.
      * apply eval_Etempvar. reflexivity.
      * reflexivity.
    + apply exec_Sreturn_some. apply horner_expression_evaluates. reflexivity.
  - split; [discriminate | reflexivity].
  - reflexivity.
Qed.

Theorem polynomial_left_bits :
  Float.to_bits (polynomial_value left_node) = Int64.repr 4605722458335229421.
Proof. vm_compute. reflexivity. Qed.

Theorem polynomial_right_bits :
  Float.to_bits (polynomial_value right_node) = Int64.repr 4605722458335229421.
Proof. vm_compute. reflexivity. Qed.

Theorem polynomial_left_value : polynomial_value left_node = cosine_value.
Proof.
  rewrite <- (Float.of_to_bits (polynomial_value left_node)), polynomial_left_bits.
  reflexivity.
Qed.

Theorem polynomial_right_value : polynomial_value right_node = cosine_value.
Proof.
  rewrite <- (Float.of_to_bits (polynomial_value right_node)), polynomial_right_bits.
  reflexivity.
Qed.

Theorem cosine_left_execution ge m :
  ClightBigstep.Clight2.eval_funcall ge m (Internal cosine_function)
    [Vfloat left_node] E0 m (Vfloat cosine_value).
Proof. rewrite <- polynomial_left_value. apply cosine_execution. Qed.

Theorem cosine_right_execution ge m :
  ClightBigstep.Clight2.eval_funcall ge m (Internal cosine_function)
    [Vfloat right_node] E0 m (Vfloat cosine_value).
Proof. rewrite <- polynomial_right_value. apply cosine_execution. Qed.

Print Assumptions cosine_execution.
Print Assumptions coefficients_rounded_taylor.
Print Assumptions polynomial_left_value.
Print Assumptions polynomial_right_value.
Print Assumptions cosine_left_execution.
Print Assumptions cosine_right_execution.
