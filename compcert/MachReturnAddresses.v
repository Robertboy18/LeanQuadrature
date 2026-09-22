From Coq Require Import List ZArith Lia.
From compcert Require Import Coqlib AST Integers Errors Mach Asm Asmgen
  Asmgenproof0 Asmgenproof.

Import ListNotations.
Local Open Scope Z_scope.

(** Return addresses count formal Asm instructions, not emitted machine-code bytes. *)
Definition predict_return_address (f : Mach.function) (c : Mach.code) : option ptrofs :=
  match Asmgen.transf_function f, Asmgen.transl_code f c false with
  | OK tf, OK tc =>
      Some (Ptrofs.repr (list_length_z (Asm.fn_code tf) - list_length_z tc))
  | _, _ => None
  end.

Lemma code_tail_length_difference offset body tail :
  code_tail offset body tail ->
  offset = list_length_z body - list_length_z tail.
Proof.
  induction 1.
  - lia.
  - rewrite list_length_z_cons. lia.
Qed.

(** The predictor is justified by the actual x86 assembly-generation theorem. *)
Theorem predicted_return_address_sound f sg ros c offset :
  is_tail (Mach.Mcall sg ros :: c) (Mach.fn_code f) ->
  predict_return_address f c = Some offset ->
  return_address_offset f c offset.
Proof.
  intros TAIL PREDICT.
  unfold predict_return_address in PREDICT.
  destruct (Asmgen.transf_function f) as [tf | error] eqn:TF; try discriminate.
  destruct (Asmgen.transl_code f c false) as [tc | error] eqn:TC; try discriminate.
  inversion PREDICT; subst offset.
  destruct (Asmgenproof.return_address_exists f sg ros c TAIL) as [ra RA].
  pose proof (code_tail_length_difference _ _ _ (RA tf tc TF TC)) as LENGTH.
  rewrite <- LENGTH, Ptrofs.repr_unsigned. exact RA.
Qed.

(** Every address permitted by the original relation equals the prediction. *)
Theorem predicted_return_address_unique f c offset other :
  predict_return_address f c = Some offset ->
  return_address_offset f c other ->
  other = offset.
Proof.
  intros PREDICT RA.
  unfold predict_return_address in PREDICT.
  destruct (Asmgen.transf_function f) as [tf | error] eqn:TF; try discriminate.
  destruct (Asmgen.transl_code f c false) as [tc | error] eqn:TC; try discriminate.
  inversion PREDICT; subst offset.
  pose proof (code_tail_length_difference _ _ _ (RA tf tc TF TC)) as LENGTH.
  rewrite <- LENGTH, Ptrofs.repr_unsigned. reflexivity.
Qed.

Fixpoint call_continuations (body : Mach.code) : list Mach.code :=
  match body with
  | [] => []
  | Mach.Mcall _ _ :: rest => rest :: call_continuations rest
  | _ :: rest => call_continuations rest
  end.

Lemma call_continuations_sound body c :
  In c (call_continuations body) ->
  exists sg ros, is_tail (Mach.Mcall sg ros :: c) body.
Proof.
  induction body as [|instruction rest IH]; simpl; intro H; try contradiction.
  destruct instruction; simpl in H;
    try (destruct (IH H) as [sg [ros TAIL]];
         exists sg, ros; apply is_tail_cons; exact TAIL).
  destruct H as [H | H].
  - subst c. do 2 eexists. apply is_tail_refl.
  - destruct (IH H) as [sg' [ros' TAIL]].
    exists sg', ros'. apply is_tail_cons. exact TAIL.
Qed.

Definition function_returns_known (f : Mach.function) : bool :=
  forallb (fun c => match predict_return_address f c with
    | Some _ => true | None => false end) (call_continuations (Mach.fn_code f)).

Definition program_returns_known (p : Mach.program) : bool :=
  forallb (fun definition => match snd definition with
    | Gfun (Internal f) => function_returns_known f
    | _ => true end) (prog_defs p).

Theorem function_returns_known_sound f :
  function_returns_known f = true ->
  forall c, In c (call_continuations (Mach.fn_code f)) ->
  exists offset, predict_return_address f c = Some offset /\
    (forall other, return_address_offset f c other <-> other = offset).
Proof.
  unfold function_returns_known. rewrite forallb_forall.
  intros KNOWN c IN. specialize (KNOWN c IN).
  destruct (predict_return_address f c) as [offset |] eqn:PREDICT; try discriminate.
  exists offset. split; auto. intro other. split.
  - apply predicted_return_address_unique. exact PREDICT.
  - intro SAME. subst other.
    destruct (call_continuations_sound _ _ IN) as [sg [ros TAIL]].
    eapply predicted_return_address_sound; eauto.
Qed.

Theorem program_returns_known_sound p :
  program_returns_known p = true ->
  forall name f, In (name, Gfun (Internal f)) (prog_defs p) ->
  forall c, In c (call_continuations (Mach.fn_code f)) ->
  exists offset, predict_return_address f c = Some offset /\
    (forall other, return_address_offset f c other <-> other = offset).
Proof.
  unfold program_returns_known. rewrite forallb_forall.
  intros KNOWN name f IN. apply function_returns_known_sound.
  exact (KNOWN (name, Gfun (Internal f)) IN).
Qed.

Print Assumptions predicted_return_address_sound.
Print Assumptions predicted_return_address_unique.
Print Assumptions function_returns_known_sound.
Print Assumptions program_returns_known_sound.
