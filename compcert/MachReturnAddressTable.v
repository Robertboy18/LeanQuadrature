From Coq Require Import List Bool ZArith.
From compcert Require Import AST Integers Mach.
From CminorImport Require Import EqualityMach MachReturnAddresses.

Import ListNotations.

Record address_entry := {
  entry_function : Mach.function;
  entry_code : Mach.code;
  entry_offset : ptrofs
}.

Definition address_row := (nat * nat * Z)%type.

(** Missing globals produce no entry; validity and coverage are checked separately. *)
Definition row_entries (p : Mach.program) (row : address_row) : list address_entry :=
  let '(index, skip, offset) := row in
  match nth_error (prog_defs p) index with
  | Some (_, Gfun (Internal f)) =>
      [{| entry_function := f; entry_code := skipn skip (Mach.fn_code f);
          entry_offset := Ptrofs.repr offset |}]
  | _ => []
  end.

Definition address_table (p : Mach.program) (rows : list address_row) : list address_entry :=
  flat_map (row_entries p) rows.

Fixpoint lookup_address (entries : list address_entry) (f : Mach.function) (c : Mach.code) :
    option ptrofs :=
  match entries with
  | [] => None
  | entry :: rest =>
      if mach_function_eq f (entry_function entry) then
        if mach_code_eq c (entry_code entry) then Some (entry_offset entry)
        else lookup_address rest f c
      else lookup_address rest f c
  end.

Definition valid_entry (entry : address_entry) : bool :=
  existsb (fun c => if mach_code_eq (entry_code entry) c then true else false)
    (call_continuations (Mach.fn_code (entry_function entry))) &&
  match predict_return_address (entry_function entry) (entry_code entry) with
  | Some offset => if Ptrofs.eq_dec offset (entry_offset entry) then true else false
  | None => false
  end.

Definition valid_table (entries : list address_entry) : bool :=
  forallb valid_entry entries.

Lemma valid_entry_sound entry :
  valid_entry entry = true ->
  In (entry_code entry) (call_continuations (Mach.fn_code (entry_function entry))) /\
  predict_return_address (entry_function entry) (entry_code entry) =
    Some (entry_offset entry).
Proof.
  unfold valid_entry. rewrite andb_true_iff.
  intros [CALL PREDICT]. split.
  - apply existsb_exists in CALL. destruct CALL as [c [IN SAME]].
    destruct (mach_code_eq (entry_code entry) c); try discriminate.
    now rewrite e.
  - destruct (predict_return_address (entry_function entry) (entry_code entry))
      as [offset |] eqn:P; try discriminate.
    destruct (Ptrofs.eq_dec offset (entry_offset entry)); try discriminate.
    now rewrite e.
Qed.

Lemma lookup_address_member entries f c offset :
  lookup_address entries f c = Some offset ->
  In {| entry_function := f; entry_code := c; entry_offset := offset |} entries.
Proof.
  induction entries as [|[ef ec eo] rest IH]; simpl; intro LOOKUP; try discriminate.
  destruct (mach_function_eq f ef) as [SAME | DIFFERENT].
  - subst ef. destruct (mach_code_eq c ec) as [SAME | DIFFERENT].
    + subst ec. inversion LOOKUP; subst eo. now left.
    + right. now apply IH.
  - right. now apply IH.
Qed.

Lemma lookup_address_predicts entries f c offset :
  valid_table entries = true ->
  lookup_address entries f c = Some offset ->
  In c (call_continuations (Mach.fn_code f)) /\
  predict_return_address f c = Some offset.
Proof.
  unfold valid_table. rewrite forallb_forall. intros VALID LOOKUP.
  exact (valid_entry_sound _ (VALID _ (lookup_address_member _ _ _ _ LOOKUP))).
Qed.

Theorem lookup_address_sound entries f c offset :
  valid_table entries = true ->
  lookup_address entries f c = Some offset ->
  Asmgenproof0.return_address_offset f c offset.
Proof.
  intros VALID LOOKUP.
  destruct (lookup_address_predicts _ _ _ _ VALID LOOKUP) as [CALL PREDICT].
  destruct (call_continuations_sound _ _ CALL) as [sg [ros TAIL]].
  eapply predicted_return_address_sound; eauto.
Qed.

Theorem lookup_address_unique entries f c offset other :
  valid_table entries = true ->
  lookup_address entries f c = Some offset ->
  Asmgenproof0.return_address_offset f c other ->
  other = offset.
Proof.
  intros VALID LOOKUP OTHER.
  destruct (lookup_address_predicts _ _ _ _ VALID LOOKUP) as [_ PREDICT].
  eapply predicted_return_address_unique; eauto.
Qed.

Definition covers_function (entries : list address_entry) (f : Mach.function) : bool :=
  forallb (fun c => match lookup_address entries f c with
    | Some _ => true | None => false end) (call_continuations (Mach.fn_code f)).

Definition covers_program (entries : list address_entry) (p : Mach.program) : bool :=
  forallb (fun definition => match snd definition with
    | Gfun (Internal f) => covers_function entries f
    | _ => true end) (prog_defs p).

Lemma covers_program_sound entries p name f c :
  covers_program entries p = true ->
  In (name, Gfun (Internal f)) (prog_defs p) ->
  In c (call_continuations (Mach.fn_code f)) ->
  exists offset, lookup_address entries f c = Some offset.
Proof.
  unfold covers_program. rewrite forallb_forall.
  intros COVERED FUNCTION CALL.
  specialize (COVERED _ FUNCTION). simpl in COVERED.
  unfold covers_function in COVERED. rewrite forallb_forall in COVERED.
  specialize (COVERED _ CALL).
  destruct (lookup_address entries f c) as [offset |] eqn:LOOKUP; try discriminate.
  now exists offset.
Qed.

(** At every covered call, the table is equivalent to the original assembly relation. *)
Theorem lookup_address_iff entries p name f c offset :
  valid_table entries = true ->
  covers_program entries p = true ->
  In (name, Gfun (Internal f)) (prog_defs p) ->
  In c (call_continuations (Mach.fn_code f)) ->
  (Asmgenproof0.return_address_offset f c offset <->
    lookup_address entries f c = Some offset).
Proof.
  intros VALID COVERED FUNCTION CALL. split.
  - intro ADDRESS.
    destruct (covers_program_sound _ _ _ _ _ COVERED FUNCTION CALL) as [other LOOKUP].
    pose proof (lookup_address_unique _ _ _ _ _ VALID LOOKUP ADDRESS) as SAME.
    now rewrite SAME.
  - exact (lookup_address_sound _ _ _ _ VALID).
Qed.

Print Assumptions lookup_address_sound.
Print Assumptions lookup_address_unique.
Print Assumptions lookup_address_iff.
