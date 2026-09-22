From compcert Require Import Errors Smallstep Compiler Compopts Cminor Asm.

(** CompCert's public whole-compiler theorem starts at Csyntax. The application
    in this project already has a normalized Clight proof and checked lowering
    to Cminor. Compose the remaining official pass theorems at that entry.

    Successful compilation is an explicit premise here. This theorem does not
    assert that the backend has been evaluated on our application in Rocq. *)
Theorem successful_cminor_compilation_forward p tp :
  Compiler.transf_cminor_program p = OK tp ->
  forward_simulation (Cminor.semantics p) (Asm.semantics tp).
Proof.
  intros T.
  unfold Compiler.transf_cminor_program, Compiler.time in T.
  rewrite ! Compiler.compose_print_identity in T. simpl in T.
  destruct (Selection.sel_program p) as [p1 | e] eqn:P1; simpl in T;
    try discriminate.
  destruct (RTLgen.transl_program p1) as [p2 | e] eqn:P2; simpl in T;
    try discriminate.
  unfold Compiler.transf_rtl_program, Compiler.time in T.
  rewrite ! Compiler.compose_print_identity in T. simpl in T.
  set (p3 := Compiler.total_if optim_tailcalls Tailcall.transf_program p2) in *.
  destruct (Inlining.transf_program p3) as [p4 | e] eqn:P4; simpl in T;
    try discriminate.
  set (p5 := Renumber.transf_program p4) in *.
  set (p6 := Compiler.total_if optim_constprop Constprop.transf_program p5) in *.
  set (p7 := Compiler.total_if optim_constprop Renumber.transf_program p6) in *.
  destruct (Compiler.partial_if optim_CSE CSE.transf_program p7)
    as [p8 | e] eqn:P8; simpl in T; try discriminate.
  destruct (Compiler.partial_if optim_redundancy Deadcode.transf_program p8)
    as [p9 | e] eqn:P9; simpl in T; try discriminate.
  destruct (Unusedglob.transform_program p9) as [p10 | e] eqn:P10;
    simpl in T; try discriminate.
  destruct (Allocation.transf_program p10) as [p11 | e] eqn:P11;
    simpl in T; try discriminate.
  set (p12 := Tunneling.tunnel_program p11) in *.
  destruct (Linearize.transf_program p12) as [p13 | e] eqn:P13;
    simpl in T; try discriminate.
  set (p14 := CleanupLabels.transf_program p13) in *.
  destruct (Compiler.partial_if debug Debugvar.transf_program p14)
    as [p15 | e] eqn:P15; simpl in T; try discriminate.
  destruct (Stacking.transf_program p15) as [p16 | e] eqn:P16;
    simpl in T; try discriminate.

  eapply compose_forward_simulations.
  { apply Selectionproof.transf_program_correct.
    apply Selectionproof.transf_program_match. exact P1. }
  eapply compose_forward_simulations.
  { apply RTLgenproof.transf_program_correct.
    apply RTLgenproof.transf_program_match. exact P2. }
  eapply compose_forward_simulations.
  { eapply Compiler.match_if_simulation.
    + apply Compiler.total_if_match, Tailcallproof.transf_program_match.
    + exact Tailcallproof.transf_program_correct. }
  eapply compose_forward_simulations.
  { apply Inliningproof.transf_program_correct.
    apply Inliningproof.transf_program_match. exact P4. }
  eapply compose_forward_simulations.
  { apply Renumberproof.transf_program_correct, Renumberproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply Compiler.match_if_simulation.
    + apply Compiler.total_if_match, Constpropproof.transf_program_match.
    + exact Constpropproof.transf_program_correct. }
  eapply compose_forward_simulations.
  { eapply Compiler.match_if_simulation.
    + apply Compiler.total_if_match, Renumberproof.transf_program_match.
    + exact Renumberproof.transf_program_correct. }
  eapply compose_forward_simulations.
  { eapply Compiler.match_if_simulation.
    + eapply Compiler.partial_if_match; [exact CSEproof.transf_program_match | exact P8].
    + exact CSEproof.transf_program_correct. }
  eapply compose_forward_simulations.
  { eapply Compiler.match_if_simulation.
    + eapply Compiler.partial_if_match;
        [exact Deadcodeproof.transf_program_match | exact P9].
    + exact Deadcodeproof.transf_program_correct. }
  eapply compose_forward_simulations.
  { apply Unusedglobproof.transf_program_correct.
    apply Unusedglobproof.transf_program_match. exact P10. }
  eapply compose_forward_simulations.
  { apply Allocproof.transf_program_correct.
    apply Allocproof.transf_program_match. exact P11. }
  eapply compose_forward_simulations.
  { apply Tunnelingproof.transf_program_correct, Tunnelingproof.transf_program_match. }
  eapply compose_forward_simulations.
  { apply Linearizeproof.transf_program_correct.
    apply Linearizeproof.transf_program_match. exact P13. }
  eapply compose_forward_simulations.
  { apply CleanupLabelsproof.transf_program_correct,
      CleanupLabelsproof.transf_program_match. }
  eapply compose_forward_simulations.
  { eapply Compiler.match_if_simulation.
    + eapply Compiler.partial_if_match;
        [exact Debugvarproof.transf_program_match | exact P15].
    + exact Debugvarproof.transf_program_correct. }
  eapply compose_forward_simulations.
  { eapply Stackingproof.transf_program_correct
      with (return_address_offset := Asmgenproof0.return_address_offset).
    + exact Asmgenproof.return_address_exists.
    + apply Stackingproof.transf_program_match. exact P16. }
  apply Asmgenproof.transf_program_correct, Asmgenproof.transf_program_match.
  exact T.
Qed.

Print Assumptions successful_cminor_compilation_forward.
