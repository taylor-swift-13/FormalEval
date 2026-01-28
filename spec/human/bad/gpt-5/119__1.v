Example problem_119_test : problem_119_spec ["()("; ")"] "Yes".
Proof.
  left.
  eexists; eexists; eexists.
  repeat split.
  - simpl. reflexivity.
  - apply concr_base.
  - apply ibr_base.
    simpl.
    apply cpir_lparen.
    eapply cpir_rparen.
    + reflexivity.
    + apply cpir_lparen.
      eapply cpir_rparen.
      * reflexivity.
      * apply cpir_nil_zero.
  - reflexivity.
Qed.