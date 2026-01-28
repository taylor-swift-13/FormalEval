Example test_case_1 : problem_136_spec [2; 4; 1; 3; 5; 7] (None, Some 1).
Proof.
  unfold problem_136_spec.
  unfold is_largest_negative, is_smallest_positive.
  split.
  - (* Prove is_largest_negative *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | H]]]]]];
    try (subst x; lia);
    contradiction.
  - (* Prove is_smallest_positive *)
    split; [lia|].
    split; [simpl; right; left; reflexivity|].
    intros x H Hpos.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | H]]]]]];
    try (subst x; lia);
    contradiction.
Qed.