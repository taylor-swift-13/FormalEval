Example problem_149_test :
  problem_149_spec ["aa"%string; "a"%string; "aaa"%string] ["aa"%string].
Proof.
  unfold problem_149_spec.
  unfold list_sort_impl.
  simpl.
  reflexivity.
Qed.