Require Import List Ascii String.
Import ListNotations.
Open Scope string_scope.
Open Scope char_scope.

Definition problem_54_pre (s0 s1 : string) : Prop := True.

Definition problem_54_spec (s0 s1 : string) (b : bool) : Prop :=
  let list_s0 := list_ascii_of_string s0 in
  let list_s1 := list_ascii_of_string s1 in
  b = true <-> (forall (c : ascii), In c list_s0 <-> In c list_s1).

Example problem_54_test_example :
  problem_54_spec "abcdcb5143241a514321de" "54321" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. discriminate.
  - intros H.
    exfalso.
    specialize (H "a").
    destruct H as [H1 H2].
    assert (Ha_in : In "a" (list_ascii_of_string "abcdcb5143241a514321de")).
    { simpl. left. reflexivity. }
    specialize (H1 Ha_in).
    simpl in H1.
    destruct H1 as [H1|H1]; [discriminate H1|].
    destruct H1 as [H1|H1]; [discriminate H1|].
    destruct H1 as [H1|H1]; [discriminate H1|].
    destruct H1 as [H1|H1]; [discriminate H1|].
    destruct H1 as [H1|H1]; [discriminate H1|].
    inversion H1.
Qed.