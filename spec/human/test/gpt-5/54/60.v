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
  problem_54_spec "abcdcb5143241a514321db" "cd" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. exfalso. inversion H.
  - intros H.
    specialize (H "a"%char).
    destruct H as [Hlr Hrl].
    assert (In "a"%char (list_ascii_of_string "abcdcb5143241a514321db")) as Ha0.
    { simpl. left. reflexivity. }
    pose proof (Hlr Ha0) as Ha1.
    simpl in Ha1.
    exfalso.
    destruct Ha1 as [H0|H0].
    + inversion H0.
    + destruct H0 as [H1|H1].
      * inversion H1.
      * inversion H1.
Qed.