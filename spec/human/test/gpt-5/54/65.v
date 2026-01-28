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
  problem_54_spec "aab" "123" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H.
    exfalso.
    discriminate H.
  - intros H.
    exfalso.
    specialize (H "a").
    destruct H as [H1 H2].
    assert (Hin0 : In "a" ("a" :: "a" :: "b" :: [])).
    { simpl. left. reflexivity. }
    pose proof (H1 Hin0) as Hin1.
    simpl in Hin1.
    destruct Hin1 as [E1 | [E2 | [E3 | E4]]].
    + discriminate E1.
    + discriminate E2.
    + discriminate E3.
    + inversion E4.
Qed.