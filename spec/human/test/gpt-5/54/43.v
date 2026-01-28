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
  problem_54_spec "llo" "helleo" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H.
    exfalso.
    discriminate H.
  - intros Hprop.
    exfalso.
    specialize (Hprop "h").
    simpl in Hprop.
    assert (Hin1 : In "h" ("h" :: "e" :: "l" :: "l" :: "e" :: "o" :: [])).
    { simpl. left. reflexivity. }
    apply (proj2 Hprop) in Hin1.
    simpl in Hin1.
    destruct Hin1 as [H1|[H2|[H3|H4]]].
    + discriminate H1.
    + discriminate H2.
    + discriminate H3.
    + inversion H4.
Qed.