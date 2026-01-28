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
  problem_54_spec "aaabbbccc" "a5432caaaabacababecdeadbecdeadbabcbc" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. exfalso. discriminate H.
  - simpl.
    intros Hprop.
    exfalso.
    specialize (Hprop "5"%char).
    destruct Hprop as [Hlr Hrl].
    assert (In "5"%char (list_ascii_of_string "a5432caaaabacababecdeadbecdeadbabcbc")) as Hin_right.
    { simpl. right. left. reflexivity. }
    pose proof (Hrl Hin_right) as Hin_left.
    simpl in Hin_left.
    destruct Hin_left as [H|Hin_left]; [discriminate H|].
    destruct Hin_left as [H|Hin_left]; [discriminate H|].
    destruct Hin_left as [H|Hin_left]; [discriminate H|].
    destruct Hin_left as [H|Hin_left]; [discriminate H|].
    destruct Hin_left as [H|Hin_left]; [discriminate H|].
    destruct Hin_left as [H|Hin_left]; [discriminate H|].
    destruct Hin_left as [H|Hin_left]; [discriminate H|].
    destruct Hin_left as [H|Hin_left]; [discriminate H|].
    destruct Hin_left as [H|Hin_left]; [discriminate H|].
    inversion Hin_left.
Qed.