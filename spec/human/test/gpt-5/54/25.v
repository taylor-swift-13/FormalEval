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
  problem_54_spec "adbbcccddddeeeeehelldefo" "abcde" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H ch.
    split; intros _; exfalso; discriminate H.
  - intros H.
    exfalso.
    specialize (H "h").
    destruct H as [Hlr Hrl].
    assert (Hin0 : In "h" (list_ascii_of_string "adbbcccddddeeeeehelldefo")).
    simpl.
    right. right. right. right. right. right. right. right. right. right. right. right. right. right. right. right.
    left. reflexivity.
    pose proof (Hlr Hin0) as Hin1.
    simpl in Hin1.
    destruct Hin1 as [Ha|Hin1]; [discriminate|].
    destruct Hin1 as [Hb|Hin1]; [discriminate|].
    destruct Hin1 as [Hc|Hin1]; [discriminate|].
    destruct Hin1 as [Hd|Hin1]; [discriminate|].
    destruct Hin1 as [He|Hin1]; [discriminate|].
    inversion Hin1.
Qed.