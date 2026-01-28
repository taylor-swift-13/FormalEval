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
  problem_54_spec "abcdeadbbcccddddeeeeehelabdcba" "54321" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H.
    intros ch.
    split; intros; inversion H.
  - intros Hall.
    pose (Hall "a") as Hiff.
    destruct Hiff as [Hto Hfrom].
    assert (Hin1 : In "a" (list_ascii_of_string "54321")).
    { apply Hto. simpl. left. reflexivity. }
    exfalso.
    simpl in Hin1.
    destruct Hin1 as [H|H]. { discriminate H. }
    destruct H as [H|H]. { discriminate H. }
    destruct H as [H|H]. { discriminate H. }
    destruct H as [H|H]. { discriminate H. }
    destruct H as [H|H]. { discriminate H. }
    inversion H.
Qed.