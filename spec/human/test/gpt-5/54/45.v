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
  problem_54_spec "abcdcb5143241a514321de" "abcdcbadcbade" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. exfalso. discriminate H.
  - intros Hall. exfalso.
    assert (Hin0 : In "1"%char (list_ascii_of_string "abcdcb5143241a514321de")).
    { simpl. right. right. right. right. right. right. right.
      left. reflexivity. }
    specialize (Hall "1"%char).
    destruct Hall as [Hlr Hrl].
    assert (Hin_s1 : In "1"%char (list_ascii_of_string "abcdcbadcbade")).
    { apply Hlr. exact Hin0. }
    simpl in Hin_s1.
    destruct Hin_s1 as [H|H]; [discriminate H|].
    destruct H as [H|H]; [discriminate H|].
    destruct H as [H|H]; [discriminate H|].
    destruct H as [H|H]; [discriminate H|].
    destruct H as [H|H]; [discriminate H|].
    destruct H as [H|H]; [discriminate H|].
    destruct H as [H|H]; [discriminate H|].
    destruct H as [H|H]; [discriminate H|].
    destruct H as [H|H]; [discriminate H|].
    destruct H as [H|H]; [discriminate H|].
    destruct H as [H|H]; [discriminate H|].
    destruct H as [H|H]; [discriminate H|].
    destruct H as [H|H]; [discriminate H|].
    inversion H.
Qed.