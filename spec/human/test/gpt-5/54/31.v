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
  problem_54_spec "ab54321fg" "gfedcba" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. exfalso. discriminate H.
  - intros Hall.
    exfalso.
    pose proof (Hall "e"%char) as He.
    destruct He as [Hlr Hrl].
    assert (Hin_s1 : In "e"%char (list_ascii_of_string "gfedcba")).
    { simpl. right. right. left. reflexivity. }
    assert (Hnot : ~ In "e"%char (list_ascii_of_string "ab54321fg")).
    { intros Hin. simpl in Hin.
      destruct Hin as [H|Hin]; [inversion H|].
      destruct Hin as [H|Hin]; [inversion H|].
      destruct Hin as [H|Hin]; [inversion H|].
      destruct Hin as [H|Hin]; [inversion H|].
      destruct Hin as [H|Hin]; [inversion H|].
      destruct Hin as [H|Hin]; [inversion H|].
      destruct Hin as [H|Hin]; [inversion H|].
      destruct Hin as [H|Hin]; [inversion H|].
      destruct Hin as [H|Hin]; [inversion H|].
      inversion Hin. }
    apply Hnot. apply Hrl. exact Hin_s1.
Qed.