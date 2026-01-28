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
  problem_54_spec "5432caaaababecdead" "5432cababecdead" true.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros _.
    intros ch.
    split.
    + simpl.
      intros H.
      simpl in H.
      destruct H as [H|H].
      { subst. simpl. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl. right. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl. right. right. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl. right. right. right. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl. right. right. right. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl. right. right. right. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl. right. right. right. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl. right. right. right. right. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl. right. right. right. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl. right. right. right. right. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl.
        right. right. right. right. right. right. right. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl. right. right. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl.
        right. right. right. right. right. right. right. right. right. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl.
        right. right. right. right. right. right. right. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl. right. right. right. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl.
        right. right. right. right. right. right. right. right. right. right. right. left. reflexivity. }
      inversion H.
    + simpl.
      intros H.
      simpl in H.
      destruct H as [H|H].
      { subst. simpl. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl. right. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl. right. right. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl. right. right. right. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl.
        right. right. right. right. right. right. right. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl. right. right. right. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl.
        right. right. right. right. right. right. right. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl.
        right. right. right. right. right. right. right. right. right. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl. right. right. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl.
        right. right. right. right. right. right. right. right. right. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl.
        right. right. right. right. right. right. right. right. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl. right. right. right. right. right. left. reflexivity. }
      inversion H.
  - intros _. reflexivity.
Qed.