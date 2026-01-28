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
  problem_54_spec "eabcdzzzz" "dddzzzzzzzddeddabc" true.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros _. (* We prove the bi-implication of membership for all ascii chars *)
    intros ch.
    split.
    + (* In ch left -> In ch right *)
      simpl.
      intros H.
      simpl in H.
      destruct H as [H|H].
      { subst.
        simpl.
        right. right. right. right. right. right. right. right. right. right. right. right.
        left. reflexivity.
      }
      destruct H as [H|H].
      { subst.
        simpl.
        right. right. right. right. right. right. right. right. right. right. right. right.
        right. right. right.
        left. reflexivity.
      }
      destruct H as [H|H].
      { subst.
        simpl.
        right. right. right. right. right. right. right. right. right. right. right. right.
        right. right. right. right.
        left. reflexivity.
      }
      destruct H as [H|H].
      { subst.
        simpl.
        right. right. right. right. right. right. right. right. right. right. right. right.
        right. right. right. right. right.
        left. reflexivity.
      }
      destruct H as [H|H].
      { subst.
        simpl. left. reflexivity.
      }
      destruct H as [H|H].
      { subst.
        simpl. right. right. right. left. reflexivity.
      }
      destruct H as [H|H].
      { subst.
        simpl. right. right. right. left. reflexivity.
      }
      destruct H as [H|H].
      { subst.
        simpl. right. right. right. left. reflexivity.
      }
      destruct H as [H|H].
      { subst.
        simpl. right. right. right. left. reflexivity.
      }
      inversion H.
    + (* In ch right -> In ch left *)
      simpl.
      intros H.
      simpl in H.
      destruct H as [H|H].
      { subst. simpl. right. right. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl. right. right. right. right. left. reflexivity. }
      destruct H as [H|H].
      { subst. simpl. right. right. right. right. left. reflexivity. }
      destruct H as [H|H]. (* z #1 *)
      { subst. simpl. right. right. right. right. right. left. reflexivity. }
      destruct H as [H|H]. (* z #2 *)
      { subst. simpl. right. right. right. right. right. left. reflexivity. }
      destruct H as [H|H]. (* z #3 *)
      { subst. simpl. right. right. right. right. right. left. reflexivity. }
      destruct H as [H|H]. (* z #4 *)
      { subst. simpl. right. right. right. right. right. left. reflexivity. }
      destruct H as [H|H]. (* z #5 *)
      { subst. simpl. right. right. right. right. right. left. reflexivity. }
      destruct H as [H|H]. (* z #6 *)
      { subst. simpl. right. right. right. right. right. left. reflexivity. }
      destruct H as [H|H]. (* z #7 *)
      { subst. simpl. right. right. right. right. right. left. reflexivity. }
      destruct H as [H|H]. (* d after z's #1 *)
      { subst. simpl. right. right. right. right. left. reflexivity. }
      destruct H as [H|H]. (* d after z's #2 *)
      { subst. simpl. right. right. right. right. left. reflexivity. }
      destruct H as [H|H]. (* e *)
      { subst. simpl. left. reflexivity. }
      destruct H as [H|H]. (* d after e #1 *)
      { subst. simpl. right. right. right. right. left. reflexivity. }
      destruct H as [H|H]. (* d after e #2 *)
      { subst. simpl. right. right. right. right. left. reflexivity. }
      destruct H as [H|H]. (* a *)
      { subst. simpl. right. left. reflexivity. }
      destruct H as [H|H]. (* b *)
      { subst. simpl. right. right. left. reflexivity. }
      destruct H as [H|H]. (* c *)
      { subst. simpl. right. right. right. left. reflexivity. }
      inversion H.
  - intros _. reflexivity.
Qed.