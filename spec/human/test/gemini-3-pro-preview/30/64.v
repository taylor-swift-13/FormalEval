Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Import ListNotations.
Open Scope R_scope.

Fixpoint is_subsequence {A : Type} (l1 l2 : list A) : Prop :=
  match l1, l2 with
  | [], _ => True
  | _, [] => False
  | x :: xs, y :: ys =>
      (x = y /\ is_subsequence xs ys) \/ is_subsequence l1 ys
  end.

Definition is_positive (r : R) : Prop :=
  r > 0.

Definition problem_30_pre (input : list R) : Prop := True.

Definition problem_30_spec (input : list R) (output : list R) : Prop :=
  is_subsequence output input /\
  (forall r, In r output <-> (In r input /\ is_positive r)).

Example test_problem_30 :
  problem_30_spec [10; 15; -3; 20; -20; 8; -25; 20] [10; 15; 20; 8; 20].
Proof.
  unfold problem_30_spec.
  split.
  - simpl.
    left. split. { reflexivity. }
    left. split. { reflexivity. }
    right.
    left. split. { reflexivity. }
    right.
    left. split. { reflexivity. }
    right.
    left. split. { reflexivity. }
    simpl. trivial.
    
  - intros r.
    split.
    + intros H_in_out.
      simpl in H_in_out.
      destruct H_in_out as [H | [H | [H | [H | [H | H]]]]]; subst.
      * split.
        -- simpl. left. reflexivity.
        -- unfold is_positive. apply IZR_lt. simpl. reflexivity.
      * split.
        -- simpl. right. left. reflexivity.
        -- unfold is_positive. apply IZR_lt. simpl. reflexivity.
      * split.
        -- simpl. right. right. right. left. reflexivity.
        -- unfold is_positive. apply IZR_lt. simpl. reflexivity.
      * split.
        -- simpl. right. right. right. right. right. left. reflexivity.
        -- unfold is_positive. apply IZR_lt. simpl. reflexivity.
      * split.
        -- simpl. right. right. right. left. reflexivity.
        -- unfold is_positive. apply IZR_lt. simpl. reflexivity.
      * contradiction.
        
    + intros [H_in_in H_pos].
      simpl in H_in_in.
      destruct H_in_in as [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]; subst.
      * simpl. left. reflexivity.
      * simpl. right. left. reflexivity.
      * unfold is_positive in H_pos.
        apply Rgt_lt in H_pos.
        apply lt_IZR in H_pos.
        simpl in H_pos. discriminate.
      * simpl. right. right. left. reflexivity.
      * unfold is_positive in H_pos.
        apply Rgt_lt in H_pos.
        apply lt_IZR in H_pos.
        simpl in H_pos. discriminate.
      * simpl. right. right. right. left. reflexivity.
      * unfold is_positive in H_pos.
        apply Rgt_lt in H_pos.
        apply lt_IZR in H_pos.
        simpl in H_pos. discriminate.
      * simpl. right. right. left. reflexivity.
      * contradiction.
Qed.