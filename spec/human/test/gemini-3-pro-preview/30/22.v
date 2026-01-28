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
  problem_30_spec [0; 1; 1; 2; -2; 3; -3; 4; -4] [1; 1; 2; 3; 4].
Proof.
  unfold problem_30_spec.
  split.
  - (* Part 1: Verify is_subsequence *)
    simpl.
    right. (* Skip 0 *)
    left. split. { reflexivity. } (* Match 1 *)
    left. split. { reflexivity. } (* Match 1 *)
    left. split. { reflexivity. } (* Match 2 *)
    right. (* Skip -2 *)
    left. split. { reflexivity. } (* Match 3 *)
    right. (* Skip -3 *)
    left. split. { reflexivity. } (* Match 4 *)
    simpl. trivial. (* Base case *)
    
  - (* Part 2: Verify filtering logic *)
    intros r.
    split.
    + (* Forward: In output -> In input /\ r > 0 *)
      intros H_in_out.
      simpl in H_in_out.
      destruct H_in_out as [H | [H | [H | [H | [H | H]]]]]; subst.
      * (* r = 1 *)
        split.
        -- simpl. right. left. reflexivity.
        -- unfold is_positive. apply IZR_lt. simpl. reflexivity.
      * (* r = 1 *)
        split.
        -- simpl. right. right. left. reflexivity.
        -- unfold is_positive. apply IZR_lt. simpl. reflexivity.
      * (* r = 2 *)
        split.
        -- simpl. right. right. right. left. reflexivity.
        -- unfold is_positive. apply IZR_lt. simpl. reflexivity.
      * (* r = 3 *)
        split.
        -- simpl. right. right. right. right. right. left. reflexivity.
        -- unfold is_positive. apply IZR_lt. simpl. reflexivity.
      * (* r = 4 *)
        split.
        -- simpl. right. right. right. right. right. right. right. left. reflexivity.
        -- unfold is_positive. apply IZR_lt. simpl. reflexivity.
      * (* False *)
        contradiction.
        
    + (* Backward: In input /\ r > 0 -> In output *)
      intros [H_in_in H_pos].
      simpl in H_in_in.
      destruct H_in_in as [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]]; subst.
      * (* r = 0 *)
        unfold is_positive in H_pos.
        apply Rgt_lt in H_pos.
        apply lt_IZR in H_pos.
        simpl in H_pos. discriminate.
      * (* r = 1 *)
        simpl. left. reflexivity.
      * (* r = 1 *)
        simpl. right. left. reflexivity.
      * (* r = 2 *)
        simpl. right. right. left. reflexivity.
      * (* r = -2 *)
        unfold is_positive in H_pos.
        apply Rgt_lt in H_pos.
        apply lt_IZR in H_pos.
        simpl in H_pos. discriminate.
      * (* r = 3 *)
        simpl. right. right. right. left. reflexivity.
      * (* r = -3 *)
        unfold is_positive in H_pos.
        apply Rgt_lt in H_pos.
        apply lt_IZR in H_pos.
        simpl in H_pos. discriminate.
      * (* r = 4 *)
        simpl. right. right. right. right. left. reflexivity.
      * (* r = -4 *)
        unfold is_positive in H_pos.
        apply Rgt_lt in H_pos.
        apply lt_IZR in H_pos.
        simpl in H_pos. discriminate.
      * (* False *)
        contradiction.
Qed.