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
  problem_30_spec [10; 10; -10; 15; -15; 20; -20; 25; -25; 25] [10; 10; 15; 20; 25; 25].
Proof.
  unfold problem_30_spec.
  split.
  - (* Part 1: Verify is_subsequence *)
    simpl.
    left. split. { reflexivity. } (* Match 10 *)
    left. split. { reflexivity. } (* Match 10 *)
    right. (* Skip -10 *)
    left. split. { reflexivity. } (* Match 15 *)
    right. (* Skip -15 *)
    left. split. { reflexivity. } (* Match 20 *)
    right. (* Skip -20 *)
    left. split. { reflexivity. } (* Match 25 *)
    right. (* Skip -25 *)
    left. split. { reflexivity. } (* Match 25 *)
    simpl. trivial.

  - (* Part 2: Verify filtering logic *)
    intros r.
    split.
    + (* Forward: In output -> In input /\ r > 0 *)
      intros H_in_out.
      simpl in H_in_out.
      destruct H_in_out as [H | [H | [H | [H | [H | [H | H]]]]]]; subst.
      * (* r = 10 *)
        split.
        -- simpl. left. reflexivity.
        -- unfold is_positive. apply IZR_lt. simpl. reflexivity.
      * (* r = 10 *)
        split.
        -- simpl. left. reflexivity.
        -- unfold is_positive. apply IZR_lt. simpl. reflexivity.
      * (* r = 15 *)
        split.
        -- simpl. right. right. right. left. reflexivity.
        -- unfold is_positive. apply IZR_lt. simpl. reflexivity.
      * (* r = 20 *)
        split.
        -- simpl. right. right. right. right. right. left. reflexivity.
        -- unfold is_positive. apply IZR_lt. simpl. reflexivity.
      * (* r = 25 *)
        split.
        -- simpl. right. right. right. right. right. right. right. left. reflexivity.
        -- unfold is_positive. apply IZR_lt. simpl. reflexivity.
      * (* r = 25 *)
        split.
        -- simpl. right. right. right. right. right. right. right. left. reflexivity.
        -- unfold is_positive. apply IZR_lt. simpl. reflexivity.
      * (* False *)
        contradiction.

    + (* Backward: In input /\ r > 0 -> In output *)
      intros [H_in_in H_pos].
      simpl in H_in_in.
      destruct H_in_in as [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]]]; subst.
      * (* r = 10 *)
        simpl. left. reflexivity.
      * (* r = 10 *)
        simpl. right. left. reflexivity.
      * (* r = -10 *)
        unfold is_positive in H_pos.
        apply Rgt_lt in H_pos.
        apply lt_IZR in H_pos.
        simpl in H_pos. discriminate.
      * (* r = 15 *)
        simpl. right. right. left. reflexivity.
      * (* r = -15 *)
        unfold is_positive in H_pos.
        apply Rgt_lt in H_pos.
        apply lt_IZR in H_pos.
        simpl in H_pos. discriminate.
      * (* r = 20 *)
        simpl. right. right. right. left. reflexivity.
      * (* r = -20 *)
        unfold is_positive in H_pos.
        apply Rgt_lt in H_pos.
        apply lt_IZR in H_pos.
        simpl in H_pos. discriminate.
      * (* r = 25 *)
        simpl. right. right. right. right. left. reflexivity.
      * (* r = -25 *)
        unfold is_positive in H_pos.
        apply Rgt_lt in H_pos.
        apply lt_IZR in H_pos.
        simpl in H_pos. discriminate.
      * (* r = 25 *)
        simpl. right. right. right. right. right. left. reflexivity.
      * (* False *)
        contradiction.
Qed.