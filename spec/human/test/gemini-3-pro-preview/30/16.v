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
  problem_30_spec [-1; -1; -3; -4; -1] [].
Proof.
  unfold problem_30_spec.
  split.
  - (* Part 1: Verify is_subsequence *)
    simpl. trivial.
    
  - (* Part 2: Verify filtering logic *)
    intros r.
    split.
    + (* Forward: In output -> In input /\ r > 0 *)
      intros H_in_out.
      simpl in H_in_out.
      contradiction.
        
    + (* Backward: In input /\ r > 0 -> In output *)
      intros [H_in_in H_pos].
      simpl in H_in_in.
      destruct H_in_in as [H | [H | [H | [H | [H | H]]]]]; subst.
      * (* r = -1 *)
        unfold is_positive in H_pos.
        apply Rgt_lt in H_pos.
        apply lt_IZR in H_pos.
        simpl in H_pos. discriminate.
      * (* r = -1 *)
        unfold is_positive in H_pos.
        apply Rgt_lt in H_pos.
        apply lt_IZR in H_pos.
        simpl in H_pos. discriminate.
      * (* r = -3 *)
        unfold is_positive in H_pos.
        apply Rgt_lt in H_pos.
        apply lt_IZR in H_pos.
        simpl in H_pos. discriminate.
      * (* r = -4 *)
        unfold is_positive in H_pos.
        apply Rgt_lt in H_pos.
        apply lt_IZR in H_pos.
        simpl in H_pos. discriminate.
      * (* r = -1 *)
        unfold is_positive in H_pos.
        apply Rgt_lt in H_pos.
        apply lt_IZR in H_pos.
        simpl in H_pos. discriminate.
      * (* False *)
        contradiction.
Qed.