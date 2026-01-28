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

Definition is_positive (r : R) : Prop := r > 0.

Definition problem_30_pre (input : list R) : Prop := True.

Definition problem_30_spec (input : list R) (output : list R) : Prop :=
  is_subsequence output input /\
  (forall r, In r output <-> (In r input /\ is_positive r)).

Example test_case_proof :
  problem_30_spec [(-1)%R; (-2)%R; 4%R; 5%R; 6%R] [4%R; 5%R; 6%R].
Proof.
  unfold problem_30_spec.
  split.
  - (* Prove is_subsequence output input *)
    simpl.
    right. right. left.
    split.
    + reflexivity.
    + right. right. left.
      split.
      * reflexivity.
      * right. right. left.
        split.
        { reflexivity. }
        { exact I. }
  - (* Prove the forall equivalence *)
    intro r.
    split.
    + (* Forward direction: In r output -> In r input /\ is_positive r *)
      intro H.
      simpl in H.
      destruct H as [H | H].
      * rewrite H.
        split.
        { simpl. right. right. left. reflexivity. }
        { unfold is_positive. lra. }
      * destruct H as [H | H].
        { rewrite H.
          split.
          { simpl. right. right. right. left. reflexivity. }
          { unfold is_positive. lra. } }
        { rewrite H.
          split.
          { simpl. right. right. right. right. left. reflexivity. }
          { unfold is_positive. lra. } }
    + (* Backward direction: In r input /\ is_positive r -> In r output *)
      intro H.
      destruct H as [H_in H_pos].
      simpl in H_in.
      destruct H_in as [H | H].
      * rewrite H in H_pos.
        unfold is_positive in H_pos.
        lra.
      * destruct H as [H | H].
        { rewrite H in H_pos.
          unfold is_positive in H_pos.
          lra. }
        { destruct H as [H | H].
          { rewrite H.
            simpl. left. reflexivity. }
          { destruct H as [H | H].
            { rewrite H.
              simpl. right. left. reflexivity. }
            { rewrite H.
              simpl. right. right. left. reflexivity. } } }
Qed.