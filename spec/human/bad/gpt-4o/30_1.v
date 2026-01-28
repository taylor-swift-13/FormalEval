Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope R_scope.
Open Scope Z_scope.

Fixpoint is_subsequence {A : Type} (l1 l2 : list A) : Prop :=
  match l1, l2 with
  | [], _ => True
  | _, [] => False
  | x :: xs, y :: ys =>
      (x = y /\ is_subsequence xs ys) \/ is_subsequence l1 ys
  end.

Definition is_positive (z : Z) : Prop :=
  z > 0.

Definition problem_30_spec (input : list Z) (output : list Z) : Prop :=
  is_subsequence output input /\
  (forall z, In z output <-> (In z input /\ is_positive z)).

Example test_case_1 :
  let input := [-1; -2; 4; 5; 6] in
  let output := [4; 5; 6] in
  problem_30_spec input output.
Proof.
  unfold problem_30_spec.
  split.
  - simpl. repeat right. left. split; auto.
    repeat right. left. auto.
  - intros z. split; intros H.
    + split.
      * destruct H; subst; simpl; auto.
      * destruct H; subst; simpl; auto; lia.
    + destruct H as [H_in H_pos].
      simpl in H_in.
      destruct H_in as [H_eq | [H_eq | [H_eq | H_in]]]; subst; auto.
Qed.