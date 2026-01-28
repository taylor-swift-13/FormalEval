Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_90_pre (l : list Z) : Prop := True.

Definition problem_90_spec (l : list Z) (res : option Z) : Prop :=
  match res with
  | Some z =>
    exists s1,
      In s1 l /\
      (forall x, In x l -> s1 <= x) /\
      In z l /\
      s1 < z /\
      (forall y, In y l -> s1 < y -> z <= y)
  | None =>
    ~ (exists x y, In x l /\ In y l /\ x <> y)
  end.

Example problem_90_example :
  problem_90_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z] (Some 2%Z).
Proof.
  unfold problem_90_spec.
  exists 1%Z.
  split.
  - simpl; auto.
  - split.
    + intros x H. simpl in H. destruct H as [H1 | [H2 | [H3 | [H4 | [H5 | []]]]]]; subst; omega.
    + split.
      * simpl; auto.
      * split.
        { omega. }
        { intros y H H0. simpl in H. destruct H as [H1 | [H2 | [H3 | [H4 | [H5 | []]]]]]; subst; omega. }
Qed.