Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.

Definition Spec(input output : list Z) : Prop :=
  length input = length output /\
  forall i : nat, i < length output -> nth i output 0%Z = ((nth i input 0%Z) + 1)%Z.

Example test_incr_list :
  Spec [100%Z; 200%Z; 300%Z; 400%Z; 500%Z] [101%Z; 201%Z; 301%Z; 401%Z; 501%Z].
Proof.
  unfold Spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    destruct i; simpl; try lia.
    destruct i; simpl; try lia.
    destruct i; simpl; try lia.
    destruct i; simpl; try lia.
    destruct i; simpl; try lia.
Qed.