Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [10; 3; 1; 0; -3; -1; -3; -5; -7; -9; -5; -3] [3; 2; 0; -12; -5; -18; -35; -56; -81; -50; -33].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    destruct i. simpl. reflexivity.
    destruct i. simpl. reflexivity.
    destruct i. simpl. reflexivity.
    destruct i. simpl. reflexivity.
    destruct i. simpl. reflexivity.
    destruct i. simpl. reflexivity.
    destruct i. simpl. reflexivity.
    destruct i. simpl. reflexivity.
    destruct i. simpl. reflexivity.
    destruct i. simpl. reflexivity.
    destruct i. simpl. reflexivity.
    lia.
Qed.