Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [10; -25; 0; 0; 10; -40; -2; 5; 10; -40; 10] [-25; 0; 0; 40; -200; -12; 35; 80; -360; 100].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 10 (destruct i; [ simpl; reflexivity | ]).
    simpl in H. lia.
Qed.