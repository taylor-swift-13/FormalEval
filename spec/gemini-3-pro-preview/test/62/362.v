Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [-3; -25; -1; 63; -40; 0; 10; 0; 5; -1; 63] [-25; -2; 189; -160; 0; 60; 0; 40; -9; 630].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 10 (destruct i; [ simpl; reflexivity | ]).
    simpl in H. lia.
Qed.