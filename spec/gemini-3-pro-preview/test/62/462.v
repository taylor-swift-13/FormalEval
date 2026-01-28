Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [0; 0; 0; 1; 0; 9; 0; 1; 0; 1; 10; 0; 1] [0; 0; 3; 0; 45; 0; 7; 0; 9; 100; 0; 12].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    repeat (destruct i; [ simpl; reflexivity | simpl in H; try lia ]).
Qed.