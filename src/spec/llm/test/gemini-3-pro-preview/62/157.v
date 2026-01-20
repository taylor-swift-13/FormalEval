Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [-7; 3; 1; 0; -1; -3; -5; -7; -8; -9; 3; -5] [3; 2; 0; -4; -15; -30; -49; -64; -81; 30; -55].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 11 (destruct i; [simpl; reflexivity | ]).
    simpl in H. lia.
Qed.