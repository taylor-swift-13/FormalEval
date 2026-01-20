Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [2; 0; 4; 3; -2; 0; 1; 1; 0; -2; 0; 6; 2; 0] [0; 8; 9; -8; 0; 6; 7; 0; -18; 0; 66; 24; 0].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    do 13 (destruct i as [|i]; [ simpl; reflexivity | ]).
    lia.
Qed.