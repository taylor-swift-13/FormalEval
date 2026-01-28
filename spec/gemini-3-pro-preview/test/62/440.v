Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [10; -25; 0; 63; -40; 5; 0; 10; 0; 1; 5; 1] [-25; 0; 189; -160; 25; 0; 70; 0; 9; 50; 11].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    do 11 (destruct i as [|i]; [ simpl; reflexivity | ]).
    lia.
Qed.