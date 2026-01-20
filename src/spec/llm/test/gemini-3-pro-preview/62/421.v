Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [0; 3; -5; 1; 0; 0; 9; 0; 1; 1; 1; 0] [3; -10; 3; 0; 0; 54; 0; 8; 9; 10; 0].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 11 (destruct i as [|i]; [ vm_compute; reflexivity | ]).
    simpl in H. lia.
Qed.