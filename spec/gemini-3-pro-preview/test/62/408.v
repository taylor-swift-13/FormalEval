Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [1; 0; 0; -1; 4; 0; 0; 5; 0; 63; 63; 0; 0; 63; 0; -7; 0; 63; 0; 1; 1] [0; 0; -3; 16; 0; 0; 35; 0; 567; 630; 0; 0; 819; 0; -105; 0; 1071; 0; 19; 20].
Proof.
  unfold derivative_spec.
  split.
  - reflexivity.
  - intros i H.
    do 20 (destruct i as [|i]; [ vm_compute; reflexivity | ]).
    simpl in H. lia.
Qed.