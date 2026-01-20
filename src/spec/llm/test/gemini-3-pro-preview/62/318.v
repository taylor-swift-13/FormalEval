Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [10; -25; 0; 63; -40; 0; 10; 0; 64; 5; 10; 10] [-25; 0; 189; -160; 0; 60; 0; 512; 45; 100; 110].
Proof.
  unfold derivative_spec.
  split.
  - reflexivity.
  - intros i H.
    do 11 (destruct i; [ vm_compute; reflexivity | ]).
    simpl in H. lia.
Qed.