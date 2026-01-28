Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [1; 1; 0; 1; 0; 9; 0; 1; 2; 0; 1; -7; 0; 10; 0; 1] [1; 0; 3; 0; 45; 0; 7; 16; 0; 10; -77; 0; 130; 0; 15].
Proof.
  unfold derivative_spec.
  split.
  - reflexivity.
  - intros i H.
    do 15 (destruct i; [ vm_compute; reflexivity | ]).
    simpl in H.
    lia.
Qed.