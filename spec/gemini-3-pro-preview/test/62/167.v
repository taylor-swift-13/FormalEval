Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [-1; 0; 63; 0; 0; 9; 0; 0; 0; 0; -1; 1] [0; 126; 0; 0; 45; 0; 0; 0; 0; -10; 11].
Proof.
  unfold derivative_spec.
  split.
  - reflexivity.
  - intros i H.
    do 11 (destruct i; [ vm_compute; reflexivity | ]).
    simpl in H. lia.
Qed.