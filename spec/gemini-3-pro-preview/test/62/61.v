Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec 
  [0; -1; 0; 0; 6; 0; 0; 0; 0; 7; 0; 0; 1; 8; 0; 0] 
  [-1; 0; 0; 24; 0; 0; 0; 0; 63; 0; 0; 12; 104; 0; 0].
Proof.
  unfold derivative_spec.
  split.
  - reflexivity.
  - intros i H.
    do 15 (destruct i; [ vm_compute; reflexivity | ]).
    vm_compute in H. lia.
Qed.