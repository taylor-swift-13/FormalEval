Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [5; 0; 1; 0; 1; -25; 1; 0; -5; -2; 9; 0; 1; -25; 0; 0; 1; -5] [0; 2; 0; 4; -125; 6; 0; -40; -18; 90; 0; 12; -325; 0; 0; 16; -85].
Proof.
  unfold derivative_spec.
  split.
  - reflexivity.
  - intros i H.
    do 17 (destruct i; [ vm_compute; reflexivity | ]).
    vm_compute in H. lia.
Qed.