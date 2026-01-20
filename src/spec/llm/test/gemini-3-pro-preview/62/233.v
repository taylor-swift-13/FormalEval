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
  [0%Z; 1%Z; 0%Z; -25%Z; 1%Z; 0%Z; -5%Z; -2%Z; 9%Z; 0%Z; 1%Z; 0%Z; 0%Z; 0%Z] 
  [1%Z; 0%Z; -75%Z; 4%Z; 0%Z; -30%Z; -14%Z; 72%Z; 0%Z; 10%Z; 0%Z; 0%Z; 0%Z].
Proof.
  unfold derivative_spec.
  split.
  - reflexivity.
  - intros i H.
    do 13 (destruct i; [ vm_compute; reflexivity | ]).
    vm_compute in H.
    lia.
Qed.