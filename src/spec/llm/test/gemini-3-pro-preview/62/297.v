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
  [1; 0; 0; -1; 0; 10; 0; 0; 0; 0; 63; 0; -7; 0; 10; 0; 1; 0] 
  [0; 0; -3; 0; 50; 0; 0; 0; 0; 630; 0; -84; 0; 140; 0; 16; 0].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H. simpl in H.
    do 17 (destruct i; [ vm_compute; reflexivity | ]).
    lia.
Qed.