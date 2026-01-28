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
  [0; 1; 0; -1; 0; 0; 0; -40; 0; 3; 0; 0; -25] 
  [1; 0; -3; 0; 0; 0; -280; 0; 27; 0; 0; -300].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    do 12 (destruct i; [ vm_compute; reflexivity | ]).
    lia.
Qed.