Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [-1; 0; -2; 0; 9; 0; 0; 0; -1; 0; -1; -4] [0; -4; 0; 36; 0; 0; 0; -8; 0; -10; -44].
Proof.
  unfold derivative_spec.
  split.
  
  - simpl. 
    reflexivity.
    
  - intros i H.
    simpl in H.
    do 11 (destruct i; [ simpl; reflexivity | ]).
    lia.
Qed.