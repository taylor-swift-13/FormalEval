Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [-5; 0; 0; 0; -4; 0; 0; -1; 1; 1; -5] [0; 0; 0; -16; 0; 0; -7; 8; 9; -50].
Proof.
  unfold derivative_spec.
  split.
  
  - (* Part 1: Verify the length condition *)
    simpl. 
    reflexivity.
    
  - (* Part 2: Verify the element-wise calculation *)
    intros i H.
    simpl in H.
    
    do 10 (destruct i; [ simpl; reflexivity | ]).
    
    (* i >= 10 *)
    lia.
Qed.