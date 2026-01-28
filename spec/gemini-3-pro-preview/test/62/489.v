Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [9; 5; -5; 10; -2; 0; 0; 11; 5; -5] [5; -10; 30; -8; 0; 0; 77; 40; -45].
Proof.
  (* Unfold the specification definition *)
  unfold derivative_spec.
  split.
  
  - (* Part 1: Verify the length condition *)
    simpl. 
    reflexivity.
    
  - (* Part 2: Verify the element-wise calculation *)
    intros i H.
    simpl in H.
    
    (* We iterate through the specific indices *)
    do 9 (destruct i; [ simpl; reflexivity | ]).
    
    (* This case contradicts the hypothesis H *)
    lia.
Qed.