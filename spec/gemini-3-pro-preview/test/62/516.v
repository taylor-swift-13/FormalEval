Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [5; 3; 1; 0; -1; -3; -5; 62; -26; 62] [3; 2; 0; -4; -15; -30; 434; -208; 558].
Proof.
  unfold derivative_spec.
  split.
  
  - (* Part 1: Verify the length condition *)
    simpl. 
    reflexivity.
    
  - (* Part 2: Verify the element-wise calculation *)
    intros i H.
    simpl in H.
    
    (* Iterate through indices 0 to 8 *)
    do 9 (destruct i; [ simpl; reflexivity | ]).
    
    (* i >= 9 contradicts H *)
    lia.
Qed.