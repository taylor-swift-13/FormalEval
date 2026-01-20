Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [10; -25; -1; 63; -40; -5; 0; -3; 4] [-25; -2; 189; -160; -25; 0; -21; 32].
Proof.
  (* Unfold the specification definition *)
  unfold derivative_spec.
  split.
  
  - (* Part 1: Verify the length condition *)
    simpl. 
    reflexivity.
    
  - (* Part 2: Verify the element-wise calculation *)
    intros i H.
    simpl in H. (* Simplifies length result to 8, so H is i < 8 *)
    
    (* We iterate through the specific indices 0 to 7 *)
    destruct i.
    + (* i = 0 *)
      simpl. reflexivity.
    + destruct i.
      * (* i = 1 *)
        simpl. reflexivity.
      * destruct i.
        -- (* i = 2 *)
           simpl. reflexivity.
        -- destruct i.
           ++ (* i = 3 *)
              simpl. reflexivity.
           ++ destruct i.
              ** (* i = 4 *)
                 simpl. reflexivity.
              ** destruct i.
                 *** (* i = 5 *)
                     simpl. reflexivity.
                 *** destruct i.
                     ---- (* i = 6 *)
                          simpl. reflexivity.
                     ---- destruct i.
                          ++++ (* i = 7 *)
                               simpl. reflexivity.
                          ++++ (* i >= 8 *)
                               (* This case contradicts the hypothesis H : i < 8 *)
                               lia.
Qed.