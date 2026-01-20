Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [9; -5; -25; 2; -40; 10; -2; 4] [-5; -50; 6; -160; 50; -12; 28].
Proof.
  (* Unfold the specification definition *)
  unfold derivative_spec.
  split.
  
  - (* Part 1: Verify the length condition *)
    simpl. 
    reflexivity.
    
  - (* Part 2: Verify the element-wise calculation *)
    intros i H.
    simpl in H. (* Simplifies length result to 7, so H is i < 7 *)
    
    (* We iterate through the specific indices 0 to 6 *)
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
                 --- (* i = 5 *)
                     simpl. reflexivity.
                 --- destruct i.
                     +++ (* i = 6 *)
                         simpl. reflexivity.
                     +++ (* i >= 7 *)
                         (* This case contradicts the hypothesis H : i < 7 *)
                         lia.
Qed.