Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition derivative_spec (xs : list R) (result : list R) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * INR (S i).

Example test_derivative: derivative_spec [1; -5; -4; 0; 5/2; 34/5; 9; 7/2] [-5; -8; 0; 10; 34; 54; 49/2].
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
      simpl. lra.
    + destruct i.
      * (* i = 1 *)
        simpl. lra.
      * destruct i.
        -- (* i = 2 *)
           simpl. lra.
        -- destruct i.
           ++ (* i = 3 *)
              simpl. lra.
           ++ destruct i.
              ** (* i = 4 *)
                 simpl. lra.
              ** destruct i.
                 --- (* i = 5 *)
                     simpl. lra.
                 --- destruct i.
                     +++ (* i = 6 *)
                         simpl. lra.
                     +++ (* i >= 7 *)
                         (* This case contradicts the hypothesis H : i < 7 *)
                         lia.
Qed.