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

Example test_derivative: derivative_spec 
  [1; -4; 0; 2.5; 6.8; -4; 9; 10.61599760044726; 10.2; -4; -4] 
  [-4; 0; 7.5; 27.2; -20; 54; 74.31198320313082; 81.6; -36; -40].
Proof.
  (* Unfold the specification definition *)
  unfold derivative_spec.
  split.
  
  - (* Part 1: Verify the length condition *)
    simpl. 
    reflexivity.
    
  - (* Part 2: Verify the element-wise calculation *)
    intros i H.
    simpl in H. (* Simplifies length result to 10, so H is i < 10 *)
    
    (* We iterate through the specific indices 0 to 9 *)
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
                     +++ destruct i.
                         *** (* i = 7 *)
                             simpl. lra.
                         *** destruct i.
                             ---- (* i = 8 *)
                                  simpl. lra.
                             ---- destruct i.
                                  ++++ (* i = 9 *)
                                       simpl. lra.
                                  ++++ (* i >= 10 *)
                                       (* This case contradicts the hypothesis H : i < 10 *)
                                       lia.
Qed.