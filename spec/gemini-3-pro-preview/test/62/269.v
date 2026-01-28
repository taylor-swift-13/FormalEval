Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope R_scope.

Definition derivative_spec (xs : list R) (result : list R) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * INR (S i).

Example test_derivative: derivative_spec [3.5; -2.8; 1.1; -4.4; 0; 3.5; 3.5] [-2.8; 2.2; -13.2; 0; 17.5; 21].
Proof.
  (* Unfold the specification definition *)
  unfold derivative_spec.
  split.
  
  - (* Part 1: Verify the length condition *)
    simpl. 
    reflexivity.
    
  - (* Part 2: Verify the element-wise calculation *)
    intros i H.
    simpl in H. (* Simplifies length result to 6, so H is i < 6 *)
    
    (* We iterate through the specific indices 0 to 5 *)
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
                 --- (* i >= 6 *)
                     (* This case contradicts the hypothesis H : i < 6 *)
                     lia.
Qed.