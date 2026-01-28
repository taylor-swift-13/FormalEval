Require Import List.
Require Import Reals.
Require Import Lra.
Require Import Lia.
Import ListNotations.

Open Scope R_scope.

Definition derivative_spec (xs : list R) (result : list R) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * INR (S i).

Example test_derivative: derivative_spec [1; -5; -4; 0; -4; 2.5; 6.8; 9; 3.5] [-5; -8; 0; -16; 12.5; 40.8; 63; 28].
Proof.
  (* Unfold the specification definition *)
  unfold derivative_spec.
  split.
  
  - (* Part 1: Verify the length condition *)
    simpl. 
    reflexivity.

  - (* Part 2: Verify the element-wise calculation *)
    intros i Hi.
    simpl in Hi. 
    
    (* Perform case analysis on i *)
    destruct i as [|i].
    + (* i = 0 *)
      simpl. lra.
    + destruct i as [|i].
      * (* i = 1 *)
        simpl. lra.
      * destruct i as [|i].
        -- (* i = 2 *)
           simpl. lra.
        -- destruct i as [|i].
           ++ (* i = 3 *)
              simpl. lra.
           ++ destruct i as [|i].
              ** (* i = 4 *)
                 simpl. lra.
              ** destruct i as [|i].
                 --- (* i = 5 *)
                     simpl. lra.
                 --- destruct i as [|i].
                     +++ (* i = 6 *)
                         simpl. lra.
                     +++ destruct i as [|i].
                         *** (* i = 7 *)
                             simpl. lra.
                         *** (* i >= 8 *)
                             lia.
Qed.