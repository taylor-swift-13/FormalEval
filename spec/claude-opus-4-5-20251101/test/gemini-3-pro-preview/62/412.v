Require Import List.
Require Import Reals.
Require Import Psatz.
Require Import Lia.
Import ListNotations.

Open Scope R_scope.

Definition derivative_spec (xs : list R) (result : list R) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * INR (S i).

Example test_derivative: derivative_spec 
  [3.6845190419876506; 1; -5; -4; -4.5; 6.135053916071352] 
  [1; -10; -12; -18; 30.67526958035676].
Proof.
  unfold derivative_spec.
  split.
  
  - simpl. reflexivity.

  - intros i Hi.
    simpl in Hi.
    
    destruct i as [|i].
    + simpl. lra.
    + destruct i as [|i].
      * simpl. lra.
      * destruct i as [|i].
        -- simpl. lra.
        -- destruct i as [|i].
           ++ simpl. lra.
           ++ destruct i as [|i].
              ** simpl. lra.
              ** lia.
Qed.