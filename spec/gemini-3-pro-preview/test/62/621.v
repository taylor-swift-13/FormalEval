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

Example test_derivative: derivative_spec [1; -4; 0; 2.5; 7.7663698979753315; 9; 10.2] [-4; 0; 7.5; 31.065479591901326; 45; 61.2].
Proof.
  unfold derivative_spec.
  split.
  
  - simpl. reflexivity.
    
  - intros i H.
    simpl in H.
    
    destruct i.
    + simpl. lra.
    + destruct i.
      * simpl. lra.
      * destruct i.
        -- simpl. lra.
        -- destruct i.
           ++ simpl. lra.
           ++ destruct i.
              ** simpl. lra.
              ** destruct i.
                 --- simpl. lra.
                 --- lia.
Qed.