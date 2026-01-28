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

Example test_derivative: derivative_spec 
  [1; -4; 0; 62; -4.5; -2.413995463147514; 3.4009590491925366; 0] 
  [-4; 0; 186; -18.0; -12.06997731573757; 20.4057542951552196; 0].
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
                 --- destruct i.
                     +++ simpl. lra.
                     +++ lia.
Qed.