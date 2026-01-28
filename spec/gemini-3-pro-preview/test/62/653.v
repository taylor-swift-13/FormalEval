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

Example test_derivative: derivative_spec [1; 2; -4; 0; 2.5; 7.7663698979753315; 9] [2; -8; 0; 10; 38.8318494898766575; 54].
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