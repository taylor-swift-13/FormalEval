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
  [1; -2; 0; 3.14; -5; 0; 1.2; 0; -6; -4.5; 0; 2; -4.5; 2] 
  [-2; 0; 9.42; -20; 0; 7.2; 0; -48; -40.5; 0; 22; -54; 26].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    do 13 (destruct i; [ simpl; lra | ]).
    lia.
Qed.