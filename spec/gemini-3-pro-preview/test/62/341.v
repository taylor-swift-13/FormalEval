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
  [1; -4; 2; 2.5; 6.8; 9; 10.2; 1.5; -4; 11.093256507253008; 10.2; 1.5] 
  [-4; 4; 7.5; 27.2; 45; 61.2; 10.5; -32; 99.839308565277072; 102; 16.5].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    do 11 (destruct i; [ simpl; lra | ]).
    lia.
Qed.