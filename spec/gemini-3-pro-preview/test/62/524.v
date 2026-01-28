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
  [1; 2; 2.5; 6.8; 9; 10.6640235766586; 10.2; 1.5; -4; 11.093256507253008; 10.2; 1.5] 
  [2; 5; 20.4; 36; 53.320117883293; 61.2; 10.5; -32; 99.839308565277072; 102; 16.5].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 11 (destruct i; [ simpl; lra | ]).
    simpl in H. lia.
Qed.