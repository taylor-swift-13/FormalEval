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
  [1.5; -2; 4.398225143948116; 0; 3.14; -5; 0; 1; 1.2; 0; -4.5; 0; 2] 
  [-2; 8.796450287896232; 0; 12.56; -25; 0; 7; 9.6; 0; -45; 0; 24].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    do 12 (destruct i; [ simpl; lra | ]).
    lia.
Qed.