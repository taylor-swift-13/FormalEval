Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition derivative_spec (xs : list R) (result : list R) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * INR (S i).

Example test_derivative: derivative_spec 
  [3.6845190419876506; 6.8; 6.8; 1.8861584708109862; 3.5; -2.8; 1.1; -4.4; -4.5; -5; 3.5; 0; 3.5] 
  [6.8; 13.6; 5.6584754124329586; 14.0; -14.0; 6.6; -30.8; -36.0; -45; 35.0; 0; 42.0].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    do 12 (destruct i; [ simpl; lra | ]).
    lia.
Qed.