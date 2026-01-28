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
  [-2.8; 3.5; 10.2; -2.8; 1.1; -4.4; -4.5; -5; 3.5; -5; 1.1; -5] 
  [3.5; 20.4; -8.4; 4.4; -22.0; -27.0; -35; 28.0; -45; 11.0; -55].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    do 11 (destruct i as [|i]; [ simpl; lra | ]).
    lia.
Qed.