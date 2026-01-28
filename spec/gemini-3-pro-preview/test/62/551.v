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
  [3.6845190419876506; 6.8; -2.413995463147514; 3.5; -2.8; -4.4; -4.5; -5; 3.5; 0; 6.8] 
  [6.8; -4.827990926295028; 10.5; -11.2; -22.0; -27.0; -35; 28.0; 0; 68.0].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    do 10 (destruct i; [ simpl; lra | ]).
    lia.
Qed.