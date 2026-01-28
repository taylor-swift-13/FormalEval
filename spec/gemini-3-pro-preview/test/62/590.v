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
  [1; -4; 0; 2.5; 6.8; 9; 10.2; 1.5; -4; 10.2; 10.2; -4; -4] 
  [-4; 0; 7.5; 27.2; 45; 61.2; 10.5; -32; 91.8; 102; -44; -48].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    do 12 (destruct i as [|i]; [simpl; lra | ]).
    lia.
Qed.