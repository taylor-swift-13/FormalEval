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
  [-2.8; 3.5; -2.8; 1.1; -4.4; -4.5; -5; 3.5; -5; 1.1; -5] 
  [3.5; -5.6; 3.3; -17.6; -22.5; -30; 24.5; -40; 9.9; -50].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    destruct i; [simpl; lra |].
    destruct i; [simpl; lra |].
    destruct i; [simpl; lra |].
    destruct i; [simpl; lra |].
    destruct i; [simpl; lra |].
    destruct i; [simpl; lra |].
    destruct i; [simpl; lra |].
    destruct i; [simpl; lra |].
    destruct i; [simpl; lra |].
    destruct i; [simpl; lra |].
    lia.
Qed.