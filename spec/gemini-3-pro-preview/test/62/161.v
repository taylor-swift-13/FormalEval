Require Import Coq.ZArith.ZArith.
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

Definition input : list R := [
  3.6845190419876506;
  6.8;
  1.8861584708109862;
  3.5;
  -2.8;
  1.1;
  -4.4;
  -4.5;
  -5;
  3.5;
  0
].

Definition output : list R := [
  6.8;
  3.7723169416219724;
  10.5;
  -11.2;
  5.5;
  -26.4;
  -31.5;
  -40;
  31.5;
  0
].

Example test_derivative: derivative_spec input output.
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    unfold input, output.
    destruct i. { simpl. lra. }
    destruct i. { simpl. lra. }
    destruct i. { simpl. lra. }
    destruct i. { simpl. lra. }
    destruct i. { simpl. lra. }
    destruct i. { simpl. lra. }
    destruct i. { simpl. lra. }
    destruct i. { simpl. lra. }
    destruct i. { simpl. lra. }
    destruct i. { simpl. lra. }
    simpl in H. lia.
Qed.