Require Import List.
Require Import Reals.
Require Import Lra.
Require Import Lia.
Import ListNotations.

Open Scope R_scope.

Definition derivative_spec (xs : list R) (result : list R) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * INR (S i).

Definition xs : list R := [
  36845190419876506 / 10000000000000000;
  68 / 10;
  18861584708109862 / 10000000000000000;
  35 / 10;
  -28 / 10;
  11 / 10;
  -44 / 10;
  -45 / 10;
  -5;
  35 / 10;
  0
].

Definition res : list R := [
  68 / 10;
  37723169416219724 / 10000000000000000;
  105 / 10;
  -112 / 10;
  55 / 10;
  -264 / 10;
  -315 / 10;
  -40;
  315 / 10;
  0
].

Example test_derivative: derivative_spec xs res.
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    simpl in Hi.
    do 10 (destruct i; [simpl; lra | ]).
    lia.
Qed.