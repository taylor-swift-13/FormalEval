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

Example test_derivative: derivative_spec 
  [-2.8; 3.5; -2.8; 1.1; -4.4; -4.5; -5; 3.5; -5; 1.1; -5]
  [3.5; -5.6; 3.3; -17.6; -22.5; -30; 24.5; -40; 9.9; -50].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    simpl in Hi.
    repeat (destruct i as [|i]; [ simpl; lra | simpl in Hi; try lia ]).
Qed.