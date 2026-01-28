Require Import List.
Require Import Reals.
Require Import Lra.
Require Import Lia.
Import ListNotations.

Open Scope R_scope.

Definition derivative_spec (xs : list R) (result : list R) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0%R = nth (S i) xs 0%R * INR (S i).

Example test_derivative: derivative_spec [3.5%R; -2.8%R; 1.1%R; -4.4%R; 1.1%R] [-2.8%R; 2.2%R; -13.2%R; 4.4%R].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    simpl in Hi.
    destruct i as [|i].
    + simpl. lra.
    + destruct i as [|i].
      * simpl. lra.
      * destruct i as [|i].
        -- simpl. lra.
        -- destruct i as [|i].
           ++ simpl. lra.
           ++ lia.
Qed.