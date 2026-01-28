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

Example test_derivative: derivative_spec [3.5; -2.8; 1.1; -4.4; 1; 1.1; -4.4] [-2.8; 2.2; -13.2; 4; 5.5; -26.4].
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
           ++ destruct i as [|i].
              ** simpl. lra.
              ** destruct i as [|i].
                 --- simpl. lra.
                 --- lia.
Qed.