Require Import List.
Require Import Reals.
Require Import Lia.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Definition derivative_spec (xs : list R) (result : list R) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * INR (S i).

Example test_derivative: derivative_spec [-4; 0; 3.5; 6.8; 9; 6.8; 6.8; 6.8] [0; 7.0; 20.4; 36; 34.0; 40.8; 47.6].
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
                 --- destruct i as [|i].
                     +++ simpl. lra.
                     +++ lia.
Qed.