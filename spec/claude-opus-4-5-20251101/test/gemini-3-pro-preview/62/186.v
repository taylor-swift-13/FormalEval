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
  [10; 1; -4; 0; 63; -4.5; -4.4; 6.8] 
  [1; -8; 0; 252; -22.5; -26.4; 47.6].
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