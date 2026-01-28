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

Example test_derivative: derivative_spec [1.5; -2; 0; 3.14; -5; 0; 1.2; 0; -4.5; 0; 2] [-2; 0; 9.42; -20; 0; 7.2; 0; -36; 0; 20].
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
                     +++ destruct i as [|i].
                         *** simpl. lra.
                         *** destruct i as [|i].
                             ---- simpl. lra.
                             ---- destruct i as [|i].
                                  ++++ simpl. lra.
                                  ++++ lia.
Qed.