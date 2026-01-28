Require Import List.
Require Import Reals.
Require Import Psatz.
Require Import Lia.
Import ListNotations.

Open Scope R_scope.

Definition derivative_spec (xs : list R) (result : list R) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * INR (S i).

Example test_derivative: derivative_spec 
  [3.6845190419876506; 6.8; 6.8; 1.8861584708109862; 3.5; -2.8; 1.1; -4.4; -4.5; -5; 3.5; 0] 
  [6.8; 13.6; 5.6584754124329586; 14.0; -14.0; 6.6; -30.8; -36.0; -45; 35.0; 0].
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