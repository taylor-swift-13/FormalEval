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

Example test_derivative: derivative_spec [1; -4; 0; 63; -4.5; -4.4; -1; 6.8; 10] [-4; 0; 189; -18; -22; -6; 47.6; 80].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    destruct i.
    + simpl. lra.
    + destruct i.
      * simpl. lra.
      * destruct i.
        -- simpl. lra.
        -- destruct i.
           ++ simpl. lra.
           ++ destruct i.
              ** simpl. lra.
              ** destruct i.
                 *** simpl. lra.
                 *** destruct i.
                     ---- simpl. lra.
                     ---- destruct i.
                          ++++ simpl. lra.
                          ++++ lia.
Qed.