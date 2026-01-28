Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Definition derivative_spec (xs : list nat) (ds : list nat) : Prop :=
  length ds = pred (length xs) /\
  (forall i : nat, 1 <= i < length xs -> nth (pred i) ds 0 = nth i xs 0 * i).

Example test_derivative : derivative_spec [0; 0; 0; 0; 0; 5] [0; 0; 0; 0; 25].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    destruct i.
    + lia.
    + destruct i.
      * simpl. reflexivity.
      * destruct i.
        -- simpl. reflexivity.
        -- destruct i.
           ++ simpl. reflexivity.
           ++ destruct i.
              ** simpl. reflexivity.
              ** destruct i.
                 --- simpl. reflexivity.
                 --- simpl in Hi. lia.
Qed.