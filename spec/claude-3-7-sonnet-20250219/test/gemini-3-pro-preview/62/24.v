Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (ds : list Z) : Prop :=
  length ds = pred (length xs) /\
  (forall i : nat, (1 <= i < length xs)%nat -> nth (pred i) ds 0 = nth i xs 0 * Z.of_nat i).

Example test_derivative : derivative_spec [1; 0; -2; 5; 0; 0; 1] [0; -4; 15; 0; 0; 6].
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
                 --- destruct i.
                     +++ simpl. reflexivity.
                     +++ simpl in Hi. lia.
Qed.