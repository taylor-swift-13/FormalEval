Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition derivative_spec (xs : list nat) (ds : list nat) : Prop :=
  length ds = pred (length xs) /\
  (forall i : nat, 1 <= i < length xs -> nth (i - 1) ds 0 = nth i xs 0 * i).

Example derivative_example : derivative_spec [3; 1; 2; 4; 5] [1; 4; 12; 20].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i [H1 H2].
    simpl in H2.
    destruct i as [|i'].
    + lia.
    + destruct i' as [|i''].
      * simpl. reflexivity.
      * destruct i'' as [|i'''].
        -- simpl. reflexivity.
        -- destruct i''' as [|i''''].
           ++ simpl. reflexivity.
           ++ destruct i'''' as [|i'''''].
              ** simpl. reflexivity.
              ** simpl in H2. lia.
Qed.