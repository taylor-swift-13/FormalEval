Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example derivative_spec_test :
  derivative_spec [3%Z; 1%Z; 2%Z; 4%Z; 5%Z] [1%Z; 4%Z; 12%Z; 20%Z].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    destruct i as [|i].
    + simpl. reflexivity.
    + destruct i as [|i].
      * simpl. reflexivity.
      * destruct i as [|i].
        -- simpl. reflexivity.
        -- destruct i as [|i].
           ++ simpl. reflexivity.
           ++ exfalso. simpl in Hi. lia.
Qed.