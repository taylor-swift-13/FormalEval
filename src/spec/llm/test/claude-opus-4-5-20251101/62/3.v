Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * Z.of_nat (S i).

Example derivative_test : derivative_spec [3%Z; 2%Z; 1%Z] [2%Z; 2%Z].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    simpl in Hi.
    destruct i as [|i'].
    + simpl. reflexivity.
    + destruct i' as [|i''].
      * simpl. reflexivity.
      * simpl in Hi. lia.
Qed.