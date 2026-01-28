Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * Z.of_nat (S i).

Example test_derivative: derivative_spec [1%Z; -1%Z; 0%Z; 0%Z; 0%Z; 0%Z; -24%Z; 0%Z; 0%Z; -7%Z; 0%Z; 0%Z; 1%Z] [-1%Z; 0%Z; 0%Z; 0%Z; 0%Z; -144%Z; 0%Z; 0%Z; -63%Z; 0%Z; 0%Z; 12%Z].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    simpl in Hi.
    do 12 (destruct i as [|i]; [ simpl; reflexivity | ]).
    lia.
Qed.