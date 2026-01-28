Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * Z.of_nat (S i).

Example test_derivative: derivative_spec [0; 0; -1; 4; 0; 0; 5; 0; 63; 63; 0; 0; 63; 0; -7; 0; 63; 0; 1; 1] [0; -2; 12; 0; 0; 30; 0; 504; 567; 0; 0; 756; 0; -98; 0; 1008; 0; 18; 19].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    simpl in Hi.
    do 19 (destruct i as [|i]; [simpl; reflexivity | ]).
    lia.
Qed.