Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * Z.of_nat (S i).

Example test_derivative: derivative_spec [9; -5; -25; 2; -40; 10; -2; 4] [-5; -50; 6; -160; 50; -12; 28].
Proof.
  unfold derivative_spec.
  split.
  - reflexivity.
  - intros i Hi.
    do 7 (destruct i; [ simpl; reflexivity | ]).
    simpl in Hi; lia.
Qed.