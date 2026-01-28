Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * Z.of_nat (S i).

Example test_derivative: derivative_spec [2; 4; 0; 3; 0; 3; 0; 2; 0; 1] [4; 0; 9; 0; 15; 0; 14; 0; 9].
Proof.
  unfold derivative_spec.
  split.
  - reflexivity.
  - intros i Hi.
    do 9 (destruct i as [|i]; [ vm_compute; reflexivity | ]).
    simpl in Hi; lia.
Qed.