Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * Z.of_nat (S i).

Example test_derivative: derivative_spec [10; -25; 0; 63; -40; 0; 10; 0; 64; 5; 10; 10] [-25; 0; 189; -160; 0; 60; 0; 512; 45; 100; 110].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    (* Verify element-wise calculation for indices 0 to 10 *)
    do 11 (destruct i as [|i]; [ simpl; reflexivity | ]).
    (* For i >= 11, we have a contradiction with Hi *)
    simpl in Hi. lia.
Qed.