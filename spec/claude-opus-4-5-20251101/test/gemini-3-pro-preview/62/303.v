Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * Z.of_nat (S i).

Example test_derivative: derivative_spec [0; -8; 0; 0; 1; 0; 9; 0; 1; 0; 0; 0] [-8; 0; 0; 4; 0; 54; 0; 8; 0; 0; 0].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    simpl in Hi.
    (* We use 'do 11' to destruct i exactly enough times to cover the valid indices (0 to 10).
       Using 'repeat' can cause timeouts because the equation holds trivially for out-of-bound indices
       (0 = 0), causing an infinite loop until stack overflow or timeout. *)
    do 11 (destruct i as [|i]; [ simpl; reflexivity | ]).
    (* For i >= 11, the hypothesis i < 11 is contradictory *)
    lia.
Qed.