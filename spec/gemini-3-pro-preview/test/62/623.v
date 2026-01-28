Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [10; -25; 0; 63; -40; -1; 10; 0; 5; -40] [-25; 0; 189; -160; -5; 60; 0; 40; -360].
Proof.
  unfold derivative_spec.
  split.
  - (* Part 1: Verify the length condition *)
    reflexivity.
  - (* Part 2: Verify the element-wise calculation *)
    intros i H.
    (* We iterate through the specific indices 0 to 8. 
       Using 'do 9' to destruct i 9 times avoids deep nesting and infinite loops. 
       vm_compute is more efficient than simpl for arithmetic verification. *)
    do 9 (destruct i; [ vm_compute; reflexivity | ]).
    (* For i >= 9, the hypothesis H (i < 9) is contradictory *)
    simpl in H. lia.
Qed.