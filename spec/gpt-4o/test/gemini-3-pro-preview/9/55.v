Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.

Definition rolling_max_spec (numbers : list nat) (result : list nat) : Prop :=
  length numbers = length result /\
  forall i, i < length numbers ->
            nth i result 0 = fold_left max (firstn (i + 1) numbers) 0.

Example test_rolling_max : rolling_max_spec [10; 5; 20; 30; 25; 20; 15; 10; 15; 62] [10; 10; 20; 30; 30; 30; 30; 30; 30; 62].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl.
    reflexivity.
  - intros i H.
    do 10 (destruct i as [|i]; [ vm_compute; reflexivity | ]).
    simpl in H.
    lia.
Qed.