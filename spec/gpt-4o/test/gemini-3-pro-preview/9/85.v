Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.

Definition rolling_max_spec (numbers : list nat) (result : list nat) : Prop :=
  length numbers = length result /\
  forall i, i < length numbers ->
            nth i result 0 = fold_left max (firstn (i + 1) numbers) 0.

Example test_rolling_max_nonzero : rolling_max_spec [1; 3; 2; 4; 3; 30; 5; 6; 2; 2; 3] [1; 3; 3; 4; 4; 30; 30; 30; 30; 30; 30].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 11 (destruct i; [ vm_compute; reflexivity | ]).
    simpl in H. lia.
Qed.