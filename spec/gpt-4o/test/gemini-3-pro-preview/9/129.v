Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.

Definition rolling_max_spec (numbers : list nat) (result : list nat) : Prop :=
  length numbers = length result /\
  forall i, i < length numbers ->
            nth i result 0 = fold_left max (firstn (i + 1) numbers) 0.

Example test_rolling_max_basic : rolling_max_spec [10; 20; 90; 40; 50; 45; 60; 55; 70; 10] [10; 20; 90; 90; 90; 90; 90; 90; 90; 90].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 10 (destruct i; [ simpl; reflexivity | ]).
    simpl in H. lia.
Qed.