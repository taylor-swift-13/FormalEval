Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.

Definition rolling_max_spec (numbers : list nat) (result : list nat) : Prop :=
  length numbers = length result /\
  forall i, i < length numbers ->
            nth i result 0 = fold_left max (firstn (i + 1) numbers) 0.

Example test_rolling_max_simple : rolling_max_spec [1; 3; 2; 4; 3; 5; 4; 6; 2] [1; 3; 3; 4; 4; 5; 5; 6; 6].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 9 (destruct i; [simpl; reflexivity | ]).
    simpl in H. lia.
Qed.