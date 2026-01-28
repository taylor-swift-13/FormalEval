Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.

Definition rolling_max_spec (numbers : list nat) (result : list nat) : Prop :=
  length numbers = length result /\
  forall i, i < length numbers ->
            nth i result 0 = fold_left max (firstn (i + 1) numbers) 0.

Example test_rolling_max_non_empty : rolling_max_spec [2; 3; 2; 1; 3; 3; 2; 3] [2; 3; 3; 3; 3; 3; 3; 3].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl.
    reflexivity.
  - intros i H.
    simpl in H.
    repeat (destruct i; [ simpl; reflexivity | ]).
    lia.
Qed.