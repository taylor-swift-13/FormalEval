Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.

Definition rolling_max_spec (numbers : list nat) (result : list nat) : Prop :=
  length numbers = length result /\
  forall i, i < length numbers ->
            nth i result 0 = fold_left max (firstn (i + 1) numbers) 0.

Example test_rolling_max_complex : rolling_max_spec [1; 2; 3; 4; 5; 4; 3; 2; 1] [1; 2; 3; 4; 5; 5; 5; 5; 5].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    repeat (destruct i as [|i]; [ simpl; reflexivity | ]).
    simpl in H. lia.
Qed.