Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.

Definition rolling_max_spec (numbers : list nat) (result : list nat) : Prop :=
  length numbers = length result /\
  forall i, i < length numbers ->
            nth i result 0 = fold_left max (firstn (i + 1) numbers) 0.

Example test_rolling_max_1 : rolling_max_spec [5; 4; 6; 4; 7; 10; 3; 8; 2; 10] [5; 5; 6; 6; 7; 10; 10; 10; 10; 10].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl.
    reflexivity.
  - intros i H.
    repeat (destruct i as [|i]; [simpl; reflexivity |]).
    simpl in H.
    lia.
Qed.