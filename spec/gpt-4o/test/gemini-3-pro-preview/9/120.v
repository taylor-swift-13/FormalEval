Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.

Definition rolling_max_spec (numbers : list nat) (result : list nat) : Prop :=
  length numbers = length result /\
  forall i, i < length numbers ->
            nth i result 0 = fold_left max (firstn (i + 1) numbers) 0.

Example test_rolling_max : rolling_max_spec [100; 99; 98; 97; 96; 95; 94; 93; 92; 91; 90; 94] 
                                            [100; 100; 100; 100; 100; 100; 100; 100; 100; 100; 100; 100].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl.
    reflexivity.
  - intros i H.
    repeat (destruct i; [ simpl; reflexivity | simpl in H ]).
    lia.
Qed.