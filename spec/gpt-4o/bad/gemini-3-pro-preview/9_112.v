Require Import List.
Require Import Arith.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length numbers = length result /\
  forall i, i < length numbers ->
            nth i result 0%Z = fold_left Z.max (firstn (i + 1) numbers) (nth 0 numbers 0%Z).

Example test_rolling_max_integers : rolling_max_spec 
  [-1%Z; -2%Z; -3%Z; -2%Z; -3%Z; -4%Z; -3%Z; -2%Z; -1%Z; -2%Z; -3%Z; -4%Z; -5%Z; -3%Z; -2%Z; -1%Z; 0%Z; -1%Z; -2%Z; -3%Z; -2%Z; -1%Z; 0%Z; 1%Z; 0%Z; -1%Z; -2%Z]
  [-1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 1%Z; 1%Z; 1%Z; 1%Z].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 27 (destruct i; [ simpl; reflexivity | ]).
    simpl in H.
    lia.
Qed.