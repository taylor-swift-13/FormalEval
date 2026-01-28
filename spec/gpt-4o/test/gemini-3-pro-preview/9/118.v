Require Import List.
Require Import Arith.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length numbers = length result /\
  forall i, i < length numbers ->
            nth i result 0%Z = fold_left Z.max (firstn (i + 1) numbers) 0%Z.

Example test_rolling_max_custom : rolling_max_spec 
  [100%Z; 99%Z; 98%Z; 97%Z; 99%Z; 96%Z; 95%Z; 94%Z; 95%Z; 92%Z; 91%Z; 90%Z] 
  [100%Z; 100%Z; 100%Z; 100%Z; 100%Z; 100%Z; 100%Z; 100%Z; 100%Z; 100%Z; 100%Z; 100%Z].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 12 (destruct i as [|i]; [simpl; reflexivity | ]).
    simpl in H. lia.
Qed.