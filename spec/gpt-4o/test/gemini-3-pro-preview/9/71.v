Require Import List.
Require Import Arith.
Require Import ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length numbers = length result /\
  forall i, (i < length numbers)%nat ->
            nth i result 0 = fold_left Z.max (firstn (i + 1)%nat numbers) 0.

Example test_rolling_max : rolling_max_spec 
  [2%Z; 2%Z; -3%Z; 4%Z; 5%Z; 4%Z; 3%Z; 2%Z; 1%Z; 2%Z] 
  [2%Z; 2%Z; 2%Z; 4%Z; 5%Z; 5%Z; 5%Z; 5%Z; 5%Z; 5%Z].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 10 (destruct i; [ simpl; reflexivity | ]).
    simpl in H. lia.
Qed.