Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length numbers = length result /\
  forall i, (i < length numbers)%nat ->
            nth i result 0 = match firstn (i + 1)%nat numbers with
                             | [] => 0
                             | x :: xs => fold_left Z.max xs x
                             end.

Example test_rolling_max : rolling_max_spec 
  [-2%Z; 5%Z; 10%Z; -5%Z; 20%Z; 15%Z; 6%Z; 9%Z; -8%Z; -1%Z; 20%Z]
  [-2%Z; 5%Z; 10%Z; 10%Z; 20%Z; 20%Z; 20%Z; 20%Z; 20%Z; 20%Z; 20%Z].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 11 (destruct i; [ vm_compute; reflexivity | ]).
    simpl in H. lia.
Qed.